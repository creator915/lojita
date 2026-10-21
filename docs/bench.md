# 跑 ProgramBench：题目镜像 + 解释器（2026-10-13）

一句话：ProgramBench 没有 Agda，我们的后端又是解释器，所以把后端叠进每个题目的官方镜像，
harness（`src/Bench.agda`）就在题目自己的容器里跑；题目、测试、评测脚本都没变，只是镜像多了一层。

```
 programbench/<题目>:task_cleanroom_v6 ──叠一层 /opt/lojita（解释器 + 数据目录 + cubical + Lojita 源码）──▶ …:task_cleanroom_v6_lojita
            │ 对每个题目都是同一个 Dockerfile（bench/Dockerfile，BASE 是参数）                                    │
            ▼                                                                                                     ▼
       官方评测用它                                                                           智能体跑在它里面；评测时 --image-tag task_cleanroom_v6_lojita
```

## 一局怎么跑（bench/run.sh）

```
 宿主机                                        容器（--network none，用户 agent，镜像 = 题目 + 解释器）
 relay.py ◀──看见 n.prompt──  /box（共享卷）  ◀──写 n.prompt──  agda --cubical-drive=agent
    │ 问 DeepSeek（密钥只在这里）                                     --cubical-handler=ask:mailbox:/box
    └──写 n.answer（先写 .tmp 再改名）──▶ /box ──读到 n.answer──▶      --cubical-handler=sh:/workspace
                                                                       src/Bench.agda：ask → 取 ```bash 块 → sh → 结果记进历史
 跑完：tar /workspace → runs/bench/<题目>/<时间>/sub/<题目>/submission.tar.gz → bench/eval.sh
```

- LLM 在宿主机，容器断网：和 mini-swe-agent 一样的拓扑（它的模型也在容器外）。/box 里的 `n.prompt` / `n.answer` 就是完整轨迹。
- 提示词 = mini-swe-agent `programbench.yaml` 的 system / instance 模板原文，只把"工具调用"换成"恰好一个 ```bash 块"；每轮带全部历史（DeepSeek Flash 上下文 1M，前缀缓存命中 0.02–0.04 元/百万）。
- 结果超过 10000 字符留头尾各 5000（原模板的 observation 规则，在 `Str.elide` 里）；少于 20 步时附原模板的提醒。
- 配额 = 步数上限（300）：`ask` 要配额 ≥ 1，所以"最多 300 步"是类型说的。每条命令 180 秒超时（退出码 124），整局 3 小时墙钟（宿主机 `timeout`）。

## 后端加的一步：sh

签名 `AgdaSig` 多一步 `sh : String → Op ix`，`Res (sh _) = ℕ × String`（退出码 × 输出，stderr 并进 stdout），环境不变。
方案里叫 run（Σ = {ask, run}），仓库里 `run` 已被占用，所以叫 sh。
后端 `--cubical-handler=sh:DIR`：命令在 DIR 里用 `bash -c` 跑，stdin 是 /dev/null，`LOJITA_SH_TIMEOUT` 秒后杀（默认 180），
输出按 UTF-8 宽松解码、最多 `LOJITA_SH_MAXOUT` 字符（默认 100000）；没配 sh 处理函数就拒答。
Drive.hs +40 行，增量重编 1 分钟；旧二进制留作 `agda-cubical-run.v6-pre-sh`。

## 脚本

| 文件 | 管什么 |
| --- | --- |
| `bench/Dockerfile` | 函子那一层：COPY 四样东西到 /opt/lojita，构建时以 agent 用户检查一遍 Bench.agda（接口缓存就位） |
| `bench/build-image.sh 题目` | 拉官方镜像、打包上下文、build、打标 `…_lojita` |
| `bench/dry.sh` | 不用 LLM 的演练：三份预置答卷（一条命令、一次没围栏、提交），回路走通 |
| `bench/run.sh 题目` | 真跑：起容器、relay、驱动器、打提交包。`LOJITA_API_KEY=… WALL=10800 bench/run.sh junegunn__fzf.b56d614` |
| `bench/eval.sh 运行目录` | `programbench eval … --image-tag task_cleanroom_v6_lojita` + `programbench info` |
| `bench/relay.py` | 信箱中继（宿主机） |

## 踩到的坑（只记录，不改）

1. **Agda 2.9 按当前目录找 `.agda-lib`，不按文件所在目录。** 在 /workspace 里启动 `agda /opt/lojita/lojita/src/Bench.agda` 报
   `ModuleNameDoesntMatchFileName`（include 路径成了 /workspace 和 prim）。宿主机上 `cd /tmp && agda /root/lojita/src/Bench.agda` 一样。
   解决：驱动器在项目根目录启动（`docker exec -w /opt/lojita/lojita`），sh 的目录由 `sh:/workspace` 单独定。
2. **提交包里没有题目给的 `executable`**：它对 agent 用户只有 x 没有 r，tar 读不了（mini-swe-agent 一样，它的 tar 也是这么失败再 docker cp 的）。
   `tar --ignore-failed-read`，评测不需要它。
3. 驱动器日志（stderr）把提示词和输出都截到 200 字；完整的东西在 /box 里。
4. **一条回复里几十个 ```bash 块**（fzf 第一局就出现）：mini-swe-agent 靠工具调用让模型"发一条命令就停"，我们的 `ask` 是一条纯文本消息，
   模型会在一条回复里连写一串命令（第 2 步 149 个块、38 KB；第 5 步 25 个块、51 KB），中间夹着"接着我再试……"，没有编造结果。
   harness 只跑第一个块，整条回复原样进历史，所以提示词第 6 步就到 124 KB。这不是 Lojita 的类型能挡的——回复是 String，签名里没说"一条回复一个命令"。
   可选的补法（没做）：relay 发请求时给 `stop`（在第一个块的 ``` 之后停）、或 `ask` 的回应类型改成"恰好一条命令"、或历史里只留每条回复的第一个块。
5. **后端进程被 OOM 杀掉。** 第 18 次提问之后（驱动器第 34 步，提示词 575 KB），容器 16 GB 内存上限处内核杀了 `agda`
   （`anon-rss 16.7 GB`，exit 137），只跑了 26 分钟，远没到 300 步 / 3 小时。
   历史是 `List (String × String)`，每轮用 `primStringAppend` 从头拼整条提示词，再加 `elide` 把 10 万字符的输出 `primStringToList` 成表——
   这些都在 Agda 的归约器里做，项不回收，内存随历史平方级涨。是 Bench.agda 的写法问题，不是签名的问题。
   可选的补法（没做）：历史不进 Agda 的项（放在后端或文件里，`ask` 只带增量）、或后端给字符串切片的原语、或把 `elide` 搬进 sh 处理函数。

## fzf 第一局的记录（2026-10-13，runs/bench/junegunn__fzf.b56d614/20261013T101155Z）

| 项 | 数 |
| --- | --- |
| 提问（步） | 18（驱动器步 34，含 sh） |
| 墙钟 | 26 分钟（其中 LLM 22 分钟） |
| 提示词 | 7.8 KB → 576 KB |
| tokens | 输入 130 万（缓存命中 113 万，未命中 17 万）、输出 26 万 |
| 费用（按价目表） | 约 1.2–2.5 元 |
| 结束方式 | 后端 OOM（坑 5） |
| 评测 | `programbench eval … --image-tag task_cleanroom_v6_lojita`：0 分，`compile_failed`（没有 compile.sh） |

模型做到了哪：前 10 步读文档、试 `--filter`、看 `--help`；第 12、13 步各写了 190 KB、二十几个块的回复（整套实现分成多个 heredoc），
但只有第一个块被执行；第 18 步它说「环境好像每轮都在重置」，把 `main.py` 整个放进第一个块——这一步没来得及跑，进程就被杀了。
工作区里只有它存下来的 help.txt / man.txt / bash.txt 等；没有源码、没有 compile.sh。

评测流水线本身走通了：提交包 → 官方评测脚本在叠了解释器的镜像里 wipe / seed_git / compile / 测试；分数口径和官方一致。
