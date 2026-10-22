# Lojita

> **本仓库冻结于 2026-10-22 晚。** 换了基础（文件库 + 触发器），后续工作在新仓库 github.com/creator915/logita1；这里的整棵树以 `archive/lojita-2026-10-22/` 的形式放在那边，只作参考。

用 Agda 写出一个编程 harness 的范畴骨架：**范畴说什么合法，智能在参数里**。

全部模块开着 `--safe --cubical`，没有一个 postulate：预言机（LLM、人、时钟……）、世界、数据库、运输、执行者都是模块参数，所以每条定理都是「对任何预言机、任何世界、任何执行者」成立的。

```
 2026-10-22 晚复位后的一句话：系统是一个关系式文件库；一切皆文件；每个文件挂着 memory 与权限；
 特定的行被写就唤起该文件的 agent 跑一轮；agent 之间只有行（协议），没有调用（继承）；与人对话的会话 agent 挂在根上。

 文件库（Store）     p/spec/* ──写──▶ 唤起 p.agent 跑一轮 ──写──▶ p/result ──▶ 唤起 p 的父（或根会话）
                     p/kids/K/spec/* ◀── p.agent 写（open K）      K/result ◀── K.agent 写（K close）
 四类操作           open / close / read / write，是操作的类型；Σ 是文件的目录
 调度器             一个查询（谁被唤起）+ 一个循环；它是操作系统，不是 agent
```

## 先读什么（2026-10-22）

仓库里新旧混放。规矩一条：**日期晚的为准，`docs/reset-2026-10-22.md` 最新。** 三档：

| 档 | 东西 | 怎么用 |
| --- | --- | --- |
| 现行规格，照着做 | `CLAUDE.md`；`docs/reset-2026-10-22.md`（复位：旧在哪、清掉什么、留什么、新基础、待拍板、下一步 D0–D4）；`docs/harness/`（10-21 的展开，各页顶上一行写着哪些段作废，README 有速查表；01、10 两页是新基础的底） | 开工前读；D0 讨论后 reset §四搬进新的 docs/harness/ |
| 现行代码与测试，已通过 | `src/`（Game / PathCat / Later、Store / Keys / Path、Env、生成的 Syntax / FlagTable、玩具 ToyEnv / StoreToy / DriveToy）、`tests/`、`check.sh` `neg.sh` `drive.sh` `store.sh` `recheck.sh` `rebuild.sh` | 先跑基线再改；`Env.agda` §3 的栈帧是旧模型的，D1 换 Σ 时去掉（reset §3.2） |
| 记录与归档，只作历史 | `archive/2026-10-22-subagent-tree/`：subagent 递归的那一套（Harness / Replay / ToyStore / Node / ToyNode、04-node、harness-plan、walkthrough、category-frame、store-and-slots），README 写了哪些零件新写时照搬。`docs/store-relations.md`：10-14 的讨论，树 vs 关系，restarting 一侧就是现在的方向。`code-plan.md`、`code-design.md`：Code v6，描述的就是现在的后端。`store-plan.md`、`store-backend.md`：Store 阶段 1，现行。`bench.md`、`archive/2026-10-13-*`、`bench/`：ProgramBench 与早期归档 | 查来龙去脉时看 |

下面的"文件"表和"现在在哪"写于 10-14；之后的进展看 `docs/reset-2026-10-22.md`。

## 文件

| 文件 | 管什么 |
| --- | --- |
| `src/Game.agda` | 签名 → 程序（自由模型）、对手（余模型）、棋谱（由签名导出）、跑一局 |
| `src/PathCat.agda` | 机器（棋规）→ 范畴（合法棋谱）；确定对手的定理 `soundDet` |
| `src/Store.agda` | 对象层数据库：实例与写、快照查询（cut）、方块 `Filled`（不同键机器填）、子 schema 的 lens（三条律）、沿 `ua` 搬运、给 Harness 的运输 `whole` / `realm` |
| `src/Later.agda` | 延迟模态 ▷：拍签名 `TSig`、带环境索引的程序 `Run`、路 `Walk`（程序与棋谱共用）、余模型、`play`（2026-10-13） |
| `src/Syntax.agda` | **生成的**：Agda 的具体语法（parser 吐出来的那棵树），74 个类型 264 个构造子，由后端的 `agda-code-gen gen` 从 Agda 源码生成；范围去掉、名字是字符串、糖和 unsafe 都在 |
| `src/FlagTable.agda` | **生成的**：哪些 flag 是 infective / coinfective（`agda-code-gen flags`） |
| `src/Path.agda` | 路径键（2026-10-22，M0）：`Path = List String`、`isPrefix`（用 `discreteString`，引理能证）、`prefix-++` / `prefix-refl`、`_≤ᵇ_` / `≤ᵇ-refl`、`half` / `half-≤`、`join`、`discretePath` |
| `src/Env.agda` | 环境 `Env`（父给的库与模式 ▸ 过了检查的模块的接口）、头 `Header E`、`Code E`（只管模块边界）、栈 `Ix`（键与 realm 是路径）、签名 `AgdaSig`（parse / check / checkAt / eval / render / enter（带 realm）/ leave / ask（Query → 文件名表）/ get / set / transport / audit / log / sh / goals / give / split）、接口的导出表、运行时造头造 Code 的判定（2026-10-13，M0 改于 2026-10-22） |
| `src/ToyEnv.agda` | 脚本余模型（剧本 `Script`：check / ask / transport / audit 四张）跑一局：check 两个模块、开一个窄的子实例、问一次、回来，全 `refl`；ToyNode 的六局也用它 |
| `src/DriveToy.agda` | 真后端跑的十二个程序（`./drive.sh`）：parse → check → eval、驳回带路径、子实例、接口、头里没写的 import、M2 import 虚拟模块 M1、`--safe` 兜底、注释节点、洞的表、填洞、分情况、λ { … } 里分情况 |
| `src/Keys.agda` | 后端要实现的那个 Store：`discreteString`（由内建 injective 引理推出）、`S = Store String String` |
| `src/StoreToy.agda` | Store 的十一个程序，纯对手上九条 `refl`；同一批程序 `./store.sh` 在真后端上跑 |
| `tests/store/`、`store.sh` | 样例日志（basic / torn / blob）、独立的 `fold.py`、`logtx.py`（日志 → Agda refl）、验收脚本 |
| `archive/2026-10-13-bench/Solve.agda` | 已归档。第一个任务（2026-10-13）：规格 = 一句话 + 一条测试；每轮 ask → 子实例里 check 模块、check 测试模块 → leave；驳回的报错原文喂回下一轮；配额 = 轮数上限。`./task1-dry.sh` 用信箱里的三份假答卷演练，`./task1.sh N` 真跑 DeepSeek Flash N 次 |
| `archive/2026-10-13-bench/Str.agda` | 已归档。字符串零件：拼接、分行、围栏、修剪、掐中间（Solve 与 Bench 共用） |
| `archive/2026-10-13-bench/Bench.agda` | 已归档。在 ProgramBench 的容器里当智能体（2026-10-13）：每步 ask → 取 ```bash 块 → `sh` 跑 → 结果记进历史；提示词 = mini-swe-agent 模板原文 + 全部历史；配额 = 步数上限 |
| `bench/` | 把解释器叠进题目镜像的 Dockerfile 与脚本（build-image / dry / run / eval / relay）；说明见 `docs/bench.md` |
| `tests/neg/` | 十个必须编译失败的反例（`./neg.sh`）：看不见的 import、多开 flag、关 `--safe`、根上 leave、配额超支、realm 外写键、realm 变宽、transport 目标在 realm 外、NodeSig 里裸 set 写 code、孩子偷看父刚 check 的模块 |
| `docs/code-plan.md` | Code 类型的方案（2026-10-13）：完整的 concrete 语法从 Agda 源码生成、环境 = 语境 × 余语境、import / flag 是模态算子、余模型 = agda 程序的入口；接法 A / B |
| `docs/bench.md` | 跑 ProgramBench：题目镜像 + 解释器那一层、一局的拓扑、`sh` 这一步、踩到的坑（2026-10-13） |
| `docs/code-design.md` | 设计稿与实施记录（2026-10-13）：生成器、Env / Code E、AgdaSig、后端接在 agda 的哪几个入口、子实例、待拍板与已定 |
| `archive/2026-10-13-code-v5/` | 归档：Code 的核心子集版（名字按层号、接反射 API）与它的玩具、文档、驱动脚本；后端 v5 在 `/root/lojita-discarded/backend-v5` |
| `archive/2026-10-22-subagent-tree/` | 归档（2026-10-22 晚）：subagent 递归的那一套——`Harness.agda`（配置树、`sub`、`Dynamics` lens）、`Replay.agda`、`ToyStore.agda`、`Node.agda`（递归 `node`，`enter` 孩子等返回值）、`ToyNode.agda`（六局）、`NegNote.agda`、`04-node.md`、`harness-plan.md`、三份 10-11 / 10-12 的讲解；README 写了为什么归档、哪些零件照搬、怎么退回 |

## 检查

需要 Agda（≥ 2.6.3）和 cubical 库（在 `~/.agda/libraries` 里登记，库名 `cubical`）。

```
./check.sh        # Path、ToyEnv、StoreToy、DriveToy（2026-10-22 复位后；Harness / Node 一系已归档）
./neg.sh          # 九个反例必须编译失败（NegNote 随 Node 归档）
./drive.sh        # 真后端（agda-cubical-run.v7）跑 DriveToy 的十二个程序
./store.sh        # Store 的硬盘余模型：F 组不要后端（fold / 日志 → Agda refl），B 组八项（回环、realm、重启、撕裂与 kill -9、dump = fold、blob、压力、日志 → Agda）
./recheck.sh      # 十个真实文件走 parse → 树 → 检查
./rebuild.sh      # Rebuilder：第二次 check 同一个模块，哈希没变就直接装接口
LOJITA_API_KEY=… ./task1.sh 10   # 第一个任务真跑十次，每次最多五轮；结果在 runs/task1/
bench/build-image.sh junegunn__fzf.b56d614     # 题目镜像 + 解释器 → …:task_cleanroom_v6_lojita
bench/dry.sh                                   # 容器里的演练（三份预置答卷）
LOJITA_API_KEY=… bench/run.sh junegunn__fzf.b56d614 && bench/eval.sh runs/bench/junegunn__fzf.b56d614/<时间>
```

`LC_ALL=C.UTF-8` 不能省：错误信息里有 Σ、≡，非 UTF-8 环境下 Agda 会把错误本身吞掉。

已验证：Game–ToyStore 六个模块 Agda 2.6.3 + cubical v0.5（commit 132a2a3）；Later 在服务器上 Agda 2.9.0 + cubical（commit 9216603）；全部零警告。

## 现在在哪

**2026-10-22 晚，复位。** 10-11 到 10-22 上午的骨架（配置树 + `sub`、Env 的栈帧、递归 `node`）是 DeepSeek Harness 式的 subagent 递归，已归档；新基础是文件库 + 触发器，见 `docs/reset-2026-10-22.md`。Store / Later / Env 的接口部分、路径键、Query / transport / audit / checkAt 都留着。下面是 10-14 写的记录，仍描述现在的后端 v7 与 Store 阶段 1。

骨架、数据库、Rebuilder、Scheduler 的槽都在；延迟模态 ▷（`src/Later.agda`）已到位。

代码的类型 v6 已经跑通（2026-10-13）：`Syntax.agda` 从 Agda 源码生成；`Env.agda` 的 `Code E` 由环境算出（归纳–递归），
`check` 过了下一拍才看得见新模块（▷）；余模型是 `agda` 进程自己（后端 v6 的 `--cubical-drive`，接在 parser / createInterface / normalise 上）。
`./drive.sh` 里 LLM 写的文本被 parse、check、eval，驳回时带着树上的路径回来；子实例只看得见父给的模块、只开父开了的 flag、只有父给的配额，违反的写不出来（`./neg.sh`）。
编辑器的三步（goals 列洞、give 填洞、split 分情况，含 λ { … } 里的洞）、注释节点、接口里的声明级依赖与哈希也在；`ask` 用 DeepSeek Flash 真跑过。
Rebuilder 用 Agda 自己的接口缓存：check 过的模块哈希没变就不重查（`./rebuild.sh`）。
第一个任务（`src/Solve.agda`）：规格「写 twice : ℕ → ℕ，twice 3 要等于 6」，模块只许 import Cubical.Data.Nat、必须 `--safe --cubical`；
LLM 写，harness 在子实例里 check 模块再 check 测试模块（`test : twice 3 ≡ 6 ; test = refl`），没过就把 Agda 的报错原文喂回去，最多五轮。
提示词里写明：只能 import Cubical.Data.Nat（`_·_`、`_∸_` 的名字）、`--safe` 下不能 postulate / TERMINATING / NON_COVERING、不要在模块里写证明。
ProgramBench（`src/Bench.agda`、`bench/`、`docs/bench.md`）：签名多一步 `sh`（后端 `--cubical-handler=sh:DIR`），解释器叠进题目镜像，harness 在题目容器里跑，LLM 经信箱中继留在宿主机；fzf 跑了一局：18 次提问、26 分钟后后端被 OOM 杀掉，评测 0 分 compile_failed；坑都记在 docs/bench.md，按约定没改。
Store 的硬盘余模型（2026-10-14，`docs/store-plan.md`、`docs/store-backend.md`）：后端 v7 `--cubical-handler=store:DIR` 在硬盘上实现 `Store String String`（`src/Keys.agda` 的 `S`）：
一局一个目录，`log.jsonl` 只追加、每行 flush + fsync，大于 2 KB 的值按 sha256 放 `blob/`，内存表是日志的 fold，`--cubical-store-dump=DIR` 打印它。
`AgdaSig` 的 readF / writeF 换成 get / set，栈帧带 realm 前缀：子实例 realm 外读到 nothing、写不出来（类型错）。
同一批程序两个对手：纯对手（`src/StoreToy.agda`，九条 refl）和真后端（`./store.sh`，25 项全过；一万次 set + get 15 秒、RSS 平直）。
Solve / Bench / Str 与信箱脚本归档到 `archive/2026-10-13-bench/`（三份记忆导致 OOM，见 `docs/store-plan.md`）。
下一步：阶段 2 棋谱插件（驱动器把每步写进 `trace/`，`ask` 的参数改成 `Query`，`Replay.wrap` 读日志续跑）。
