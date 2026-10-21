# 围绕 Store 重搭数据库：盘点与计划（2026-10-13）

一句话：现在有三份"记忆"（Agda 项里的历史、后端内存里的 TCState、硬盘上只写不读的信箱与日志），
要收成**一个 Store**：后端在硬盘上持有唯一的实例，棋谱、接口表、世界快照是它上面的三个子 schema（插件），
提示词是对它的一个查询；程序（Later 的 Run）只做策略，不拿数据。

```
                     Store（范畴：对象 = 实例，箭头 = 事务 / lens / ua 搬运）
                                      │ 后端在硬盘上实现它（唯一会写的人）
        ┌───────────────┬─────────────┼───────────────┬──────────────────┐
   realm "trace/"   realm "iface/"   realm "world/"   查询（负侧，不占行）     ← 插件 = 子 schema + 运输
   棋谱：每步 (o,r)   接口表：名字/类型  /workspace 快照   提示词 = cut s q
   Replay.wrap 读它   /依赖/哈希       sh 的效应落这里   后端增量算（S4 投影）
        └───────────────┴─────────────┴───────────────┘
   程序 Run：每步只说"下一步走什么"（S1：next = 棋谱的 fold），不抱历史
```

## 一、盘点：哪些是架构（不删），哪些是临时的（可删 / 重写）

### 架构——不删

| 东西 | 为什么是架构 |
| --- | --- |
| `src/Game.agda`、`PathCat.agda`、`Harness.agda` | 骨架：签名 → 程序 / 对手 / 棋谱；`Honest`、`soundHonest`、槽（Lifting、enter/leave、Exec） |
| `src/Store.agda` | 数据库范畴本身：实例、事务、`Filled`、`Realm` lens（三条律）、`Rename`/ua、给 Harness 的 `Lifting` |
| `src/Replay.agda` | Rebuilder：`verify`（verifying trace）、`wrap`（录音对手）——就是"读硬盘上的棋谱再跑" |
| `src/Later.agda` | ▷、`TSig`、`Run`、`Trace`、`Comodel`、`play`：程序层；"单独一个进程"指的就是它 |
| `src/Env.agda` | 环境 E、`Code E`、`Ix`、`AgdaSig`（parse / check / eval / enter / leave / ask / 编辑器三步）。`sh` 这一步保留，但它的回应要改成走 Store（见阶段 4）；`readF` / `writeF` 可删（被 Store 取代） |
| `src/Syntax.agda`、`FlagTable.agda` | 生成物（`agda-code-gen`），Code v6 的根 |
| `src/ToyStore.agda`、`ToyEnv.agda`、`DriveToy.agda`、`tests/neg/` | 架构的测试：全 refl / 五个必须失败的反例 / 十二个真后端程序 |
| 后端 `Code.hs`、`Drive.hs` 主体、`Runtime.hs`、`agda-code-gen` | 余模型 = agda 自己的入口；`toV`/`fromV`/`vToTerm`；接口缓存（Code 侧的 Rebuilder，已落盘）；v2 的 `--cubical-export` / `--cubical-import`（Agda 值的序列化通道，Store 的行就用它的 V 编码） |
| 后端的"处理函数在运行前配好"这个机制 | 世界的唯一接触点，是槽；`ask:http`、`ask:fixed`、`ask:script` 保留（真预言机 / 测试） |
| `check.sh`、`neg.sh`、`drive.sh`、`recheck.sh`、`rebuild.sh` | 架构级测试 |
| `bench/Dockerfile`、`bench/build-image.sh`、`bench/eval.sh` | 函子那一层（题目镜像 ↦ 题目镜像 + 解释器）和官方评测，是对的 |
| 文档 `walkthrough` / `category-frame` / `store-and-slots` / `code-plan` / `code-design` | 设计记录 |

### 临时——可删或重写

| 东西 | 怎么处理 |
| --- | --- |
| `src/Bench.agda` | **删**。私有 `History` 列表 + 每轮在 Agda 项里重拼提示词 + `elide` 字符表，就是 OOM 的三个来源。策略部分（取 ```bash 块、识别提交命令、投影带哪几步）在阶段 5 作为纯策略重写 |
| `src/Solve.agda` | **重写**。回路形状（ask → 子实例里 check 模块、check 测试 → leave，报错喂回）是对的，但 `List Round` 历史和在 Agda 里拼提示词同样不对；改成对 Store 的策略 |
| `src/Str.agda` | **大半删**。`elide` / 字符表不该在 Agda 里；取围栏块这种小解析要么进后端的处理函数，要么留一个十行的助手 |
| `task1.sh`、`task1-dry.sh` | 删（阶段 5 重做） |
| `bench/run.sh`、`bench/relay.py`、`bench/dry.sh`、`bench/replay.sh` | 删。信箱拓扑由"后端写 Store，中继读 Store"取代；`replay.sh` 的功能归 `Replay.wrap` |
| 后端 `ask:mailbox`、`readF:` / `writeF:` | 删（信箱是临时通道；读写文件由 Store 的 get / set 取代） |
| `_lojita_virtual/`、`_build/`、`runs/` | 不是系统的一部分：前两个是 Agda 要的文件与缓存，`runs/` 是记录（留着对照，已 gitignore） |
| `docs/bench.md` | 留作记录（第一局怎么死的、为什么），不是设计 |

删完之后仓库回到：骨架六件 + Later + Code v6 四件 + 测试 + 函子层。乱的部分全在"临时"那一栏。

## 二、关键设计选择（三条，定了就不回头）

1. **一个 Store，字符串键，插件 = 前缀 realm。** 后端只实现一个实例 `K = String`（路径样式的键，如 `trace/34/reply`），`V = String`（短文本，或大字段的哈希）。
   棋谱 / 接口表 / 世界各占一个前缀，用 `Store.Realm`（前缀可判定）做子 schema：隔离由 `confineL` 保证，子实例的视野就是 `Lifting = realm R`——范畴已经写好的东西直接用，不另造。
2. **查询是数据，不是函数。** `cut s q` 里的 q 在 Agda 是函数，后端没法对硬盘上的行跑任意 Agda 函数（跑了就又把整张表装进归约器）。
   所以提示词这类投影写成一小套查询语法（`Query` 作 data：某前缀、第 i 到 j 步、取哪些字段、最近 N 条、拼接），后端解释、增量缓存；Agda 这边 `Query` 的律照旧。这正是 store-and-slots 留白里的"有内容的查询语法"。
3. **程序不持数据，每步重进。** S1：`next : Trace → Maybe Op`，驱动器每步问 Agda"录音到此，下一步"（接口有缓存，半秒），所以进程死了只丢当前这一步；长驻进程也可以，但只许持行号，不许持字节。

## 三、分期

| 阶段 | 做什么 | 删什么 | 验收 |
| --- | --- | --- | --- |
| 0 清理（半天） | README 回到架构图；临时栏全部移走（`archive/2026-10-13-bench/` 或直接删） | 临时栏 | `check.sh` / `neg.sh` / `drive.sh` 全过 |
| 1 Store 的后端 | 后端做 `WSig = {get, set}` 的硬盘余模型：一局一个目录，`log.jsonl` 只追加（步号、op、值或哈希）、`blob/<hash>`、快照 = log 的 fold；`AgdaSig` 加 `get k` / `set k v`（回应 `Maybe String` / `Unit`，环境不变）；`enter` 的子实例用 `realm` 限前缀 | `readF` / `writeF` | Agda：ToyStore 式 refl；后端：set → get 回环、杀进程后重放 log 得同一快照、`Replay.verify` 对 log 通过 |
| 2 棋谱插件 | 驱动器把每步 (o , r) 作为事务写进 `trace/`（回复、输出按哈希）；`ask` 的参数由 String 改为 `Query`，后端解释、前缀缓存；S1 的 `next`；`Replay.wrap` 读 log 回放 / 续跑 | `ask:mailbox`、`bench/run.sh` 等 | 回放 fzf 的 18 步：内存平直；中途杀进程，从该步续；`模型可见 ⟺ 已记录` 成为定义 |
| 3 接口表插件 | `check` 的 `Iface` 行写进 `iface/`（名字 / 类型 / 依赖 / 哈希）；Rebuilder 读行的哈希决定重查（`.agdai` 仍是 Agda 自己的缓存）；"改了代码重查依赖它的测试"从这里长出来（v6 原定的下一步） | — | `rebuild.sh` 改为看 Store 行；依赖重查的玩具 |
| 4 世界插件 | /workspace 快照工具：路径 → 内容哈希，写进 `world/`；`sh` 变成工具：事务 = (命令, rc, 输出哈希) + 快照差；子实例看见的世界 = `realm` | `sh` 回大文本 | 一条 sh 之后 `world/` 的差就是它改的文件；`Filled` 的默认元素（不同键）照常 |
| 5 策略重写 | Solve、Bench 作为纯策略：不持历史，只决定下一步和投影（窗口 / 摘要是 `Query` 的选择）；一条回复多个块的问题在这里用回应类型或 `stop` 处理 | — | 任务一 10 次；fzf 第二局跑满预算不 OOM，能从崩溃点续 |

顺序不可换：没有 1 就没有地方写；没有 2 程序就还得自己抱历史；3、4 可并行；5 最后。

## 四、要你拍板的

1. 键空间：一个字符串键 Store + 前缀 realm（推荐），还是每个插件各一个 Store？
2. 程序进程：每步重进（推荐，S1），还是长驻只持行号？
3. `Query` 的语法先要多小：前缀 + 步号区间 + 字段 + 最近 N + 拼接，够不够第一版？
4. 临时的东西是直接删还是进 `archive/`？
