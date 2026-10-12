# Lojita

用 Agda 写出一个编程 harness 的范畴骨架：**范畴说什么合法，智能在参数里**。

全部模块开着 `--safe --cubical`，没有一个 postulate：预言机（LLM、人、时钟……）、世界、数据库、运输、执行者都是模块参数，所以每条定理都是「对任何预言机、任何世界、任何执行者」成立的。

```
 编排层   配置树 Config（底）      x ──▽ kid k（边上带运输 Lifting）──▶ x_子 ──▽──▶ …
                                   │ Fiber x                              │ Fiber x_子
                                   ▼                                      ▼
 代理层   纤维 Fiber x       棋盘 b ──棋谱 ask/run/sub──▶ 棋盘 b′      对象 = 棋盘，箭头 = 合法棋谱
                                   │ 一步 run
                                   ▼
 对象层   数据库 Store       实例 s ──事务（一列 get/set）──▶ 实例 s′     工具 = 这一层的程序

 唯一的义务 Honest：对手每答一步都是 Fiber x 的一步
 定理 soundHonest：诚实的对手 + 任何策略 ⇒ 跑出来的棋谱是 Fiber x 里的一条箭头
 槽（à la Carte）：Lifting（每条边的运输）× (X, enter, leave)（上下文 lens）× Exec（执行者）× 对手（真 / 录音）
```

## 文件

| 文件 | 管什么 |
| --- | --- |
| `src/Game.agda` | 签名 → 程序（自由模型）、对手（余模型）、棋谱（由签名导出）、跑一局 |
| `src/PathCat.agda` | 机器（棋规）→ 范畴（合法棋谱）；确定对手的定理 `soundDet` |
| `src/Harness.agda` | 配置树（边上带运输）、三类步 ask/run/sub、纤维、`Honest` 与 `soundHonest`、执行者 `Exec`、对手族 `Dynamics`（上下文 lens + 执行者为参数）、局面与产品、反射点 |
| `src/Store.agda` | 对象层数据库：实例与写、快照查询（cut）、方块 `Filled`（不同键机器填）、子 schema 的 lens（三条律）、沿 `ua` 搬运、给 Harness 的运输 `whole` / `realm` |
| `src/Replay.agda` | Rebuilder：`verify`（可判定的合法性 = verifying trace）、录音对手 `wrap`（constructive trace）、`wrap-honest` |
| `src/ToyStore.agda` | 玩具实例：键值数据库上跑一局；换运输、换对手（录音回放、录音失效）；全部 `refl` |
| `docs/walkthrough.md` | 骨架四文件逐段讲解（2026-10-11） |
| `docs/category-frame.md` | 骨架一页结论（2026-10-11） |
| `docs/store-and-slots.md` | 数据库、Scheduler、Rebuilder：结构、槽、决定、留白（2026-10-12） |
| `src/Later.agda` | 延迟模态 ▷：拍签名 `TSig`、带环境索引的程序 `Run`、路 `Walk`（程序与棋谱共用）、余模型、`play`（2026-10-13） |
| `src/Syntax.agda` | **生成的**：Agda 的具体语法（parser 吐出来的那棵树），74 个类型 264 个构造子，由后端的 `agda-code-gen gen` 从 Agda 源码生成；范围去掉、名字是字符串、糖和 unsafe 都在 |
| `src/FlagTable.agda` | **生成的**：哪些 flag 是 infective / coinfective（`agda-code-gen flags`） |
| `src/Env.agda` | 环境 `Env`（父给的库与模式 ▸ 过了检查的模块）、头 `Header E`、`Code E`（归纳–递归，只管模块边界）、栈 `Ix`、签名 `AgdaSig`（parse / check / eval / render / enter / leave / ask / readF / writeF / log）、运行时造头造 Code 的判定（2026-10-13） |
| `src/ToyEnv.agda` | 脚本余模型跑一局：check 两个模块、开一个窄的子实例、问一次、回来，全 `refl` |
| `src/DriveToy.agda` | 真后端跑的七个程序（`./drive.sh`）：parse → check → eval、驳回带路径、子实例、接口、头里没写的 import、M2 import 虚拟模块 M1、`--safe` 兜底 |
| `tests/neg/` | 五个必须编译失败的反例（`./neg.sh`）：看不见的 import、多开 flag、关 `--safe`、根上 leave、配额超支 |
| `docs/code-plan.md` | Code 类型的方案（2026-10-13）：完整的 concrete 语法从 Agda 源码生成、环境 = 语境 × 余语境、import / flag 是模态算子、余模型 = agda 程序的入口；接法 A / B |
| `docs/code-design.md` | 设计稿与实施记录（2026-10-13）：生成器、Env / Code E、AgdaSig、后端接在 agda 的哪几个入口、子实例、待拍板与已定 |
| `archive/2026-10-13-code-v5/` | 归档：Code 的核心子集版（名字按层号、接反射 API）与它的玩具、文档、驱动脚本；后端 v5 在 `/root/lojita-discarded/backend-v5` |

## 检查

需要 Agda（≥ 2.6.3）和 cubical 库（在 `~/.agda/libraries` 里登记，库名 `cubical`）。

```
./check.sh        # = agda src/ToyStore.agda && agda src/ToyEnv.agda，顺带检查其余模块
./neg.sh          # 五个反例必须编译失败
./drive.sh        # 真后端（agda-cubical-run.v6）跑 DriveToy 的七个程序
```

`LC_ALL=C.UTF-8` 不能省：错误信息里有 Σ、≡，非 UTF-8 环境下 Agda 会把错误本身吞掉。

已验证：Game–ToyStore 六个模块 Agda 2.6.3 + cubical v0.5（commit 132a2a3）；Later 在服务器上 Agda 2.9.0 + cubical（commit 9216603）；全部零警告。

## 现在在哪

骨架、数据库、Rebuilder、Scheduler 的槽都在；延迟模态 ▷（`src/Later.agda`）已到位。

代码的类型 v6 已经跑通（2026-10-13）：`Syntax.agda` 从 Agda 源码生成；`Env.agda` 的 `Code E` 由环境算出（归纳–递归），
`check` 过了下一拍才看得见新模块（▷）；余模型是 `agda` 进程自己（后端 v6 的 `--cubical-drive`，接在 parser / createInterface / normalise 上）。
`./drive.sh` 里 LLM 写的文本被 parse、check、eval，驳回时带着树上的路径回来；子实例只看得见父给的模块、只开父开了的 flag、只有父给的配额，违反的写不出来（`./neg.sh`）。
接口、编辑器步（goals / give / case）、注释、声明级依赖是下一阶段。
