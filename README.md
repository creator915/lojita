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
| `docs/code-plan.md` | Code 类型的方案（2026-10-13）：完整的 concrete 语法从 Agda 源码生成、环境 = 语境 × 余语境、import / flag 是模态算子、余模型 = agda 程序的入口；接法 A / B |
| `archive/2026-10-13-code-v5/` | 归档：Code 的核心子集版（名字按层号、接反射 API）与它的玩具、文档、驱动脚本；后端 v5 在 `/root/lojita-discarded/backend-v5` |

## 检查

需要 Agda（≥ 2.6.3）和 cubical 库（在 `~/.agda/libraries` 里登记，库名 `cubical`）。

```
./check.sh        # = agda src/ToyStore.agda && agda src/Later.agda，顺带检查其余模块
```

`LC_ALL=C.UTF-8` 不能省：错误信息里有 Σ、≡，非 UTF-8 环境下 Agda 会把错误本身吞掉。

已验证：Game–ToyStore 六个模块 Agda 2.6.3 + cubical v0.5（commit 132a2a3）；Later 在服务器上 Agda 2.9.0 + cubical（commit 9216603）；全部零警告。

## 现在在哪

骨架、数据库、Rebuilder、Scheduler 的槽都在；延迟模态 ▷（`src/Later.agda`：拍签名、带环境索引的程序、路、余模型）已到位。

代码的类型 Code 做过一版（`archive/2026-10-13-code-v5/`），因为只覆盖 Agda 的核心子集、接在反射 API 上，已归档。
定下来的方案在 `docs/code-plan.md`：Code = Agda 完整的 concrete 语法（从 Agda 源码生成，糖和 unsafe 都在）；
环境 = 已检查模块的接口 × flag（语境 × 余语境），`Code Γ` 由 Γ 递归算出（归纳–递归），`check` 的回应带回新接口、下一拍进环境（▷）；
余模型 = agda 程序自己的入口（parser / createInterface / normalise / 交互命令），不是反射 API。
