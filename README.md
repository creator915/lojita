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

## 检查

需要 Agda（≥ 2.6.3）和 cubical 库（在 `~/.agda/libraries` 里登记，库名 `cubical`）。

```
./check.sh        # = LC_ALL=C.UTF-8 agda src/ToyStore.agda，顺带检查其它五个模块
```

`LC_ALL=C.UTF-8` 不能省：错误信息里有 Σ、≡，非 UTF-8 环境下 Agda 会把错误本身吞掉。

已验证：Agda 2.6.3 + cubical v0.5（commit 132a2a3），零警告。

## 现在在哪

骨架、数据库、Rebuilder、Scheduler 的槽都在，玩具实例把每个槽各换过一次。下一步（详见 `docs/store-and-slots.md` 末节）：

- 接入真预言机：外部驱动器 + `verify`（Agda 不做 IO，只做检查与规范化）
- S1「状态 = 棋谱的 fold」：从棋谱算出下一步，换掉玩具里手写的 `rootProg`
- 资源账：`X` 从 `Unit` 换成资源表，`enter` 扣账、`leave` 归还
