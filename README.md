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
| `src/Code.agda` | 代码的类型：环境 `Env` / 声明 `Decl Γ` / 项 `Term Γ n` 一个归纳–递归块；程序 `Code Γ Γ′`、范畴 `EnvCat`；接口宇宙 `U/El`；洞 |
| `src/Load.agda` | 反射工具：步 `load d` / `call t a`、判决 `Verdict`、`CodeSig`；解释器子句 `loadThen`；`accepted`；脚本后端；给 Harness 的桥 `AsOracle` |
| `src/ToyCode.agda` | 玩具：四条声明装进环境再调用新工具，全 `refl`；驳回一条的情形；装之前调不了 |
| `src/DriveTests.agda` | 喂给后端驱动器的反例（类型错、不停机、负性、引用未定义名）和一个正例 |
| `docs/code-type.md` | Code 类型与反射工具：范畴、归纳–递归在哪、▷ 在哪、后端做什么、对勘误六问的回答、决定、留白（2026-10-13） |

## 检查

需要 Agda（≥ 2.6.3）和 cubical 库（在 `~/.agda/libraries` 里登记，库名 `cubical`）。

```
./check.sh        # = agda src/ToyStore.agda && agda src/ToyCode.agda，顺带检查其余模块
./drive.sh        # 后端 v5 的驱动器：ToyCode 的四条声明经 Agda 真的检查、进签名，再 call twice 5（需 agda-cubical-run.v5）
./drive-tests.sh  # 驱动器的反例：类型错 / 不停机 / 负性 / 引用未定义名 都该 fail
```

`LC_ALL=C.UTF-8` 不能省：错误信息里有 Σ、≡，非 UTF-8 环境下 Agda 会把错误本身吞掉。

已验证：Game–ToyStore 六个模块 Agda 2.6.3 + cubical v0.5（commit 132a2a3）；Later / Code / Load / ToyCode / DriveTests 在服务器上 Agda 2.9.0 + cubical（commit 9216603）；全部零警告。

## 现在在哪

骨架、数据库、Rebuilder、Scheduler 的槽都在；代码的类型与反射工具（2026-10-13）接上了：

```
 编排层   环境 Γ ──load d（后端判 ok）──▶ Γ ▸ d ──call t a──▶ Γ ▸ d      对象 = 环境，箭头 = 程序（Code Γ Γ′）
                 这一拍 d 是数据              下一拍新名字才在环境里（▷）
 后端 = CodeSig 的余模型（agda-cubical-run.v5 --cubical-drive）：装一条声明 = 调 Agda 自己的检查器扩展签名
```

详见 `docs/code-type.md`。下一步（留白）：后端接记录（`recdef`）与一拍装一组（互递归）；文本 → Code（LLM 写 Agda 文本，后端用 Agda 的 parser 翻成 Code 值）；`Discrete (Decl Γ)`（回放按语法对位）；弱化 `wk`（编辑器插入声明）。
