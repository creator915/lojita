# 整个范畴的骨架：四个 Agda 文件（2026-10-11）

接续 nine-ideas、decisions、dev-order-draft v2 与上一轮"三层塔 + 每层一个数据库值 + 沿配置的纤维化"的框架。本会话把骨架写成 Agda 并通过检查；逐段讲解在 Claude Doc《用 Agda 造出 Harness 的范畴：三个文件逐段讲解》 https://claude.ai/code/artifact/cc6fb48b-e73e-445e-8e39-47a88fdd4970 。文件在 `harness-agda/`：Game.agda（60 行）、PathCat.agda（103 行）、Harness.agda（209 行）、Toy.agda（184 行，玩具实例）。

## 一句话
底 = 配置树 `Config`（规则书 + 孩子）；每个 x 上一个纤维 `Fiber x`（对象 = 棋盘，箭头 = 在 x 下合法的棋谱）；纤维里程序 `Free (Sig-of x)` 对上对手 `opp x` = 预言机 × 世界 × 子 harness；定理 `sound`：对任何策略、任何预言机，跑出的棋谱都是 `Fiber x` 里的一条箭头。范畴说合法，智能在参数里。

## 结构（都已通过 --safe --cubical，原版 Agda 2.6.3 + cubical v0.5，零警告）
- Game：`Sig`（Op, Res）→ `Free`（程序 = 有限策略树）；`Step/Trace` 由签名导出；`Comodel S W`（对手，状态 W 在类型里）；`Play.play`（模型 ⊗ 余模型 = 结果 × 新状态 × 棋谱）。
- PathCat：`Category`（自写，无 isSetHom）；`Machine Pos Move`（ok 是命题 okProp；落点唯一 okDet = "状态是日志的 fold"）；`Build`：Hom p q = 棋谱 + 合法证明，恒等 = 空棋谱，合成 = 接棋谱，三条律一行一条；`Det`：确定对手 ⇒ 机器，定理 `soundDet`。
- Harness（模块参数：预言机族 Oracle/Q/A/OState/oracle、世界 WSig/Board/world、Spec/Report）：§0 `Store`、事务范畴 `Trans`；§1 `Rules`（工具 = `Free WSig` 里的程序）、`Config` 树；§2 三类步 `Act` = ask/run/sub，`Sig-of`（sub 的回应夹子棋谱，父棋谱树形）；§3 `Mach x`（ask 任意合法、run 由 exec 定、sub 递归用孩子的 Legal）、`Fiber x`、`transOf`（上层的一步是下层的一条路）；§2 末 `Strat x`（策略树：每个配置一段 prog、每个孩子一棵子树，形状跟配置树走）；§4 `Dynamics.opp x st`（sub 由子 harness 整条跑完作答）；§5 `sound`；§6 `Position`（余切片的对象）、`finish`、`Product = Σ Board Accept`；§7 `Reflect.turn`（回答是数据，经 check 才成为一步；子实例由此产出）。

## 本会话的决定
1. 没有全局公理：所有未知量是 `Harness` 的模块参数；定理自动对任何预言机/世界成立。
2. `Comodel`、`Machine` 的状态/局面/记录放在类型参数而不是字段里（否则递归里 `W (opp (kid k))` 卡住）："状态是什么"属于类型，"怎么答"才是数据。
3. 子配置在开子线时定死、整条子线不换；没有沿底搬纤维；子线顺序执行、子棋盘直接接回父棋盘，不合并。
4. 预言机 = 只受类型约束的对手：静态合法性对 ask 一律放行，动态由 `oracle` 参数给。
5. 对象层本次只到"棋盘之间"（Trans）；棋盘里面（键 ↦ 值、代码态射）留到数据库那次。
6. 策略不是"对所有配置"的一个函数，是和配置树同形的策略树 `Strat x`（玩具逼出来的：策略必须知道自己的工具表）。子 harness 的策略是父策略的一部分。
7. 用户定：用 B（策略树）。理由：配置本来就要自带程序。工具是类型不是要解码的数据，点错工具是编译错误；通用循环 A 是 B 的特例（mkStrat），推迟到 S4。
8. 代码与讲解放进 GitHub 仓库 Lojita：src/ 四个模块、docs/walkthrough.md（讲解稿快照）、docs/category-frame.md（本页）、check.sh。

## 玩具实例 Toy.agda（全部 refl 通过）
棋盘 = 计数器 ℕ；世界 = {get, add k}；工具 inc/peek 是 Free WSig 里的两步程序；预言机 llm 按脚本答 add!/delegate!/stop!；配置树 root（一个孩子）→ leaf；根策略 = 读一次后预算内"问 → check → 走"，叶策略不问模型。脚本 [add! 2, delegate! 3, stop!] 从 0 跑到 5：棋谱 6 条记录，sub 那条夹着叶的子棋谱 [(run inc 3 , 5)]（子实例对父是一个点，点里装着一段）。`accepted : Product (_≡ 5)` 和 `trace-is : 棋谱 ≡ expected` 都是 `refl`。两局接成 `Fiber root` 里 0 → 10 的箭头（12 条记录）；`transOf rules inc 2 0` 是 Trans 里 0 → 2 的两步箭头。

## 留白（代码里已占位，补时不改核心）
Board/WSig/world → 数据库（Store、事务、交换性）；Strat 的每段 prog（valueOf、loop 手写）→ S1 状态 = 棋谱的 fold、S4 提示词 = 投影；sub 顺序 → 交错与合并（decisions 2）；Category → 补 isSetHom 接 cubical 库；Config 树 → 写成数据后造编排层范畴（S7）；≃ 只在桥上（S2 两对手何时说同样的话）。

## 编译
服务器上 `LC_ALL=C.UTF-8 agda Harness.agda`（新后端不带 --cubical-* 即原版）。Toy.agda 里 `fst (snd demo)`、`fst demo`、`fst both` 是封闭项，可直接 `--cubical-run`。
