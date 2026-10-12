# 数据库、Scheduler、Rebuilder：结构、槽、决定、留白（2026-10-12）

接续 category-frame.md（骨架）、nine-ideas、decisions、dev-order-draft v2、catdb-displayed-optics（数据库的范畴设计）。本次新增 `Store.agda`、`Replay.agda`、`ToyStore.agda`，重写 `Harness.agda`；全部 `--safe --cubical`，零 postulate。

## 一句话
数据库 = 底（schema）上铺开的一族范畴；Scheduler 和 Rebuilder 不是数据库的一部分，是开数据库的两种策略，各占一个槽。结构只认一条义务 `Honest`（对手每答一步都是 `Mach x` 的一步）；`soundHonest` 证一次，换任何槽都不动。

## Store.agda：对象层
- 正侧：实例 `Board = K → Maybe V`，写 `upd`；三条算术 `upd-here / upd-there / upd-comm`，`upd-same`（后写赢，同键方块天生空心）。
- 负侧：快照查询 `Query`，`cut s q = q s`；读不造版本。
- 签名 `WSig = {get, set}`，`world` 余模型；`get-pure`、`read-indep`。填 Harness 参数 ②。
- 方块：`Filled t₁ t₂` 是「填满了」这个类型；`fill-indep` 是机器填的默认元素（两两不写同键；小方块 `step-comm` 拼成大方块 `tx-comm`）。同键证书留给提供者 / LLM。
- 底箭头一：子 schema `Realm R`，lens `restrict / merge` 与三条律 GetPut / PutGet / PutPut、`confine`；握手律在「查询接在 view 后面」的免费版本里是 `refl`。
- 底箭头二：`Rename e`，`path i = ua e i → Maybe V`，`carry = transport path`，`carry-is` 算出来就是重索引；闭项在原版 Agda 里直接算到 `just 5`。
- §7 给 Harness 的同类型运输：`Lifting = whole | realm R`，`restrictL / mergeL`，三条律与 `confineL`。

## Harness.agda：槽
- 参数组 ④ `(Lifting, restrict, merge)`；`node` 第四个字段 `lf : Kids → Lifting`：运输是结构的数据，定在边上。
- `okOf` 的 sub 分支：存在 c，子棋谱从 `restrict b` 合法到 c，且 `merge b c ≡ b′`。仍是命题、终点仍唯一。
- `Honest x C board`、`soundHonest`：诚实 ⇒ 整局合法。
- `Exec`：`execute` + `execute-sound`；`playExec` 是唯一居民（suspending）。
- `Dynamics (X, enter, leave) (E)`：`W = OState × Board × X`；sub = 三个 lens 下去再回来（棋盘 restrict/merge；预言机状态原样共享；X 是资源账的位子）。`honest` 与 `opp` 互递归；`sound` 降为推论。
- 两类依赖的落点：权限类走 `restrict`（复制，不消耗）；资源类走 `enter / leave`（消费、归还，= 对父的 Σ 做一次更新）。并发子线的配额约束是 `enter` 的前置条件，不碰 `Mach x`。

## Replay.agda：Rebuilder
- `DecCfg x`（形状跟配置树走）：`decOp`、`decRes`、`kids`；`DecAct` 从规则书零件拼出 `Discrete (Act r Kids)`（Act ≅ 三个 Σ 的和）。
- `verify x d b 录音 : Maybe Board`：ask 任意、run 重算比结果、sub 递归校验再 merge；`verify-sound`：通过 ⇒ `Build.Legal`。这就是 verifying trace。
- `wrap x d C L`：录音对手，状态 = C 的状态 × 没放完的录音；ask 放、run 真跑后比、sub 校验后记账不跑；对不上就回到 C。`wrap-honest`：C 诚实 ⇒ wrap C 诚实。
- Rebuilder 管「要不要重跑」；一步成功与否归回应和策略；中途前提被改归 Scheduler。

## 玩具实测（ToyStore.agda，全部 refl）
| 节 | Lifting | X | Exec | 对手 | 结果 |
| --- | --- | --- | --- | --- | --- |
| §7 | whole | Unit | play | 真 | x=5，y=2，棋谱 7 条；`transOf incX 2` 是两步事务 |
| §8 | | | | | 写 x 与写 y 填满（`fill-indep`）；两次写 x 空心（`¬ Filled`） |
| §9/§10 | | | | | realm lens 写回；沿 ua 搬运 `moved kx′ ≡ just 5` |
| §11 | realm isY | Unit | play | 真 | 叶子看不见 x：y=0 |
| §12 | whole | Unit | play | wrap 真 | 回放棋谱逐字相同，脚本一条没消费；起点 x=10 时录音在第 2 步失效，9 条，x=17；`replay-legal` 由 `soundHonest` 直接得到 |

## 决定（2026-10-12）
1. Board 固定、Config 不依赖 Board、不用 IR：限制由运输保证（`confineL`），配置的安装史是编排层的日志（状态 = 日志的 fold），不烤进构造子。
2. 运输是数据（`whole | realm`），解释成函数；S7 把配置写成数据时不用回头改。
3. 两类依赖 = 两个 lens 的形状：复制（restrict）vs 消费（enter）。资源表本身不设计，槽先留着。
4. 执行者的全部义务 = `execute-sound`；restarting / 并发执行者要改 Σ（「未就绪」、世界线），改完填同一个槽。
5. 录音粒度 = 整条子线（verify 通过就不跑）；失效后整条子线重跑，分叉点续跑以后再说。
6. 改名：`Square → Filled`（与 Prelude 撞名）、`move → carry`（与 Game 撞名）、`Lift → Lifting`（与 Prelude 的 Lift/lift 撞名）、`Exec.run → execute`（与 Act.run 撞名）。

## 留白
- 同键证书：`Filled` 的其它居民；要先把 `Tx = List WOp` 换成程序 `Free WSig Unit`。
- 回应层面的方块：带回应的独立性 `Indepʳ`，`Legal s (t₁ ++ t₂) s′ → Legal s (t₂ ++ t₁) s′`；Lift 的 snapshot 合并要它（S7）。
- 线性观察者（订阅、令牌）：不在 Store，进账本。
- 有内容的查询语法与非平凡握手律：换 `Query`、`pull`、`handshake` 三个定义。
- 一般的 replay-faithful 定理（玩具里只是 refl 实例）。

## 离接入真预言机还有多远（对照 dev-order-draft v2）
- 已有：S0（签名、自由单子、棋谱由签名导出）；S2 的纯一侧（脚本预言机 + 内存 Store）与第二个解释器（录音回放）；S3 的类型一半（`Rules.impl`）；S7 的槽（运输、上下文 lens、诚实）。
- 缺：S1「状态 = 棋谱的 fold」（`next : Trace → Maybe Op`，换掉手写 `rootProg`）；S4 真模型与提示词投影；S5 棋谱序列化；S3 的管线与一个真工具。
- 硬约束：cubical Agda 不做 IO（原版 GHC 后端拒绝 cubical；自写后端只归约）。所以真预言机只能经**外部驱动器**接入：驱动器每步问 Agda「录音到此，下一步是什么」（`next`，由程序 fold 录音算出），去问 LLM / 跑工具，把 (步, 回应) 追加进录音，再问 Agda；跑完由 `verify` 检查整条录音（`verify-sound` 给合法性）。这正是 decisions 3：LLM 的产出是数据，`verify` 是反射点。驱动器就是 Exec 槽在机外的实现。
- 三步到第一个 LLM 任务：(1) Agda 侧 `next`（一个 fold）+ Op/Res 的编码（或直接用后端的 export/import 包）；(2) 驱动器（约 150 行，LLM 调用 + 沙箱 bash）；(3) 一个把文件快照装进 Store 的工具（世界边界外的效应按 decisions 3 标为未验证）。提示词拼装先放驱动器里，S4 再搬进 Agda 作投影。
