# 归档：subagent 递归式的树（2026-10-22 晚）

## 为什么归档（用户定）

受 DeepSeek Harness 影响，10-11 到 10-22 的骨架把 agent 组织成**父程序开孩子、等孩子回来、拿返回值**的递归（suspending 调度）。
10-22 晚用户决定换基础：整个系统是一个范畴式数据库（关系式文件库），一切皆文件，每个文件上挂着 memory 与权限，
特定的行被写就唤起该文件的 agent 跑一轮；agent 之间只有**协议**（写到对方前缀里的行），没有**继承**（调用、返回值、共享栈、配额对半继承）；
与人对话的会话 agent 挂在根上。盘点与新基础见 `docs/reset-2026-10-22.md`。

这里的东西编译都通过（提交 127be63），不是坏代码，是建在错误基础上的代码。

## 这里是什么

| 文件 | 它体现的旧形状 |
| --- | --- |
| `src/Harness.agda` | 配置树 `Config` = agent 种类的树；`sub k sp` 一步 = 开子线并把**整条子棋谱**夹回父的回应；策略树 `Strat` 跟配置走；`Dynamics` 用 `enter` / `leave` 两个 lens 把上下文传下去、收回来。这就是 DSH 的 spawn / fork |
| `src/Replay.agda` | Harness 之上的 Rebuilder：`sub` 的回放 = 校验夹在回应里的子棋谱 |
| `src/ToyStore.agda` | Harness + Replay 的玩具（换运输、换对手） |
| `src/Node.agda` | 文件 agent 的递归程序 `node d q p X`：`kids` 里 `enter` 孩子、**就地跑 `nodeK`**、`leave`、经续体 `Cont` 拿孩子的 `Result`；配额经 `enter` 对半分给孩子；`redesign` 是父的续体 |
| `src/ToyNode.agda` | node 的六局 S1–S6（嵌套 enter 的棋谱形状） |
| `tests/neg/NegNote.agda` | import Node 的反例 |
| `docs/harness/04-node.md` | Node.agda 的规格 |
| `docs/harness-plan.md` | 10-21 的方案；§一明确选了 suspending（"Env 栈帧不动"、"孩子顺序跑"、"重写成 Node.agda"） |
| `docs/walkthrough.md`、`docs/category-frame.md`、`docs/store-and-slots.md` | 10-11 / 10-12 对 Harness.agda 骨架（配置树、纤维、sub）的讲解 |

## 还有用的（新写时照搬，别重新发明）

- `Node.agda` §4 答卷分类 `classify`；§6 提示词 `prompt` / `promptRedesign`（Query）；§3 键构造子 `specStub` / `codeOf` / `kidStub` … 与 `ok-++` 一类证明；
  §7.1 / §7.2 / §7.5 里 transport → 沙箱 check → 粘合 check 的顺序。这些是"一轮"的内容，和调度方式无关。
- `ToyNode.agda` 六局的**断言**（结局行、memo 行数、A 只跑一次、配额耗尽）是新调度器玩具的验收目标；棋谱形状会变（不再有嵌套 enter）。
- `Harness.agda` 的 `Honest` / `soundHonest` 思想：`Later.agda` 的 `play` 已按构造给出合法棋谱；多 agent 的"合法"改由 `Store.Filled`（不同前缀的事务可换）说。
- `Replay.agda` 的 verify / wrap 思想（verifying / constructive trace）在新模型里是对 `trace/` 行的操作，做 Rebuilder 时重写。
- `04-node.md` §8 的程序不变量 N1–N7、`02-agents.md` 的验收 A1–A7 多数仍是目标，只是保证方式变了。

## 怎么退回

`git checkout 127be63 -- src tests docs check.sh`（整个退回 M0 完成时的状态），或逐个 `git mv` 回去并把 check.sh 的三行加回。
