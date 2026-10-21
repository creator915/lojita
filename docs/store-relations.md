# 两种理解合起来：à la carte 的四个词落在任务库和 Store 上（2026-10-14，讨论稿）

接续 store-plan.md（三条选择、五个阶段）、store-and-slots.md、project-context 的
claude_build-systems-state-reading.md 与 claude_decisions.md，以及 10-14 聊天里
"权限资源走树、任务走关系、memory 挂在行上"那一段。本稿只讨论，不开工；末尾五条待拍板。

## 一句话

树状与关系式不是两种架构，是 à la carte 的两个 Scheduler：spawn 等返回是 suspending，
任务库加触发器是 restarting。Store 要管的两种关系，都是 Rebuilder 的 trace 表。

三个结论：

1. memory 挂 agent 还是挂行，由调度器决定。suspending 把半成品留在栈帧里，栈帧就是父 agent 的上下文窗口；
   restarting 没有栈，不写进 Store 的东西就没了。"memory 挂任务不挂 agent"是 restarting 的必然，不是口味。
2. 代码与测试 = verifying trace。测试是 (fake, 条件, 标准)，就是关系式里的 Criterion；
   verdict 行记着依赖的哈希，对不上就重跑。接口哈希变了不是重跑，是重新成为任务。
3. 代码与思维链 = constructive trace。LLM 的回答是输入键，代码的依赖集里列着造出它的那几条回答。
   子实例从父亲那里拿的不是数据，是一个写前缀（树）加一个读 Query（关系）。

## 一、四个词各落在哪

| à la carte | 关系式任务库 | Lojita 现在 / 计划 |
| --- | --- | --- |
| Task k：给它 fetch，它算出 k 的值 | Task 行 + Criterion；细化 = 写 Refines | Spec 进、Report 出；Strat 的一段 prog；Reflect.turn 把回答变成步 |
| Store：k ↦ v，外加持久信息 i | 所有的表 | 一个字符串键 Store，前缀 realm：world/ iface/ trace/，再加 task/ memo/ verdict/ |
| Scheduler：谁先算 | 触发器：就绪就起 agent | Exec 槽 / 驱动器；现在是 suspending |
| Rebuilder：要不要重算 | Verdict / Evidence 的指纹比对 | Replay.verify 与 wrap；Agda 自己的 .agdai 哈希；阶段 3 的 iface/ |

对接的关键一步：**LLM 的回答是输入键。** 论文对不纯计算的办法是 RealWorld 键（§6.3）；
我们把每次 ask 的回复记成 trace/n 这一行。有了它，任务对输入就是确定的，论文的定理照用。
Replay.verify 已经是这个意思：ask 放录音，run 重算比结果。

超出论文的只有一处：论文的 Tasks 是固定函数 k ↦ Maybe Task，整局不变。我们把它放进 Store 的 task/ 前缀，
细化本身是一个任务，它的产出是几行新任务。回答是数据，经 check 才成为控制（想法 5，Harness §7 Reflect）。

## 二、树 vs 关系 = suspending vs restarting

```
suspending（Shake；Lojita 现在的 Dynamics.opp）
  任务 fetch 到一个没算好的键 → 就地递归把它算出来 → 回来接着算
  半成品放在哪：递归的栈帧 = 父 agent 的上下文窗口
  于是 memory 只能挂在 agent 上；子线顺序执行；父 spawn 儿子等返回

restarting（Excel / Bazel；关系式任务库）
  任务发现缺依赖 → 把依赖写成行（Depends / Refines）→ 自己中止
  依赖做完 → 触发器把它重新排进队列 → 从头再跑
  半成品放在哪：没有栈。不写进 Store 的东西就没了
  于是 memory 必须挂在行上；谁就绪谁跑，天然并发
```

论文说 restarting 的中止是免费的，因为任务是纯的。对 LLM 不免费：上下文窗口里的半截推理会丢。
所以 restarting 对 agent 的纪律只有一句：**让出之前，把学到的写成行。**

第三条路是论文 Task/Free 里的物化延续：Finished | Depends k (v → 继续)。"我做到哪了"本身也是一行。
这是想法 5 的最小模型，留给阶段 5 的策略层。

并发从哪里来：每个任务有自己的写前缀，两个任务的事务写的是不同键，fill-indep 自动把方块填满
（decisions 2 的世界线合拢）。memo/ verdict/ trace/ 都是只追加、带唯一行号的行，同键写不会发生。
唯一会争的是父任务的状态格那种可变格子：留证书，或者排队。

## 三、关系一：代码与测试

测试 = (fake, 条件, 标准)：条件成立时，real 与 fake 在标准下一致。这不是新东西，是 Criterion 那张表。
任务一的 `test : twice 3 ≡ 6` 里，fake 是常数 6，条件是输入为 3，标准是 ≡。

```
键                 值                                        谁写
code/M/f           正文（大的进 blob）                         LLM 写、check 过
iface/M/f          类型、依赖、两个哈希：接口哈希 / 全哈希      后端从 Iface 算（接口哈希是新列）
code/M/fake        fake 的正文                                  人或 LLM
spec/std           标准（decisions 3 里人定的观察等价）         人
verdict/T          过 / 不过 + [(依赖键, 当时的哈希)]           check 跑出来：这就是 VT 的一行
```

"代码变了测试怎么跟着变"分两档，靠两个哈希分开：

- 全哈希变、接口哈希没变：测试这句话还成立，只是结论要重算。Rebuilder 看 verdict 行里的哈希对不上，
  重跑 check。这是论文的 verifying trace，一字不改。
- 接口哈希变：测试这句话本身可能不再成立，类型都对不上。这时不是重跑，是重新成为任务：
  谁错了，测试还是代码，要有人或 agent 决定。verdict 行标成待细化，不标 fail。

标准 spec/std 也是键：换了观察等价，它底下所有 verdict 一起失效。

两种测试对应 Store.agda 里 Filled 的两种填法：条件有限，refl 就过，机器填；
条件全称，是证明，LLM 写、Agda 查。

## 四、关系二：代码与思维链

DSH 的做法：memory = 每个 agent 自己的 session 日志。子 agent 要么 fork（拿父亲已完成回合的一次性快照，
之后不再同步），要么 spawn（只拿一句任务文本）。压缩是往日志里追加"用摘要替换前面"的事件，
摘要属于这个 agent。三样都是 suspending 的样子：父亲决定你带什么。

改成行以后：

```
trace/n            第 n 步的 (op, 回应)：ask 的回复在这里，它是输入键
code/M/f           正文；依赖集里列着 trace/n：这就是"这段代码是怎么想出来的"
memo/<about>/m     关于某一行的笔记，about 是任意键：任务、资源、产物、某个哈希
summary/<a..b>     摘要是派生键，依赖 trace/a..b 的哈希，过期由 Rebuilder 判，谁都能用
```

于是代码与思维链在 à la carte 里就是 constructive trace：代码这个键的 trace 行列出造出它的回答，
回答本身在 Store 里。代码重写了，旧回答仍在，只是不在新代码的依赖集里。
挂在 agent 上的话，两者混在同一个窗口里，agent 死了全没。

子实例拿什么：父亲在 enter 时给两样东西，不给数据。

```
写：一个前缀 p     沿树收紧，restrictL / mergeL，类型上保证（prefixOf 前置条件）
读：一个 Query     沿关系汇聚：memo 关于 t、关于 t 的 Needs、关于 Depends 的产物、沿 Refines 的祖先
```

这就是聊天里"记忆取并、权限取交"：写权限是 lens，走树；读是查询，走关系，不占行。
现在 Store.agda 的 Lifting 是对称的：realm R 同时限读限写，R 外 get 回 nothing。
要改成**读的范围大于等于写的范围**：写仍是 realm 前缀，读是一个 Query。阶段 2 本来就要把 ask 的参数换成 Query。
三条 lens 律只对写那一侧要求：PutGet 在写前缀上成立，confine 照旧。

上下文窗口有限的问题，落成一个显式的东西：提示词 = cut s q，q 是数据，后端增量算。
裁剪、加权、截断都是换 q，不是换架构。

## 五、合成一张图

```
             Store（一个实例，后端在硬盘上线性持有）
   ┌────────┬────────┬────────┬────────┬────────┬─────────┬────────┐
   task/    trace/   memo/    code/    iface/   verdict/  world/
   任务行   录音     笔记     正文     类型哈希  测试结论   文件快照
   细化写   ask 回复 about=键 LLM 写   后端算    check 出   sh 落这里
   └────────┴────────┴────────┴────────┴────────┴─────────┴────────┘
        ▲ 写：前缀 p（树）                 ▲ 读：Query（关系）
        │                                  │
   Agent = (配置树的某个 kid, Spec, 前缀)：任务上方的纤维，弱实体
        │ Scheduler 在任务就绪时起它（sub），leave 时消失，自己不持数据
   Rebuilder = verify / wrap：读 verdict 与 trace 的指纹，决定重跑还是放录音
   Scheduler = 驱动器：现在 suspending；restarting 要在 Σ 里加"未就绪"，填同一个 Exec 槽
```

配置树和任务库不冲突：配置树是 agent 的种类（工具表、规则书、能碰的前缀），任务行是工作的实例。
触发器做的事是：任务就绪，挑一个合适的 kid，sub k sp。

聊天里留下的四个问题，落到哪：

| 问题 | 落点 |
| --- | --- |
| 上下文太大怎么裁 | 换 Query；摘要是 summary/ 派生键 |
| Refines 把树带回来 | 它是唯一的树，而且是历史。restarting 运行时没有树，只有 Depends 的 DAG |
| 触发器怎么调度 | 就是 Scheduler，单独一个槽；execute-sound 是它唯一的义务，soundHonest 证一次不动 |
| 细化到什么程度 | 策略层（Strat）的事，论文和数据库都不回答 |

## 六、动工时会碰到的地方（只列，不做）

- Store.agda：Lifting 读写分开；memo/ verdict/ 这类只追加的行要么复用日志行号 n 当键尾，要么加一个"追加一行"的原语。
- Harness.agda / Replay.agda：sub 的回应现在夹着整条子棋谱 (rep , ct)。改成子棋谱在 Store 的 trace/ 前缀里，
  回应只带指针；verify 从 Board 里读子棋谱。verify-sound 的形状不变，多一个 Board 参数。
- Env.agda：ask 的参数换成 Query（阶段 2 已定）；check 的 Iface 行落 iface/（阶段 3 已定），加接口哈希 / 全哈希两列。
- 阶段 5 策略：restarting 的纪律写成程序形状，发现缺依赖就写行、leave；或者物化延续。

## 七、待拍板

1. 读权限：子实例的读是否不受前缀限制（Store 里永远不放密钥，密钥只走环境变量），还是 enter 时也给一个读集合。
2. 调度器：阶段 2、5 先用 suspending 把 trace 落盘，并发真的需要时再改 Σ；还是阶段 2 就按 restarting 的形状设计 trace 行。
3. 子棋谱：指针进 Store，还是继续夹在回应里。影响 Replay 的类型，不影响定理。
4. 标准 spec/std 做不做成键。
5. 接口哈希变时：标成待细化的任务行（推荐），还是直接 fail。
