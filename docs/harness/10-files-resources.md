# 10 一切皆文件：抽象文件、四类操作、资源的形式化

一句话：Linux 说一切皆文件，设备、进程、管道都是 open / close / read / write 的对象。把这句话搬进 Agda 封闭世界：
窗口 Σ 不是一列零散的步，是一个目录；目录里每个抽象文件有四类操作；open / close 是线性的，read 随便复制，write 是追加一个版本。
权限就是"对哪个文件有哪类操作"，agent 就是一个带 memory 的文件。脑看目录，手实现文件。这一页是展开，不改 v1 的代码。

## 1 抽象文件

```
 抽象文件 F = (状态 S_F , 四类操作)
   open    取得句柄。线性：之后必须 close。可能失败：没挂载、没权限、容量满
   close   归还句柄
   read    看一眼，不改状态。快照，可复制
   write   换一个新版本。追加：旧版本还在
```

在 Game / Later 的词汇里，一个抽象文件就是一个余模型：有状态，按操作作答。四类是操作的**类型**，不是四个构造子：
一个文件可以有很多具体的 write，用不同工具、带不同权限，它们都属于"换版本"这一类。

## 2 操作类型与具体操作

同一个 Store 文件上的 write 有三种具体形式，类型相同、工具与权限不同：

```
 具体操作           工具                 权限                                  谁发
 set k v            直接写               k ∈ Note 的四种键（memo verdict result dropped）  agent
 transport m t s d  fill / whole         t ∈ realm 且在 code/ 或 kids/K/spec/ 下          agent
 ask 的落盘         后端代写             trace/ draft/ 只有后端写                           后端
```

read 也有两种：`get k`（一行）和 Query 的 `row` / `last`（后端渲染给 LLM 看）。open / close 只有一对：`enter` / `leave`。

## 3 Σ 是一个目录

把现有 `AgdaSig` 的每一步按（文件，操作类型）归位：

```
 文件           open              close    read                 write                              谁实现
 store/<p>      enter（realm）    leave    get、Query           set、transport、（ask 的落盘）       store:DIR
 proc/<p>       enter（配额）     leave    Result（返回值）      spec：transport whole 到 kids/K/spec/ 驱动器 + node
 llm            挂载即打开        —        ask 的回应           ask 的提示词                        ask:http / script / fixed
 agda           挂载即打开        —        Verdict              checkAt（键）、check（值）            agda 进程自己
 eval           —                 —        Answer               eval                                agda 进程
 sh             —                 —        (rc , 输出)          sh                                  sh:DIR
 editor         —                 —        Goals / Edit         goals / give / split                agda 进程
```

`enter` 同时打开两个文件：一个子文件系统（realm）和一个进程（孩子 agent）。v1 把它做成一个步；按目录读法它是两次 open。

## 4 open / close 是线性的：Ix 就是打开文件表

```
 Ix = 栈顶 × 其余      每一层 = (环境 , 配额 , realm) = 一个打开着的 (proc , store 子目录)
 enter 压栈 = open     leave 弹栈 = close     leave 要 hasParent：没 open 的不能 close
 子只能更窄更穷        打开的子目录 ⊆ 父的；进程的预算 ≤ 父的
 read 不占栈           get、Query 想读几次读几次（catdb 第四轮：快照读自带 ?）
 write 追加            日志只追加；"覆盖"只是读时后写胜
```

这就是"负侧是线性的、快照读可复制"落到文件上：open / close 走账本，read 不走。

## 5 权限 = Σ

```
 一个 agent 的权限 = 它能发的步的集合 = 它的签名 NodeSig = { (文件 , 操作类型 , 约束) }
   (store/p , write , 键 ∈ Note)                          setN
   (store/p , write , 目标 ∈ realm，工具 fill / whole)      transport
   (store/p , read  , 键 ∈ realm)                          get、Query
   (proc/p/kids/K , open , 配额 ≤ 父)                     enter
   (llm , write + read , 配额 ≥ 1)                         ask
   (agda , write + read)                                   checkAt
 没有的就是没权限：sh、eval、裸 set、读 realm 外
```

权限表和工具注册表是同一张表；`Env.agda` 的前置条件就是约束那一列。

## 6 进程也是文件：agent 文件

每个计算文件配一个抽象 agent，由 memory（这个文件历次变更的思维链叠在一起）和权限组成。规约与计算是一体的，所以 agent 挂在计算文件上，不另挂在测试上。

```
 1.agda ──import──▶ 2.agda ──import──▶ 3.agda

 1.agent 的权限
   1.agda        read / write（transport fill / whole）
   1Test.agda    read；write 只能填证明（fill）：陈述是 1 的父写的
   2Test.agda    open / read / write（transport whole 写 stub；改设计时重写）
   2.agda        open（checkAt：让检查器读）；没有 read
   2.agent       open（enter）/ read（Result）/ close（leave）
   别的文件      没有
```

生命周期，按前面的逻辑推演：

```
 1.agent 写 2Test            ⇒ 2.agent 被 open
 2.agent 开着                   直到新的 2.agda 通过 2Test
 2.agent 回 solved            ⇒ 2.agent close（leave）；2Test 也 close：spec 定了 = keep
 2.agent 回 refuted/exhausted ⇒ 2.agent close 了，但 2Test 仍开着：1.agent 必须重写它（whole）或把 2 搬到 1（drop）
```

v1 是顺序的：open 由父显式做（`enter`）。M5 的 restarting 版本里，"2Test 被写"这个 write 事件本身触发 2.agent 的 open，触发器就是对 spec 文件的 write。

**树内固定，树外开放。** Agda 树里每个文件恰一个 agent，签名都是 NodeSig，open / close 的纪律由 Ix 给，形状不随任务变。
树外的文件（壳、硬件、根会话）由挂载表决定，形状开放。

## 7 硬件与外部服务也是文件

```
 llm        写提示词、读回应；状态 = 会话，或无状态
 时钟       只读；状态 = 时间
 网络       写请求、读响应；open = 连接
 GPU、进程  写任务、读结果；open 受容量限制
```

每个这样的文件在 Agda 里有一个模型：脚本余模型（mock）。形式验证对着模型做，部署时换成真手。
唯一的假设是 Honest：真手每答一步都是模型允许的一步。模型错了，错在一个文件上，不散在树上。这就是脑手分离。

## 8 挂载表 = handler 表

`--cubical-handler=name:spec` 就是 mount：把一个真实现挂到目录里的一个名字下；没挂的名字 = 没有这个文件，步一到就停机（现有行为）。
挂载在开工前做完，跑起来不换；"工具注册表开工前设定好"说的就是挂载。

## 9 Agda 能验什么，不能验什么

```
 能（类型或定理）   open / close 配对；子窄于父；写在 realm 内；读越界为空；代码只经 transport；配额不超；整局合法（soundHonest）
 不能               手的真实行为（假设 Honest）；时间；容量（一次能开几个 = 填满方块的最高维数，catdb 第三轮）；性能
```

## 10 对 v1 的影响

- 代码不变。文档里只改一处：`04-node.md` 的 `parse` / `check` 换成 `checkAt`，agent 对孩子的 code 只有 open 没有 read，读的是检查器（`03-env.md` §4.5、`05-backend.md` §3b）。
- Σ 现在还是平的一列构造子。把它重排成"目录 × 四类操作"的 record 是 M5 以后的重构，定理不动。

## 11 待展开

- 容量：同时能 open 几个 = 填满的方块的最高维数。并发孩子时要。
- 时钟文件与超时。
- GitHub 作为版本化文件：write = commit，schema 变与值变都进历史。最彻底的函数式，未必值得；暂不做，记一笔。
- 跨机器：两个壳之间的 socket 文件；协议仍在 Agda（`08-root-session.md` §4）。
- 压缩 / GC：不可达前缀。
