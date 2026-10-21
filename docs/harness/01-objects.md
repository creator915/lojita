# 01 对象：文件、关系、搬运、删除、键表

一句话：文件是一行带属性的记录；文件之间的依赖是表，分持有与引用两种；文件夹是查询；
"树"只是持有这一张表碰巧无环且每个文件恰有一个持有者。Store 的键就是这张关系式 schema 的编码。

## 1 文件是一行

一个节点 = 一个包 `X.agda` 加它的测试 `XTest.agda`，身份是路径 p（也是它的 realm）。它的属性：

```
 属性     值                                                  在哪个键                      v1 / 以后
 path     p，如 twice 或 pow/kids/mul                          键的前缀本身                   v1
 name     模块名 X                                            由 p 的最后一段给出             v1
 spec     接口：stub 文本 + 测试 stub 文本（父写）              p/spec/stub、p/spec/test       v1
 text     正文：填好的文本                                      p/code/X.agda、p/code/XTest.agda  v1
 refute   反驳（若有）                                          p/code/XRefute.agda            v1
 iface    接口哈希 = hash(spec/stub , spec/test)                iface/p（后端算）              M5；v1 用 spec 文本逐字比
 full     全哈希 = hash(code/*)                                 Agda 自己的接口缓存            v1（Agda 给）
 alive    还被持有吗                                            p/dropped 不存在               v1
 result   solved 清单 / refuted 键 / exhausted / 空 = 进行中     p/result                       v1
```

"stub"是带洞的模块：import、具体的 data / record / 谓词定义都可以有，洞是其中的 `postulate` 块。
接口 = spec = 两个 stub 的文本；正文 = 洞填上之后的文本。

## 2 关系是表

每张表是一个 span：一行一条边，源和目标都是文件。

```
             holds                 imports               test-of              refutes
          ╱       ╲             ╱        ╲            ╱        ╲           ╱        ╲
        p        p/kids/K     X.agda    E₀ 模块     XTest     X.agda     XRefute    p/spec
                                        或 kid K
```

| 表 | 源 → 目标 | 种类 | 谁写 | 成环 | 目标没了怎么办 |
| --- | --- | --- | --- | --- | --- |
| holds | p → p/kids/K | 持有 | 父，分解时（写 spec 就是建这条边） | 不可能：目标路径比源长 | 级联：丢弃 K，K 的整个子树到 1 |
| imports | X → E₀ 的模块 | 引用 | 后端 check 时从树上收 | Agda 禁止 import 环 | 不发生：E₀ 任务中不变 |
| imports | X → 自己的孩子 K | 与 holds 重合 | 同上 | 同上 | 同 holds |
| test-of | XTest → X | 引用（内容） | 结构：同一节点 | 否 | 跟节点走 |
| refutes | XRefute → p/spec | 关于规约的定理 | 文件 agent | 否 | 留着，它是最耐久的记忆 |
| spec-of | p/spec → 父 | 父写、子读 | 父 | 否 | 子被丢弃时一起到 1 |

**schema 约束（一包一父）：一个文件只能 import E₀ 和它自己的孩子。** 由现有机制执行：沙箱帧里 `visible` = E₀ + 这个沙箱里刚 check 过的 stub，正是自己的孩子；import 兄弟、堂兄弟、父节点，`mkHeader` 造不出来，或后端回 `imports not in the header`。
这条只管 Agda 树内。IO 壳在树外，不是 Agda 文件：多个壳可以调同一个内核（`08-root-session.md` §4）。

## 3 持有与引用，在这里是什么

| | 持有（holds） | 引用（imports E₀） |
| --- | --- | --- |
| 依赖对方的什么 | 存在：K 因为 p 的洞而存在 | 内容：E₀ 模块的导出名与类型 |
| 寿命 | K 的寿命 ⊆ p 的寿命 | 无关：E₀ 比任何任务活得长 |
| p 改设计时 | K 的 spec 变 → K 重做；K 不要了 → K 整个到 1 | 不受影响 |
| 复制 p | 要深拷贝 K 的子树 | 只复制 import 那一行 |
| 多重持有 | 不允许：唯一持有者，所以是树 | 不适用 |

## 4 存在、删除、垃圾

```
 根存在。p 存在且 p 持有 K 且 K 没被丢弃 ⇒ K 存在。除此之外没有东西存在。
 删除 K  =  把 K 搬到终对象 1  =  父写一行 p/kids/K/dropped = <轮号>
 垃圾    =  从根沿 holds 够不到的前缀
```

- 日志只追加，所以 K 的行都还在，只是没有后继、不进粘合清单。这是历史，不是垃圾；真正的回收是一个压缩工具（M5 之后）：重写 `log.jsonl`，剔掉不可达前缀。
- 引用不参与"存在"的递推：E₀ 由根会话持有，被所有文件引用。
- 持有必须无环、import 必须无环：前者由路径长度保证，后者由 Agda 保证。

## 5 一条原则，与链的终止

**被依赖的接口动了，依赖它的跟着动；接口没动，链到此终止。**

一个文件的接口 = 它的 spec = 它的父写的。所以"B 的接口动了"只有一种发生方式：B 的父改了 B 的 spec。
B 自己只能改正文，或者反驳。于是两个方向：

```
 向上（反驳传播）                               向下（spec 传播）
 C 的正文变        → B 不动：B 只看 C 的 spec    父改设计，逐个孩子比 spec 文本：
 C 反驳 spec       → B 必须改设计                 相等 → keep：孩子的 result 照用，不重跑
 B 的正文变        → A 不动                       不等 → 孩子重新成为任务，它的孩子同理往下传
 B 也反驳          → A 改设计 …                   不要了 → drop：子树到 1
 根反驳            → 根会话：需求矛盾，人改 spec
```

一句话读法：**依赖者有多少是关于被依赖者的，就有多少跟着动。** 父对孩子只"关于"孩子的 spec，所以孩子正文怎么变都不动父；
孩子对 spec 是 100% 关于，所以 spec 一变孩子整个重做；drop 是 100% 到 1。

## 6 两个哈希，各比在哪

| 哈希 | 算什么 | 谁比 | 何时 | v1 |
| --- | --- | --- | --- | --- |
| iface | spec/stub + spec/test | 父，改设计时 | 决定孩子 keep 还是重做 | 文本逐字比（`primStringEquality`），M5 后端算哈希写 `iface/p` |
| full | 填好的正文 | Agda 的接口缓存（`_build/*.agdai`） | 粘合时决定重查还是直接装 | Agda 自带 |

## 7 文件夹 = 查询

v1 的 Query 只有三种项，由后端渲染成提示词（见 `03-env.md`、`05-backend.md`）：

```
 lit  s        固定文字
 row  k        一行的值
 last n k      前缀 k 下最近 n 行
```

以后的文件夹就是更多的项：`kids p`（p 持有的孩子）、`refuted-under p`（子树里结局为 refuted 的）、`importers M`（谁 import 了 M，走 `idx/`）。都是算出来的，不存。

## 8 键表（v1 全量）

`<R>` 是根名（一局一个 store 目录 `runs/<R>-<时间>`，根前缀就是 `<R>`）。p 是任一节点的前缀，形如 `<R>`、`<R>/kids/A`、`<R>/kids/A/kids/A1`。
日志每行是一条 `set`，字段 `k`（键）、`v` 或 `h`（值或 blob 哈希）、`r`（写入时的 realm）、`by`（谁写：`set` / `ask` / `transport`，v8 新增）。

| 键 | 值 | 谁写 | by | 何时 |
| --- | --- | --- | --- | --- |
| `p/spec/stub` | X.agda 的 stub 文本 | 父 agent（transport whole）；根：Boot（set） | transport / set | 分解时；根开局 |
| `p/spec/test` | XTest.agda 的 stub 文本 | 同上 | 同上 | 同上 |
| `p/trace/<step>/prompt` | 渲染出的提示词 | 后端 | ask | 每次 ask |
| `p/trace/<step>/reply` | 答卷原文（大的进 blob） | 后端 | ask | 每次 ask |
| `p/draft/<step>/<file>` | 答卷拆出的文件 | 后端 | ask | 每次 ask |
| `p/code/X.agda` | 当前正文 | agent（transport fill / whole） | transport | 解答、改设计 |
| `p/code/XTest.agda` | 当前测试 | agent（transport fill） | transport | 同上 |
| `p/code/XRefute.agda` | 反驳 | agent（transport whole） | transport | 反驳 |
| `p/verdict/<n>` | 第 n 轮的判决文本 | agent（set） | set | 每次沙箱 / 粘合后 |
| `p/memo/<n>` | 笔记 | agent（set） | set | 驳回、改设计、孩子回来 |
| `p/result` | `solved <k> <键>…` / `refuted <键>` / `exhausted` | agent（set） | set | leave 前 |
| `p/kids/K/dropped` | 轮号 | 父 agent（set，Note drop） | set | 改设计丢弃 K |
| `session/<R>/<n>` | 根会话的记录（v1：spec 副本与一条 memo） | Boot（set） | set | 开局 |
| `iface/p` | 两个哈希 | 后端 | — | M5 |
| `idx/importers/<M>/p` | 反向索引 | 后端 | — | M5 |

`<step>` 是后端的步号（全局递增），`<n>` 是节点自己的轮号。两套号不同，报告里都打。

## 9 不变量与验收：`tests/store/schema.py`

独立于 Agda 和后端的检查器（像 `fold.py`），读一局的 `log.jsonl`，逐条核对下面的不变量。命令与期望：

```
 python3 tests/store/schema.py runs/<局>
 OK  rows=…  nodes=…                      ← 全过
 I2 violated at n=57: twice/code/Twice.agda written by set   ← 有一条就列一行，退出码 1
```

| 编号 | 不变量 | 怎么查 |
| --- | --- | --- |
| I1 | 每条写都在它的 realm 里 | `k` 以 `r` 开头（`r` 为空 = 根会话） |
| I2 | `*/code/*` 只由 transport 写 | `by == transport` |
| I3 | `*/trace/*`、`*/draft/*` 只由 ask 写 | `by == ask` |
| I4 | 任何非根节点在第一条 trace 之前已有两条 spec | 按前缀分组，比较行号 |
| I5 | 根的 spec 由根会话写 | `<R>/spec/*` 的 `r` 为空且 `by == set` |
| I6 | 键的形状合法 | 正则：`<R>(/kids/[A-Za-z0-9]+)*/(spec|trace|draft|code|verdict|memo|result|dropped)…` 或 `session/`、`iface/`、`idx/` |
| I7 | 被丢弃的孩子之后没有新的 trace | `dropped` 之后同前缀无 `trace/` 行 |
| I8 | 每个节点的 ask 次数 ≤ 它拿到的配额 | 配额在 `p/memo/0`（agent 开局写一行 `quota=<q>`）；trace/prompt 行数 ≤ q |

这八条就是第 2–5 节的全部内容，用日志能查的形式写出来。
