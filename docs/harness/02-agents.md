# 02 两类 agent：文件 agent 与根会话

一句话：文件 agent 挂在一个文件上，memory 和权限都是那个文件的前缀；它只能编辑这一个文件（经搬运），
能开它持有的文件的 agent，并给它们发搬运协议。根会话挂在根上，是人与 LLM 的对话，写根的 spec 与 E₀，收根的结局。
一个会话 = 一个根 = 一个 store 目录。

## 1 一张图

```
 根会话（人 + LLM；memory = 会话本身，副本在 session/<R>/）
   │  写 <R>/spec/stub、<R>/spec/test；定 E₀（包名单 + flag）；给配额；启动根的 agent
   ▼
 根的文件 agent = node d [R]                 memory = <R>/{trace,memo,verdict,result}；权限 = realm <R>/
   │  enter kids/A 之前：transport whole 把 A 的两个 stub 写进 <R>/kids/A/spec/；配额分一份给 A
   ▼
 A 的文件 agent = node (d−1) [R,kids,A]      memory = <R>/kids/A/…；权限 = realm <R>/kids/A/
   │
   ▼  …
 leave：Result 作为返回值回到父的程序里；行 p/result 只是记录
```

两类之间没有第三种东西：没有"调度器 agent"、没有"审查 agent"。调度是 `node` 程序的控制流；审查是 Agda 的 check。

## 2 文件 agent

### 2.1 身份

路径 p。它就是 `node d p` 这段程序在后端上的一次运行，LLM 只是它的预言机（`ask` 这一步的回答者）。
换一个 LLM、换一个进程续跑同一个节点 = 再跑一次 `node d p`，读同一个前缀。"agent"没有别的身份。

### 2.2 memory

全在 p 下，分四种，谁写见 `01-objects.md` 键表：

```
 p/spec/*       父写的规约（它的任务）                         读
 p/trace/*      每次 ask 的提示词与答卷（后端写）              读（经 Query 的 last）
 p/memo/*       自己的笔记：驳回摘要、改设计的理由、孩子的反驳  写、读
 p/verdict/*    每次 check 的判决                             写、读
 p/result       结局                                          写
```

它看见的上下文 = 对 p 的一个 Query。提示词里带多少历史，是换 Query，不是换架构。

### 2.3 权限：按文件 × 操作类型

一个 agent 由 memory 和权限组成，权限 = 它对每个文件有哪几类操作（open / close / read / write，见 `10-files-resources.md`）。以 p 为自己、K 为孩子：

```
 文件               open                  read                   write                          close
 自己的 code        —                     Query 的 row           transport fill / whole         —
 自己的 Test        —                     row                    transport fill（只填证明）      —
 自己的 memo 等     —                     last                   setN                           —
 孩子 K 的 spec     写 = open             row（改设计时比对）     transport whole                keep = close；drop = 搬到 1
 孩子 K 的 code     checkAt（让检查器读）  没有                   没有                           —
 孩子 K 的 agent    enter（分一份配额）    Result                 spec 就是写给它的协议            leave
 LLM                挂载即开              ask 的回应              ask 的提示词                    —
 检查器             挂载即开              Verdict                checkAt                        —
 父、兄弟的任何文件  没有                 没有                   没有                           —
```

都在类型里（`Env.agda`）：写 = `isPrefix realm k`；读越界回 nothing；配额 = `1 ≤ᵇ 配额`；能开的帧只有三种：沙箱（同 p、零配额、E₀⁻）、孩子（p/kids/K、分一份配额、E₀⁻）、粘合（同 p、零配额、E₀）。

### 2.4 能做什么、不能做什么

| 能 | 不能 |
| --- | --- |
| ask | 改自己的 spec（那是父的；觉得 spec 错 = 写反驳） |
| transport 自己的 `code/*`（fill / whole） | 用 set 写 `code/*`（NodeSig 的 set 键只有 memo / verdict / result / dropped） |
| 写 memo / verdict / result | 读父、兄弟、堂兄弟的任何行 |
| 给孩子写 spec（transport whole 到 `p/kids/K/spec/*`） | 给孩子写 spec 以外的东西 |
| enter 孩子、等它回来、拿 Result | 和孩子"对话"：孩子跑的时候父在等 |
| 粘合时 checkAt 孩子的 `code/*`：让检查器读 | 自己读孩子的 code；把它喂给 LLM（Query 里没有这一项） |
| drop 孩子 | sh、eval、编辑器三步（不在 NodeSig 里） |
| 在沙箱帧里 checkAt | 在节点帧里 checkAt |
| import E₀ 和自己的孩子 | import 别的任何模块（检查器拒） |

### 2.5 生命周期

```
 enter（父做）──▶ 第 1 轮 ──▶ … ──▶ 第 n 轮 ──▶ 写 result ──▶ leave（父做）
                  每轮：ask → 分类 → transport → 沙箱 check →（粘合 check）→ 过 / 记 verdict、memo
 三种结局：solved（清单）  refuted（反驳的键）  exhausted（配额 0）
```

分支细节在 `04-node.md`。

### 2.6 重启

进程死了，节点的行都在。再跑一次 `node d p`：第一轮的 Query 带 `last 3 memo/`、`last 2 verdict/`，
所以第一条提示词就带着上次的教训。v1 不做"从第 k 步续"，只做"从头再来但记得"。

### 2.7 搬运协议：文件 agent 之间唯一的话

父对孩子说的话只有两种，都是行：

| 时机 | 协议 | 落成的行 |
| --- | --- | --- |
| 第一次开孩子 | 这是你的 spec | `p/kids/K/spec/stub`、`p/kids/K/spec/test` |
| 改设计 | keep / whole / drop 三种之一 | keep：什么都不写；whole：重写两条 spec；drop：`p/kids/K/dropped` |

孩子对父说的话只有一种：`node` 的返回值 Result。

### 2.8 open / close 的生命周期

拿 1.agda import 2.agda、2.agda import 3.agda 说：

```
 1.agent 写 2Test（transport whole 到 kids/2/spec/）   ⇒ 2.agent 被 open（enter）
 2.agent 开着                                            直到新的 2.agda 通过 2Test
 2.agent 回 solved                                     ⇒ 2.agent close（leave）；2Test 也 close：spec 定了 = keep
 2.agent 回 refuted / exhausted                        ⇒ 2.agent close 了，2Test 仍开着：1.agent 重写（whole）或丢弃（drop）
 2.agent 对 3 做同样的事；1.agent 对 3 没有任何操作
```

v1 顺序版：open 由父显式做。M5 的 restarting 版：对 2Test 的 write 事件本身触发 2.agent 的 open。
树内固定：每个 Agda 文件恰一个 agent，签名都是 NodeSig，纪律由 Ix 给。树外开放：壳、硬件、根会话由挂载表定。

## 3 根会话

### 3.1 是什么

方案 2.0 与 2.1 那几轮：确认需求、写根的 spec、定 E₀、给配额。它的产物：

```
 <R>/spec/stub        根的 stub：R.agda 的签名、它要用的类型；若人已决定要分解，可以直接 import 孩子名
 <R>/spec/test        根的测试陈述；对 IO 根是对着 mock 余模型的 refl
 E₀                   包名单 + flag（含 --safe）；写在 Boot 的常量里
 配额、树深            Boot 的常量
```

### 3.2 memory

会话本身。副本写进 `session/<R>/<n>`：v1 只写 spec 的副本和一条 memo（任务一句话）；以后每轮对话一行。

### 3.3 它收到什么

```
 <R>/result = solved …    产物在 <R>/code/* 和各孩子的 code/*；清单是依赖序，拼起来就是整个程序
 <R>/result = refuted k   需求矛盾：反驳在 k；人改 spec，再开一局
 <R>/result = exhausted   加配额，或改 spec
```

### 3.4 几个根

一台中心化设备一个根 = 一个 store 目录。分布式系统多个根，每个自己的目录（或自己的机器），只共享 E₀ 里的协议签名（`08-root-session.md`）。
会话数不会多：绝大多数工作在文件 agent 上，根会话只在开局和收尾说话。

### 3.5 v1 实现

`Boot.agda`：常量（spec 两段文本、E₀、配额、树深）+ `main = 写 spec → 写 session 行 → embedRun (node d [R]) → 打印 result`。见 `08-root-session.md`。

## 4 通道一览

| 谁 → 谁 | 载体 | 内容 |
| --- | --- | --- |
| 根会话 → 根 agent | 行 + Boot 常量 | spec、E₀、配额、树深 |
| 父 agent → 子 agent | 行（enter 前） + enter 参数 | spec；配额 |
| 子 agent → 父 agent | `node` 的返回值 | Result |
| 根 agent → 根会话 | 行 + Boot 打印 | result |
| 别的方向 | 没有 | |

## 5 验收

| 编号 | 标准 | 怎么查 |
| --- | --- | --- |
| A1 | 任何 agent 的所有写都在自己前缀里 | `schema.py` I1 |
| A2 | 孩子的 spec 先于孩子的第一次 ask | `schema.py` I4 |
| A3 | 根的 spec 由根会话写 | `schema.py` I5 |
| A4 | ask 次数不超配额 | `schema.py` I8 |
| A5 | 重启记得：同一目录第二局的第一条提示词含第一局最后一条 verdict | `./node.sh dry tests/node/scripts/fail-once.txt`（第一局 exhausted）再 `./node.sh dry tests/node/scripts/pass.txt --same-dir`；`python3 tests/node/report.py runs/<局> --prompt 1` 打印第二局第一条提示词，里面有第一局的报错原文 |
| A6 | 父不读孩子：父前缀下的 trace/prompt 不含孩子 `code/` 的内容 | `report.py --prompt` 逐条看；机械版：孩子 code 文本的首行不出现在父的任何 prompt 里（`report.py --check-isolation`） |
| A7 | 孩子回来后父只多一步记忆 | 父的 `memo/` 在孩子 leave 后恰多一行（`report.py` 的树里显示每节点 memo 数） |
