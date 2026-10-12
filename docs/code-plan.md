# Code 类型的方案：完整的 Agda 宇宙，直接接 agda 程序（2026-10-13）

接续 `archive/2026-10-13-code-v5/README.md`（为什么上一版归档）和 `claude_code-errata-handoff.md`。本页是方案，不是实现；用户在本会话定下的几条标在「定」。

## 一句话

Code = Agda 的 **concrete 语法**（parser 吐出来的那棵树）原样搬进 Agda：一个构造子都不少，名字是字符串，糖和 unsafe 都在。环境 Γ = 已检查模块的接口 × 当前 flag（语境 × 余语境）；`Code Γ` 由 Γ 递归算出（只能 import Γ 里有的、flag 只降不升），这是归纳–递归；`check` 的回应带回新接口，下一拍才进 Γ，这是 ▷。余模型 = `agda` 这个 Haskell 程序自己的入口，不走反射 API。

## ① 载体：从 Agda 源码生成

`Agda.Syntax.Concrete`（Declaration ≈ 37 个构造子、Expr ≈ 45、Pattern ≈ 17、Pragma ≈ 34、ImportDirective、Fixity / Notation）加 `Agda.Syntax.Common` 的修饰（Hiding、Relevance、Quantity、Access、Erased、Induction …）和 `Literal`，用脚本逐构造子翻成 Agda 的 data（去掉 Range；Text → String；Integer → ℕ / ℤ）。同一脚本生成 Haskell 两个方向的翻译。

```
 文本 ─parser─▶ C.Module ─encode─▶ Code（Agda 值）─decode─▶ C.Module ─nicify / scope / check─▶ Interface
 完整性判据：cubical 库 + Lojita 的每个文件  parse → encode → decode → pretty → parse  回到自身
```

注释：parser 丢了它，编辑器要它。从 token 流取回来挂在声明上（doc 字段），check 前剥掉。
De Bruijn 不出现在 Code 里：那是检查器内部（Internal Term）的事，Code 是表层。

## ② 环境：语境 × 余语境，归纳–递归在这

```
 Env     ε                  父给的库：一组接口 + 一组 flag
         Γ ▸ (m , i , h)    m : Code Γ 过了检查；i 它的接口（后端算的）；h 指纹
 Code Γ  = Σ[ m ∈ Module ] (imports m ⊆ visible Γ) × (flags m ≼ flags Γ)      对 Γ 递归，可判定
 visible Γ = ε 的模块 + 链上每个 m 的名字；flags Γ = 链上最严的那组
 Iface   = 导出名 + 类型（Expr，仍是 Code）+ 种类 + fixity
```

Env 用 Code 造，Code 由 Env 算。它管模块这一级（能 import 谁、能开什么 flag），正好是父实例控制子实例的那一级；声明内部的名字由 Agda 的 scope checker 查，不在类型里重做。

## ③ import / flag 是模态算子，Agda 已经有这套规则

| 算子 | 作用在 | 只降不升 = Agda 的哪条规则 |
| --- | --- | --- |
| `open import M using / hiding / renaming` | 语境 Γ | 只能 import visible Γ 里的；using ⊆ 导出名。= Store 的 realm R |
| `--safe`、`--without-K` 这类 coinfective | 余语境 | 父有子必有：子关不掉 |
| `--cubical`、`--guardedness`、`--sized-types`、`--rewriting` 这类 infective | 余语境 | 父没有子不能开，否则父 import 不了子（InfectiveImport） |

父开子 = 写子模块的头两行（flag + import … using），Agda 在 import 时复核。资源 Σ 不在 Agda 语法里，仍走 X / enter / leave。

## ④ 余模型 = agda 程序的入口（像 IO 例子）

```
 AgdaSig  quote : String → Op      回应 Maybe Code                 ← Agda.Syntax.Parser（LLM 的文本从这进）
          check : Code Γ → Op      回应 ok Iface Hash ∣ fail 报错    ← createInterface：nicify、scope、type check、
                                                                      接口哈希、登记进已访问模块表（后面的 import 找得到）
          eval  : Expr → Op        回应 Expr（规范形仍是 Code）      ← inferExpr + normalise + reify + abstractToConcrete
          goals / give / refine / caseSplit                        ← InteractionTop（Emacs 模式背后那套，编辑器用）
 next Γ (check m) (ok i h) = Γ ▸ (m , i , h)；fail 环境不动
 W Γ = Γ 处的 TCState 快照：Haskell 里是持久值，开几个子 = 从同一快照分叉
```

flag 不由驱动器解释，createInterface 自己按 OPTIONS pragma 生效：unsafe 代码能进 Code、能被检查，但 `--safe` 的父 import 不进来。失败回滚（putTC）、每拍补做块末检查、错误类警告当错误：照 v5。

两种接法（区别见 §⑦）：
- A：decode 成 `C.Module`，在进程内从 createInterface 的 parse 之后那一步接进去。
- B：decode 后用 Agda 自己的 pretty 打成文本，走 agda 的标准文件管线（parse 起）。

## ⑤ 受限的 Code（定）

实践上很简单：**一个范畴就是一个 module**——公理在模块参数里（不是 postulate），里面用 record 造对象、箭头、律；任何范畴都这样造。
开子实例的语言：对象 (R, Σ)，箭头 = (R′ ⊆ R , Σ′ ≤ Σ)，自由度只有这两个坐标；它转成子模块的头两行。不要想复杂。

## ⑥ 编辑器与数据库的铺垫

结构 = 接口（TypeSig / DataSig / RecordSig），实现 = 子句 / 构造子 / 字段，同一棵树的两种投影；洞 = Agda 自己的 `?`；编辑器的一步 = Agda 的一条交互命令，棋谱 = 编辑历史。
数据库的键 = 声明名，值 = 检查后的哈希 + 接口条目，依赖 = 后端做 scope check 时得到的自由名；代码改了，依赖它的测试声明重查（Rebuilder）。

## ⑦ 接法 A 与 B 的区别

```
 A  Code ─decode─▶ C.Module ──────────────────────▶ nicify → scope → check → Interface     （树是真相，从 parser 之后进）
 B  Code ─decode─▶ C.Module ─pretty─▶ 文本 ─parse─▶ nicify → scope → check → Interface     （文本是真相，从大门进）
```

| | A | B |
| --- | --- | --- |
| 多做的事 | 伪造"源文件"的簿记（模块名 ↔ 文件、已访问模块表、接口缓存）——自己写、随 Agda 版本变 | 调 Agda 自带的 pretty，多一次 parse（几毫秒） |
| 依赖谁忠实 | 只依赖 decode | 依赖 decode 和 pretty 的回环 |
| 报错位置 | 全是 noRange：有名字没行号 | 有行号列号（在打印出来的文本里），可以连文本一起喂给 LLM |
| `.agdai`、接口哈希、交互点 | 要自己补 | Agda 的文件管线免费给：iFullHash 就是指纹，`?` 有位置 |
| 回环测试 | 另外跑 | 每次 check 都在跑（pretty 不忠实立刻暴露） |

从 Agda 世界看两者一样：都是 `check : Code Γ → Op`。B 用临时文件是余模型内部的事，不是 shell。
建议：**B 先做**（少写自定义代码、报错有位置、验收即实现），pretty 不够忠实或嫌慢时再换 A。

## 决定（2026-10-13）

1. Code = 完整的 Agda concrete 语法，从 Agda 源码生成；名字是字符串；糖和 unsafe 都在。（定）
2. import / flag 是模态算子，必须在 Code 里；只降不升由 Agda 的 infective / coinfective 规则复核。（定）
3. 一个范畴 = 一个 module，公理在参数里。（定）
4. v5（核心子集 + 反射 API）归档。（定）
5. 接法 A / B：待定，建议 B 先做。
