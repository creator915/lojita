# Code 类型与反射工具：程序是箭头，环境是点（2026-10-13）

接续 `claude_code-errata-handoff.md`（上一版的勘误：把 Code 做成了项的反射，造了个规约计算器）。
本次从用户原话出发重做：「agda 脚本在上一拍是数据，一经过编译器就是控制，所以 Code 就是整个 agda 宇宙；必须用归纳–递归和延迟模态；参考 Term 把代码表示为语法树；不重造后端，只接通它。」

## 一句话

`Code Γ Γ′` 是从环境 Γ 到环境 Γ′ 的一串声明（箭头）；装一条声明是编排层的一步：这一拍它是数据，后端（Agda 自己的类型检查器）判了 ok，**下一拍**的环境才多了它，续体里才能调用它——▷ 管的是环境的版本。后端是这个签名的余模型，住在 Haskell 里；Agda 这一侧一个 postulate 都没有。

## 文件

| 文件 | 管什么 | 行 |
| --- | --- | --- |
| `src/Later.agda` | 拍签名 `TSig`、延迟模态 `▷`、带索引的程序 `Run`、路 `Walk`（程序和棋谱共用）、余模型、`play` | 110 |
| `src/Code.agda` | 接口宇宙 `U/El`；归纳–递归块 `Env / Decl / Term / Pat / Clause / count`；`Code Γ Γ′` 与范畴 `EnvCat`；洞 | 270 |
| `src/Load.agda` | 两种步 `load / call`、判决 `Verdict`、`CodeSig`；解释器子句 `loadThen`；`accepted`；后端状态的模型 `Impls`；脚本后端；给 Harness 的桥 | 110 |
| `src/ToyCode.agda` | 四条声明的程序装进去再调用，全 `refl`；驳回一条的情形；装之前调不了 | 110 |
| 后端 `Runtime.v5.hs`（`/root/agda-backend`） | `--cubical-drive`：归约到 `load d` 时查、扩展签名；归约到 `call t a` 时算 | +720 |

全部 `--safe --cubical`，零 postulate，零警告。`Game / PathCat / Harness / Store / Replay / ToyStore` 一字未改。

## 范畴图：对象是环境，箭头是程序

```
          Code Γ Γ′ = d₁ ▹ d₂ ▹ … ▹ ∅          （程序：声明序列，这一拍是数据）
   Γ ────────────────────────────────▶ Γ′ = Γ ▸ d₁ ▸ d₂ ▸ …    （下一拍的环境）
   │                                     │
   │ Term Γ n（Γ 里的一个项：点上的东西）     │ 新名字在这里才存在：Name k Γ′ 比 Name k Γ 多
   ▼                                     ▼
  值（后端算）                           call 新工具 / 在后面的声明里 def 它

   EnvCat：Ob = Env，Hom = Code，id = ∅，合成 = 拼接（Later.Walk 的三条律）
   每个环境恰是一条从库出发的程序：path Γ : Code ε Γ（环境 = 程序的 fold，程序 = 环境的日志）
```

上一版做的是左边那一竖（项 → 值），这一版做的是上面那一横（环境 → 环境）。范畴式代码编辑器编辑的是横箭头。

## 归纳–递归在哪（Code.agda §2）

```
   data Env            ε | Γ ▸ d            d : Decl Γ           ← Env 用 Decl
   data Decl Γ         sig A | tool c r | fun f cs | datasig p A | datadef D k cs | recsig p A | recdef R k fs
                       f : Name dn Γ、D : Name dn Γ …           ← Decl 用 Name
   Name k Γ            = Fin (count k Γ)                          ← Name 由 count 算
   count k ε           = 库里的个数
   count k (Γ ▸ d)     = count k Γ + newCount k d                 ← count 对 Env 递归、newCount 对 Decl 递归
   pars Γ D            （数据类型的参数个数，datadef 的构造子类型写在 pars 个参数的作用域里）
```

Env / Decl / Term / Pat / Clause 是 data，count / newCount / pars / Terms / Tel 是对它们递归的函数，一个 mutual 块。
作用域由类型保证：`def f` 的 f 必须小于 `count dn Γ`，引用不存在的名字写不出来；**类型对不对交给后端**，Agda 里不查类型、不求值。

名字是**层号**（库在前，越早越小），按数字写：`# 2`；越界是编译错误（隐式证明 `Bool→Type (ltᵇ m n)` 填不上），不用写证明项。三种名字：定义 `dn`（函数 / 数据类型 / 记录 / 字段 / 工具）、构造子 `cn`、工具 `tn`（工具同时也是定义）。

项层 `Term Γ n` 照 Agda 的 Term 画：var / lam / lit / def / con / pi / sort / meta，n 个局部变量（de Bruijn）。去掉了 Proj 与 IApply：Agda 自己的 reflected 语法也没有它们——字段投影写成 `def f [r]`，路径应用写成普通应用，类型检查器会认。

## ▷ 在哪（Later.agda）

```
   record TSig Ix        Op : Ix → Type        Res : Op i → Type        next : (o : Op i) → Res o → Ix
   ▷ S o X              = (r : Res o) → X (next o r)          一步 o 之后，X 在下一拍的环境里成立
   data Run S A i        done : A i → Run S A i
                         move : (o : Op S i) → ▷ S o (Run S A) → Run S A i
```

`move (load d) k`：这一拍 d 是一个值（数据）；k 的类型写在 `cnext (load d) r` 上——判了 `ok` 就是 `Γ ▸ d`，判了 `fail` 就是 Γ。
所以「新定义下一拍才在环境里、才能被调用」不是约定，是 k 的类型说的：在 Γ 上 `call (# 0)` 写不出来（ToyCode §6），在 `Γ ▸ tool nat nat` 上才写得出来。

和 Game.agda 的关系：`Sig / Free / Comodel / Play` 是 `Ix = Unit`（环境从不变）的特例。棋谱 `Trace Γ Γ′` 是路，类型里带起点终点，「合法」不用另证：状态 = 棋谱的 fold。
没有 guarded 不动点、不要 `--guarded`：程序是有限树，和 Game.agda 一样。

## 反射点：后端是余模型（Load.agda + Runtime.v5.hs）

```
 Agda（--safe，全部保留）                                   后端 agda-cubical-run.v5（Haskell）
   COp Γ  = load (d : Decl Γ) | call (t : Name tn Γ) a      ◀── 这个签名的余模型住在这里：
   CRes (load d)   = Verdict  （ok 指纹 | fail 报错原文）        归约到 move (load d) k：
   CRes (call t a) = El (resOf Γ t)                              把 d 的树翻成 Agda 的 reflected 语法，
   cnext (load d) (ok _) = Γ ▸ d                                 交给 unquoteDecl 背后的那几条
   cnext (load d) (fail _) = Γ                                   （declareDef / defineFun / declareData / defineData），
   loadThen : Code Γ Γ′ → Run … Γ′ → Run … Γ   （纯 Agda）      过了就扩展签名、喂 ok，否则回滚状态、喂 fail；
   accepted : Trace Γ Γ′ → Code Γ Γ′                             归约到 move (call t a) k：查到工具的定义，
                                                                 apply a，normalise，喂给 k，继续归约
```

后端只做三件事：解码一棵树、调 Agda 已有的检查入口、维护一张「层号 ↦ QName」的名字表（和 Agda 侧的 `count` 同步长）。
它没有自己的检查器、没有自己的求值器——「只接通」。

后端补的一条纪律（为了 `--safe` 的精神）：**一条声明只能引用已定义的名字和它自己正在定义的名字**。
引用「sig 了还没 fun」的名字等于用公理；跨两拍的互递归（f 调 g、g 调 f 各在一拍）会逃过终止性检查。每一拍装完都补做 Agda 在 mutual 块末尾做的检查（正性、终止性、单射性）。互递归要另加一种「一拍装一组」的声明形式，列在留白。

调用方式（后端装成 `agda-cubical-run.v5`，默认的 `agda` 仍是 v2）：

```
agda-cubical-run.v5 --cubical-drive=strat --cubical-lib-defs=ℕ --cubical-lib-cons=zero,suc src/ToyCode.agda
```

`--cubical-lib-*` 说库里的 0、1、2 号名字是谁（Agda 侧 `Code 1 2 (λ _ → 0)` 只说了个数）。

## 玩具跑了什么（ToyCode.agda，全 refl）

```
 库：ℕ（dn 0），zero / suc（cn 0 / 1）
 程序 prog : Code ε Γ₄ =
   datasig 0 (sort 0)                               data Color : Set           dn 1
 ▹ datadef (# 1) 2 (Color , Color , tt)             red green : Color          cn 2 / 3
 ▹ tool nat nat                                     twice : El nat → El nat    dn 2，tn 0
 ▹ fun (# 2) [ clause 1 [pvar 0] (suc (suc (var 0))) ]   twice n = suc (suc n)
 ▹ ∅
 策略：loadThen prog (call (# 0) 5) ──脚本后端──▶ 终点 Γ₄，结果 just 7，棋谱 5 条，accepted 棋谱 ≡ prog
 脚本 [ok, ok, fail]：第三条被驳回，环境停在 Γ₂，结果 nothing，棋谱 3 条
```

`path Γ₄ ≡ prog` 也是 refl：环境就是程序的 fold。

## 对勘误 §7 六个问题的回答

1. **程序层的语法**：对照 Agda 的 `Definition / Defn`（函数、数据类型、记录、构造子、公理、原语）和 `Agda.Builtin.Reflection` 的 `declareDef / defineFun / declareData / defineData`。取「先声明后定义」的拆法（`sig / fun`、`datasig / datadef`、`recsig / recdef`），因为 TC 原语就是这样拆的、互递归要靠它、「sig 了还没 fun」刚好是程序层的洞。公理、原语、模块不进 Code（公理与 --safe 冲突；模块 = 一段程序；带参数的模块 = 函数）。
2. **IR**：`Env / Decl / count` 一个块，`--safe --cubical` 下正性、终止性都过了（冒烟 = Code.agda 本身）。
3. **▷**：不用 `--guarded`。`▷ S o X = (r : Res o) → X (next o r)`，是环境索引上的一个算子；Löb / fix 不需要，程序有限。
4. **后端做什么**：不是 checkInternal 一个项，是「每一拍装一条声明、扩展 TCState 里的签名、补做块末检查、回滚失败」，用的全是 Agda 已有的入口。
5. **和 BSALC 接**：`ok` 带新环境的指纹（后端对接受的声明算链哈希）；棋谱记着指纹链，Rebuilder 比它。Agda 侧不算哈希（算了也只是模型），后端的才是真的。
6. **编辑器的对象和箭头**：对象 = Env，箭头 = Code，范畴 = `EnvCat`。程序层的洞 = sig 了还没 fun 的名字（Agda 自己的「先声明后定义」）；项层的洞 = `meta m`，作用域就是它所在的 (Γ , n)，表按洞号查（`Holes / fillHole / zonk`）。

## 决定（2026-10-13）

1. Code 是程序（声明序列），对象是环境。Harness v1 的六个模块一字不改；装进来的工具以**预言机**的身份进代理层（`Load.AsOracle`），由后端作答。
2. 名字 = 层号 `Fin (count k Γ)`，库在前；按数字写（`# n`），越界是编译错误。
3. 工具的接口 `U`（nat / unit / bool / str / list / maybe / pair）是声明里的数据；体由后端查。限制写在接口上。
4. `Res (load d) = Verdict`：`ok` 带指纹，`fail` 带报错原文（喂回给 LLM）。
5. 项层去掉 Proj / IApply，和 Agda 的 reflected 语法对齐。
6. 后端只认「引用已定义的名字」；互递归留给一种新的声明形式。
7. 默认 `agda` 仍是 v2；v5 装成 `agda-cubical-run.v5`。

## 留白

- 后端：`recdef`（记录）还没接（`fail "records are not supported"`）；`checkRecDef` 要把字段望远镜翻成带绑定名的抽象语法，和 datadef 的参数一样的技巧。
- 后端：一拍装一组（mutual）的声明形式；显示名（现在生成 `d2 / c3 / tool0`，报错里会这样叫）。
- 文本 → Code：LLM 写的是 Agda 文本，后端用 Agda 的 parser + scope checker 翻成 Code 值（名字表反查层号）。这是「LLM 写、Agda 查」在程序层的入口，还没写。
- 可判定相等 `Discrete (Decl Γ)`（录音回放按语法对位要它）；`Discrete String` 从 `primStringToListInjective` 拼。
- 弱化 `wk : Decl Γ → Decl (Γ ▸ d)`（编辑器在前面插一条声明时要移名字）。
- 库作为程序：现在库是三个参数（个数 + 参数个数）；原则上库也是从 ε 出发的一段 Code（只有 sig / datasig）。
