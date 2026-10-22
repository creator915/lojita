# Harness 方案：规约与代码为对象，一棵树一个微服务，Store 为载体（2026-10-21，设计稿）

接续 10-21 的讨论（本稿的来源）、`store-relations.md`（五条待拍板，第 1、5 条在本稿定）、`code-design.md`（Code v6）、
`store-backend.md`（后端 v7），以及上传稿《Code 的粘合与搬运》《abstract 语法》。本稿只设计，`src/` 一字未动。

> 2026-10-21 晚：本稿展开成开发文档夹 `harness/`（每个部件一页，含逐条验收），以它为准。那里多出两处设计：底层是关系式的文件库
> （`harness/01-objects.md`），agent 分文件 agent 与根会话两类（`harness/02-agents.md`）；两处小改：测试模块叫 `XTest`、反驳叫 `XRefute`（不用带点的名字），
> stub 可含具体定义，洞只是其中的 `postulate` 块。
设计思路有过转变：现有代码里的配置树、策略树、Solve 的循环都不再是主线；哪些留、哪些绕开，第一节列。

## 一句话

一个微服务 = 一棵树。根是带 IO 的 `Run` 程序，其余节点是纯 Agda 包。每个节点 = (包 , 测试) 一对：
父节点写孩子的规约，规约就是两个只有签名的 stub 模块；孩子填实现与证明，或者反驳规约。
整棵树住在 Store 的一个前缀下，节点只经 enter 的参数和 leave 的返回值通信；代码只经搬运写入；没有别的通道。

## 零、总图

```
 E₀  任务开工时定死：能 import 的包 + flag。任务中不变，是唯一能被多个节点 import 的东西
  │
  root/            root.agda + root.Test.agda          根：Run AgdaSig 程序 + 对着 mock 余模型的测试
  ├── kids/A/      A.agda + A.Test.agda                规约 = 父写的 stub；实现 = 子 fill
  │    └── kids/A1/ …
  └── kids/B/      B.agda + B.Test.agda

 Store 前缀 = 树的路径。写 = 自己的前缀（类型里）；读 = E₀ + 自己的前缀
 向下只有 enter 时写进孩子前缀的规约；向上只有 leave 带回的结果；正文只有 Agda 读
```

三个阶段，三种 flag：

```
 洞阶段   在 E₀⁻（E₀ 去掉 --safe）：A.stub × B.stub × root ⊢ root.Test      假设 = postulate
 解阶段   孩子各自：A.stub ↦ A（fill），A.Test.stub ↦ A.Test（fill）
 粘合     在 E₀（加回 --safe）：子树全部模块按依赖序重查                      --safe = 没有假设剩下
```

`--safe` 是 coinfective，往下只能加不能减，所以"粘合帧"是节点帧的合法孩子；postulate 在 `--safe` 下不存在，所以洞阶段必须在 E₀⁻。
这两条都是 Agda 自己的规则，`Env._≼_` 已经写着。

## 一、转变：现有代码哪些契合、哪些绕开

| 现有 | 本稿 | 处置 |
| --- | --- | --- |
| `Harness.agda`：配置树 = agent 种类的树（规则书、工具表、Kids），策略树 `Strat` 跟配置走 | 树 = 程序的模块树；每个节点同一个 Σ | 留作通用定理（`soundHonest`），不在主线上。新 harness 建在 `Later` + `Env` 上 |
| `Env.agda`：栈帧 (E , 配额 , realm)，`enter` 只能更窄更穷，`get` 越界 nothing，`set` 越界类型错 | 原样就是权限模型：写 = 前缀，读 = 前缀 | 不动。`store-relations` 待拍板 1 定为"读不放宽成 Query" |
| `Env.agda`：`ask : String`，回 `String`；程序自己拼提示词、自己持答卷 | `ask : Query`，后端渲染提示词、把答卷按文件拆进 `draft/`，回文件名表 | 改 `Res (ask)`，加 `Query` |
| `Env.agda`：`check : Code E`，程序持有 `Module` 值 | 不变。模块文本在 Store 行里，用时 `get → parse → mkCode → check`，只在那一步持有 | 不动 |
| 代码的写入：`set` 任意文本 | 代码行只经 `transport` 写；`set` 留给 verdict / memo / result | `Env.agda` 加 `transport`、`audit` |
| `Store.agda` / `Keys.agda` / 后端 v7 `store:DIR` | 原样 | 不动 |
| `Syntax.agda`：concrete 语法 | 上传稿要 abstract 语法 | v1 留在 concrete：搬运只做 fill / whole 两种，按声明名拼；abstract 换代是 v2 |
| 归档的 `Solve.agda`：规格 = 一句话 + 一条测试，历史在 Agda 列表里（OOM 的来源） | 规约 = 两个 stub；历史在行里；提示词 = Query | 重写成 `Node.agda` |
| `Replay.agda`：verify / wrap | Rebuilder = Agda 接口缓存 + "孩子规约文本没变就不重做" | 本稿只用后者；录音回放到 M5 |
| 子线顺序执行、子棋谱夹回父棋谱 | 孩子顺序跑（suspending）。"B 中途被杀"在顺序模型里退化成"B 的结果作废" | 并发等 Σ 加"未就绪" |
| `sh`、`eval`、`goals` / `give` / `split` | 节点的 Σ 里没有 | 留在 `AgdaSig`，`NodeSig` 不嵌入它们 |

## 二、对象、态射、判决

### 2.1 对象 = (实现 , 规约)，规约 = 两个 stub

```
 X.agda        stub：import（⊆ E₀）、data / record 的具体定义、postulate 的函数签名        父写
 X.Test.agda   stub：import X；postulate 的定理陈述（含 refl 型的 f 3 ≡ 6）                 父写
 X.agda        filled：stub 的签名 + 子句；可以多出私有辅助声明                               子 fill
 X.Test.agda   filled：陈述 + 证明                                                            子 fill
```

设计期的 Dialectica 退化成谓词纤维化：每个对象的"测试"只有一条，就是整个规约。张量 = 两个假设并排，没有交叉。

```
 对象   (U , P ⊆ U)         U = 满足 X.agda 签名的实现，P = 过 X.Test
 态射   f : U → V，P(u) ⟹ Q(f u)
 ⊗      (U × V , P ∧ Q)      A.Test 只谈 a，B.Test 只谈 b
```

### 2.2 三种态射，三种帧

```
 分解   A ⊗ B ──▶ root     root.agda import A B；root.Test import A.Test B.Test
                            在 E₀⁻ 里 check 全部通过  ⟺  ∀ a b. A.Test a → B.Test b → root.Test (root a b)
 解     1 ──▶ A            A.agda、A.Test.agda 填满，在 E₀（--safe）里通过
 反驳   A ──▶ ⊥            A.Refute.agda：import A、A.Test 两个 stub，audit 过（自身无 postulate），absurd : ⊥，在 E₀⁻ 通过
```

postulate 就是假设，`--safe` 就是"没有假设剩下"。反驳永远在 E₀⁻ 里查（它 import 的是 stub），所以它自己不能带 postulate，这一条由 `audit`（后端在 token 流上查黑名单）把守。

帧：节点的一生只用四种帧，都是 `Env.enter` 现有的样子。

```
 帧      flags   visible                     realm          用途
 节点帧  E₀⁻     E₀                          p              循环：ask、写行、开孩子
 沙箱帧  E₀⁻     E₀ ▸ 逐个 check 的模块      p（同）        洞阶段 / 解答 / 反驳的 check；leave 后全部忘掉
 孩子帧  E₀⁻     E₀                          p ++ "kids/K/" node 递归
 粘合帧  E₀      E₀ ▸ …                      p（同）        子树全部模块 --safe 重查

 栈的样子：      [(E₀⁻ , q , "root/")]
   enter 沙箱    [(E₀⁻ , 0 , "root/") , (E₀⁻ , q , "root/")]
   enter 孩子 A  [(E₀⁻ , qA , "root/kids/A/") , (E₀⁻ , q − qA , "root/")]
   enter 粘合    [(E₀ , 0 , "root/") , (E₀⁻ , q , "root/")]        E₀ ≼ E₀⁻ 成立：coinfective 只增
```

每次 check 都在沙箱帧里做，一组查完就 leave：后端的 TCState 回到进入前，同名模块下一轮可以重交。
这是 Solve 已经在用的括号纪律；本稿把它定成唯一的用法，节点帧自己从不 check。

### 2.3 复合 = 树

```
 A₁.Test ⊗ A₂.Test ──▶ A.Test           A 节点的分解
 A.Test  ⊗ B.Test  ──▶ root.Test        root 节点的分解
 ─────────────────────────────────────  复合
 A₁.Test ⊗ A₂.Test ⊗ B.Test ──▶ root.Test
```

叶子的规约合取蕴含根的规约，就是态射可复合；粘合 = 把 import 链按依赖序交给 Agda 重查一遍。

### 2.4 判决 = 一次 cut，是一行

```
 ⟨ 程序 ‖ 测试 ⟩  =  check X.Test 的 Verdict            verdict/n 行：过 / 没过 + 报错原文
 思维链           =  trace/n 行（ask 的提示词与答卷）    后端写
 笔记             =  memo/n 行                           程序写，about 就是前缀
```

记忆挂在节点上，不挂在实例上：换一个 LLM 实例续跑同一个节点，读同一个前缀。

## 三、Store 布局

一个任务一个目录（`store:DIR`），树的路径就是键的前缀。p 是节点的前缀，如 `root/` 或 `root/kids/A/`。

```
 键                       值                                            谁写        何时
 p spec/stub              X.agda 的 stub 文本                            父（enter 前）  分解时
 p spec/test              X.Test.agda 的 stub 文本                       父            同上
 p trace/n/prompt         第 n 次 ask 渲染出的提示词                     后端          ask
 p trace/n/reply          第 n 次 ask 的答卷原文（大的进 blob）           后端          ask
 p draft/n/<file>         答卷按 "-- file: <file>" 拆出的各个模块         后端          ask
 p code/X.agda            当前版本（fill / whole 的结果）                 transport     解答 / 改设计
 p code/X.Test.agda       同上                                           transport
 p code/X.Refute.agda     反驳                                           transport     反驳
 p verdict/n              第 n 次 check 的判决                            程序（set）    每次沙箱后
 p memo/n                 笔记：驳回摘要、改设计的理由、孩子的反驳键      程序（set）
 p result                 solved + 模块清单 / refuted + 键 / exhausted    程序（set）    leave 前
 p kids/K/…               孩子 K 的前缀                                   孩子
```

三条规矩：

- `set` 的类型前置条件 `prefixOf realm k`：孩子写不进父的前缀。父能写孩子的前缀（父的前缀是它的前缀），所以规约由父在 enter 前写进 `kids/K/spec/`。
- `code/` 下的行只有 `transport` 会写。`NodeSig` 里 `set` 的键由程序构造，第五节用一个小类型把它限制在 `verdict/`、`memo/`、`result/` 三类上。
- 读 = `get`，realm 外回 nothing。节点读 E₀ 和自己的前缀，没有别的。父不读孩子的行：孩子的结果是 `node` 的返回值；粘合时父 `get` 孩子的 `code/` 行只为交给 `check`，不交给 LLM。
- 根的 `root/spec/` 由人写：M2–M4 里是驱动程序 `main` 开局时从常量 `set` 进去；以后是 2.1 那几轮对话的产物。

## 四、一个节点的一生

状态机，箭头是程序的分支：

```
 规约在 p spec/ ──ask──▶ 答卷在 p draft/n/ ──分类──┬─ 解答   ──fill──▶ 沙箱 check ──过──▶ 粘合 ──过──▶ solved
                                                    ├─ 分解   ──写孩子规约、whole 根正文──▶ 洞阶段 check ──过──▶ 逐个 enter 孩子 node leave
                                                    │          全 solved ──▶ 粘合 ──过──▶ solved
                                                    │          有孩子 refuted / exhausted ──▶ 改设计（第 4.5 节）──▶ 回到洞阶段
                                                    └─ 反驳   ──audit、沙箱 check──过──▶ refuted
 任何一步没过 ──verdict、memo──▶ 下一轮 ask（配额 −1）；配额 0 ──▶ exhausted
```

类型：

```agda
record Spec : Type where                  -- 孩子的身份：模块名。stub 与 test 两段文本在 p spec/ 行里，父在 enter 前写
  field name : String

data Result : Type where
  solved    : List Key → Result           -- 子树全部模块的键，依赖序；全部在 E₀ 下 --safe 过
  refuted   : Key → Result                -- 反驳模块的键
  exhausted : Result                      -- 配额用完。不是判决；父节点决定加配额还是改设计

node : (d : ℕ) (p : Path) (sp : Spec) → Run NodeSig (λ _ → Result) (frame p)
```

`d` 是树深：孩子用 `d − 1`，`d = 0` 直接 `exhausted`。它只是终止性论证（Agda 要结构递减），预算仍是配额。

下面的伪代码用 `▷` 表示"拿到回应接着走"，真代码里每一步的索引（栈）是显式的，形状同 `DriveToy.chain`。

### 4.1 问一次：ask 与答卷

```
 提示词 = Query 的渲染           答卷 = 文件表
   lit  规则与输出格式             -- file: X.agda
   row  p spec/stub                …
   row  p spec/test                -- file: X.Test.agda
   last 2 (p verdict/)             …
   last 3 (p memo/)
```

```agda
data Item : Type where
  lit  : String → Item             -- 固定文字
  row  : Key → Item                -- 一行的值（规约、反驳的原文）
  last : ℕ → Key → Item            -- 某前缀下最近 n 行
Query = List Item

ask : Query → Op ;  Res (ask q) = List String       -- 后端：渲染 → 问 LLM → 写 trace/n/、draft/n/<file> → 回文件名
```

程序不持答卷。后面每一步要哪个文件就 `get (p draft/n/<file>)`，用完即弃。

### 4.2 解答一轮：fill、沙箱、粘合

```
 stub                 draft                   code（transport fill 的结果）
 data T …             f zero = …              data T …            ← 照 stub
 postulate f : T → T  f (suc n) = …     ⟹     f : T → T            ← 签名照 stub
                      helper = …              f zero = … ; f (suc n) = …   ← 子句照 draft
                                              private helper = …   ← 多出的声明追加
```

```agda
solve n files =
  move (transport fill (p "code/X.agda")      (p "spec/stub") (p draft n "X.agda"))      ▷ λ e₁ →
  move (transport fill (p "code/X.Test.agda") (p "spec/test") (p draft n "X.Test.agda")) ▷ λ e₂ →
  rejected? e₁ e₂ → verdict n …; loop n
  sandbox E₀⁻ [ p "code/X.agda" , p "code/X.Test.agda" ] ▷ λ where
    fail msg → verdict n msg ; loop n
    ok       → glue E₀ [ p "code/X.agda" , p "code/X.Test.agda" ] ▷ λ where
                 fail msg → verdict n msg ; loop n
                 ok       → set (p "result") "solved …" ; done (solved [ p "code/X.agda" , p "code/X.Test.agda" ])
```

`fill` 保证签名不被改：结果的签名取自 stub，答卷里的签名被忽略，子句对着 stub 的类型查。

沙箱与粘合是同一个函数，只差 flag：

```agda
sandbox fl keys = move (enter (header E₀-list fl) 0 p) ▷ λ _ → checkAll keys ▷ λ v → move leave ▷ λ _ → done v

checkAll []       = done ok
checkAll (k ∷ ks) = get k ▷ parse ▷ λ m → mkHeader (importsOf m) fl ▷ mkCode ▷ λ c → move (check c) ▷ λ where
                      fail path msg → done (fail msg)
                      ok i          → checkAll ks          -- 环境多了 m（▷），下一个模块可以 import 它
glue = sandbox E₀
```

`importsOf : Module → List ModName` 是 Syntax 上的十行函数：收顶层和 `Module′` 里的 `Import`。

### 4.3 分解一轮：写孩子的规约，洞阶段 check

答卷里 `X.agda` import 了 E₀ 之外的名字 K₁ … Kₙ，就是分解：答卷必须同时带 `K.agda`、`K.Test.agda` 两个 stub。

```
 root.agda ──import──▶ A.agda（stub）  B.agda（stub）
 root.Test ──import──▶ A.Test（stub）  B.Test（stub）
 沙箱 E₀⁻：按序 check [ A, A.Test, B, B.Test, root, root.Test ]
 过了  =  A.Test × B.Test × root ⊢ root.Test
```

```agda
design n files ks =
  forEach ks (λ K →
    move (transport whole (p kids K "spec/stub") (p draft n (K ".agda")))      ▷ λ _ →
    move (transport whole (p kids K "spec/test") (p draft n (K ".Test.agda"))) ▷ λ _ → …) ▷
  move (transport whole (p "code/X.agda")      (p draft n "X.agda"))                    ▷ λ _ →
  move (transport fill  (p "code/X.Test.agda") (p "spec/test") (p draft n "X.Test.agda")) ▷ λ _ →
  sandbox E₀⁻ (stubsOf ks ++ [ p "code/X.agda" , p "code/X.Test.agda" ]) ▷ λ where
    fail msg → verdict n msg ; loop n
    ok       → kids n ks []
```

两条说明。

- `root.Test` 在洞阶段可以**留着 postulate**：refl 型的测试对着 postulate 的 `A.f` 算不动，父节点要么用 `A.Test` 的陈述做等式推理把它证了，要么留到粘合。
  留下的 postulate 数就是"提前验证了多少"，写进 verdict 行；粘合时它必须填满（`--safe`）。
- `whole` 只用于 stub 和根正文；stub 的形状由后端核对：只许 import、data / record、`postulate` 块、注释。

孩子顺序跑，配额按孩子数均分：

```agda
kids n []       acc = glue E₀ (acc ++ [ p "code/X.agda" , p "code/X.Test.agda" ]) ▷ λ where
                        ok       → set (p "result") … ; done (solved (acc ++ …))
                        fail msg → redesign n (glueFailed msg)
kids n (K ∷ ks) acc =
  move (enter h₀ (quota ÷ |ks|+1) (p kids K)) ▷ λ _ →
  node (d − 1) (p kids K) (spec K) ▷ λ r →           -- 递归；孩子只看得见 E₀ 和自己的前缀
  move leave ▷ λ _ →
  case r of
    solved ms → kids n ks (acc ++ ms)
    refuted k → redesign n (kidRefuted K k)
    exhausted → redesign n (kidExhausted K)
```

`node` 对 `kids` 的递归落在栈上更深一层；树深 `d` 结构递减给终止性，配额给预算；程序仍是有限树。

### 4.4 反驳一轮

```
 X.agda（stub）  X.Test.agda（stub）  ──import──▶  X.Refute.agda ：absurd : ⊥
 audit：token 流里没有 postulate / primitive / macro / unquote / 除 OPTIONS 以外的 pragma
 沙箱 E₀⁻：check [ stub , test-stub , refute ]
```

```agda
refute n files =
  move (transport whole (p "code/X.Refute.agda") (p draft n "X.Refute.agda")) ▷ λ _ →
  move (audit (p "code/X.Refute.agda")) ▷ λ where
    false → verdict n "反驳里有 unsafe 的东西" ; loop n
    true  → sandbox E₀⁻ [ p "spec/stub" , p "spec/test" , p "code/X.Refute.agda" ] ▷ λ where
              fail msg → verdict n msg ; loop n
              ok       → set (p "result") "refuted …" ; done (refuted (p "code/X.Refute.agda"))
```

反驳是关于规约的定理，不是关于程序的，所以它是最耐久的一行：父节点改规约后，若新规约蕴含旧规约，旧反驳直接复合。
v1 不做这个复合，只把反驳的键放进父的 memo 和下一次 ask 的 Query。

### 4.5 改设计：搬运，而不是重写

孩子回来 refuted / exhausted，或粘合没过，父节点多一步记忆，然后问一次：

```
 Query：规则 + spec + 旧根正文（row p code/X.agda）+ 孩子 K 的反驳（row k）+ last memo
 答卷：新的 X.agda，以及每个仍要的孩子的 K.agda / K.Test.agda
```

```
 Code₁ ──M──▶ Code₂           v1 的 M 只有两种行：
   X.agda       whole            整个换
   kids/K/spec  keep | whole     文本逐字相等 = keep：孩子的 result 照用，不重跑
                                 不等 = whole：孩子的 result 作废，重新 node
   新孩子       whole            新开
   少了的孩子   drop             前缀留着（只追加），没有后继
```

```agda
redesign n why =
  set (p memo n) (show why) ▷
  move (ask (Query: rules ∷ row spec ∷ row (p "code/X.agda") ∷ rows-of why ∷ last 3 (p "memo/") ∷ [])) ▷ λ files →
  forEach (kidsIn files) (λ K →
    get (p kids K "spec/stub") ▷ λ old → get (p draft n (K ".agda")) ▷ λ new →
    if old ==ₛ new (and test likewise) then keep K else transport whole … ; markRedo K) ▷
  move (transport whole (p "code/X.agda") (p draft n "X.agda")) ▷ …
  sandbox E₀⁻ (全部 stub ++ 根) ▷ ok → kids n (redo-list) (kept-results) | fail → verdict ; loop n
```

"B 不受影响继续干"在顺序模型里就是 `keep`：B 的规约文本没变，B 的 `solved` 清单直接进粘合。
unit 级的 M（改名、拆分、闭包沿依赖传）等 Code 换到 abstract 语法再做；那时 `Export.deps` 已经在 `Iface` 里。

### 4.6 粘合

```
 kids/A/code/A₁.agda … kids/A/code/A.agda  kids/A/code/A.Test.agda   ← A 的 solved 清单（它自己已 --safe 过）
 kids/B/code/…                                                       ← B 的
 code/X.agda  code/X.Test.agda                                       ← 自己的
 粘合帧 E₀：按这个序 checkAll；Agda 的接口缓存让孩子那部分基本不重查
```

粘合帧有 `--safe`，所以：孩子若漏了 postulate 在这里被抓；根正文里藏的 unsafe 在这里被抓；留到粘合的测试必须填满。
过了就 `solved (清单)`，父节点拿清单继续它的粘合。

## 五、Σ：节点的工具注册表

节点程序写在 `NodeSig` 上，它是 `AgdaSig` 的子签名；嵌入是一个函数，后端照旧只跑 `AgdaSig`。

```
 NodeSig           Res                     说明
 ask q             List String             q : Query；答卷进 draft/
 get k             Maybe String            realm 外 nothing（现有）
 set k v           Unit                    k 限于 verdict/ memo/ result（小类型 Note 构造键）
 transport m t s d Maybe String            m : fill | whole；t 在 realm 内（类型）；nothing = 写好
 audit k           Bool                    token 黑名单
 parse s           Maybe Module            现有
 check c           Verdict                 现有
 enter h q p       Unit                    现有：只能更窄更穷
 leave             Unit                    现有
 log s             Unit                    现有
 没有：sh、eval、render、goals / give / split
```

```agda
data NodeOp : Ix → Type where … 上面十一个构造子 …
embed : NodeOp ix → Op ix                       -- 逐个构造子
embedRun : Run NodeSig A ix → Run AgdaSig A ix   -- move o k ↦ move (embed o) k
```

"禁止用别的方法改代码"不需要机制：`NodeSig` 里能写 `code/` 的只有 `transport`。

## 六、改动清单

### Agda 侧（Lojita）

| 文件 | 改动 |
| --- | --- |
| `src/Env.agda` | 键与 realm 改成路径 `Path = List String`（下面单说）；`Query`（`Item` 三个构造子）；`ask : Query → Op`，`Res = List String`；加 `transport : Move → Path → Path → Path → {isPrefix realm t} → Op`，`Res = Maybe String`；加 `audit : Path → Op`，`Res = Bool`；`next` 对两者不变环境。其余不动 |
| `src/Node.agda`（新） | `Spec`、`Result`、`Note`（可 set 的键）、`NodeSig` 与 `embed`、`importsOf`、`sandbox` / `checkAll` / `glue`、`classify`（答卷文件名 → 解答 / 分解 / 反驳）、`node` 主循环（第四节） |
| `src/ToyNode.agda`（新） | 脚本余模型跑一棵两层树：根分解出一个孩子，孩子 fill，粘合；再一局孩子反驳、根改设计。全 refl |
| `src/ToyEnv.agda` | `respS` 补 ask（回预置的文件名表）、transport（内存里 fill / whole 用脚本给的结果）、audit |
| `tests/neg/` | 加三个反例：`transport` 写 realm 外的键；`set` 写 `code/`（Note 造不出这个键）；孩子的 header 想看父的模块 |
| `src/DriveToy.agda` | 加 `fillOne`（真后端 fill 一个 stub）、`auditBad`（带 postulate 的反驳被拒）、`twoFlags`（E₀⁻ 帧里 check 带 postulate 的 stub 过，E₀ 帧里同一模块被拒） |
| `check.sh`、`neg.sh`、`drive.sh` | 加上面的文件 |

### 键改成路径：递归程序里的前置条件怎么给

现在 `set` / `enter` 的前置条件是 `Bool→Type (prefixOf (realmOf ix) k)`，要在类型检查时算成 `true`，所以"子实例里的键要写成字面量"。
`node` 是递归的，前缀 `p` 是变量，`prefixOf p (p ++ "memo/1")` 对着 `primStringAppend` 算不动，而且没有内建引理能证它。
改法：

```
 Path  = List String                    一段一个字符串；realm 也是 Path
 isPrefix : Path → Path → Bool          逐段 =ₛ
 prefix-++ : ∀ p s → isPrefix p (p ++ s) ≡ true        对 p 归纳，十行
 ≤ᵇ-refl   : ∀ q → q ≤ᵇ q ≡ true                        enter 把剩余配额整个给孩子时用；均分要 ÷-≤
 set k v {subst Bool→Type (sym (prefix-++ p s)) tt}     递归程序显式给证明；字面量键照旧自动算出
```

后端只多一个 join：realm 每段后加 `/`（`"a/"`），键段间用 `/`（`"a/x"`），日志、`fold.py`、`store.sh` 不变。
现有 `StoreToy` / `ToyEnv` 的键从 `"a/x"` 改成 `"a" ∷ "x" ∷ []`，机械改。

### 后端（agda-backend，v8）

| 处 | 改动 |
| --- | --- |
| `ask` | 参数是 `Query` 值：`lit` 原样、`row k` 取值、`last n k` 取前缀 k 下行号最大的 n 行（Map 上一次范围查询）；拼成提示词；`ask:http` 等处理函数不变；回复写 `trace/<step>/prompt`、`trace/<step>/reply`；按行首 `-- file: NAME` 拆成 `draft/<step>/NAME`；回 `VList` 文件名。realm 取当前帧 |
| `transport` | 读三个键的文本，`parseModuleText`；`whole`：核对答卷是一个模块，就写；`fill`：按声明名把 stub 里 `Postulate` 块的每条 `TypeSig` 换成答卷里同名的 `TypeSig + FunClause`，缺一条回 `just "unfilled: f"`，答卷多出的声明追加在后；`prettyModule` 写回。约 150 行 |
| `audit` | `tokensParser` 取 token 流，黑名单：关键字 `postulate` `primitive` `macro` `tactic` `unquote` `unquoteDecl` `unquoteDef` `unquoteData`，任何非 `OPTIONS` 的 pragma；回 `VBool`。前提：E₀ 里只有 `--safe` 的模块（cubical 库全是），`Agda.Builtin.TrustMe` 之类不进 E₀，否则反驳能借它作弊 |
| stub 形状 | `transport whole` 到 `spec/` 下的键时核对：顶层只有 Import / Open / Data / Record / Postulate / Comment / OptionsPragma |
| 接口缓存 | 沙箱帧（flags 无 `--safe`）里 check 不写接口文件（`withCleanOptions … False`），粘合帧写。避免同名模块在两种 flag 下的缓存互相触发重查 |
| `get` / `set` / `enter` | 键与 realm 从 Agda 来的是 `List String`，join 后照旧 |
| 不动 | `check`、`leave`、`store:DIR`、`Code.hs`、生成器 |

## 七、根与 IO：同一程序，两个余模型

根是唯一碰 IO 的节点，但它不是别的东西，就是一个 `Run AgdaSig` 程序。外部服务（时钟、LLM、网络）就是 `ask` / `get` / `set` / `sh` 这些步。

```
 root.agda        main : Run AgdaSig A ix₀                        纯数据：一棵有限树
 root.Test.agda   mock : Comodel AgdaSig W（脚本，ToyEnv 的样子）
                  t : fst (snd (Play.play mock main w₀)) ≡ expected ; t = refl
 部署             agda --cubical-drive=main --cubical-handler=ask:http:… --cubical-handler=store:DIR
```

这是 Game / Later 已经有的"同一程序、两种解释"。根的 E₀ 因此包含 `Later`、`Env`（以及它们的依赖）。
第一个微服务之前的里程碑用纯函数做根，根与孩子没有区别。

脑手分离。权限和资源一直没出现，因为它们不住在 Agda 封闭世界里：Agda 只有 IO 一个窗口，窗口就是签名 Σ。
窗口上面是脑，`Run Σ` 程序，形式验证在这里做；窗口下面是手，余模型，真实操作在这里发生。
树上任何一枝都不另开窗口：孩子是纯包，只有根碰 Σ。资源与权限落在窗口下面的两处，都在开工前定死：

```
 窗口上（脑，Agda）      Σ 里带的只有配额与 realm 两个数：enter 只能更穷更窄（类型）
 窗口下（手，后端）      handler 表 --cubical-handler=…：开工前配好，跑起来不换
 唯一的假设              Honest：手每答一步都是 Σ 允许的一步。soundHonest 把它变成"整局合法"
```

两个微服务通讯 = 一对对偶的协议：同一个签名，一边当模型（发 move），一边当余模型（答 resp）。
验证时把对方写成脚本余模型（mock），两半在 Agda 里 cut 成一个封闭程序，refl 查；部署时手换成真网络。
协议的签名放在 E₀，两棵树共用；改协议 = 两棵树同时需求变化。只要把真实世界建成的范畴（Σ 加 Honest）没错，
真实操作就被同一条定理覆盖；错了也只错在这一个假设上，不会散在树上。

## 八、分期与验收

| 里程碑 | 做什么 | 验收 |
| --- | --- | --- |
| M0 Agda 侧 | `Env`：路径键、`Query`、`transport`、`audit`；两条引理；`Node.agda`；`ToyNode.agda`；三个反例；`StoreToy` / `ToyEnv` 键改路径 | `./check.sh` 全过；ToyNode 两局全 refl；`./neg.sh` 十个反例全被拒；`./store.sh` F 组照过 |
| M1 后端 v8 | 路径 join、`ask` 渲染与拆文件、`transport`、`audit`、沙箱不写接口 | `./drive.sh` 加三个程序全过；`fill` 后 `eval twice 3` 得 6；带 postulate 的反驳被 `audit` 拒；同一 stub 在 E₀⁻ 过、在 E₀ 被 CoInfective / postulate 拒 |
| M2 单节点 | 任务一重做：规约 = `twice` 的 stub + `test : twice 3 ≡ 6` 的 stub；真 LLM | 10 局 ≥ 9 局 solved；`runs/` 里每局 `trace/` `draft/` `verdict/` `result` 齐全；进程 RSS 平直 |
| M3 两层树 | 根的 stub 签名用到一个孩子（如 `pow` 要 `mul`）；真 LLM 分解；孩子 fill；粘合 | 一局 solved，模块清单含 `kids/mul/code/*`；洞阶段的 verdict 行记着留了几个 postulate |
| M3′ 反驳 | 故意矛盾的孩子规约（`f 0 ≡ 1` 与 `f 0 ≡ 2`） | 孩子回 refuted；根的 memo 多一行；根改设计后 solved |
| M4 keep | 根有两个孩子，一个被反驳 | 另一个孩子的 `spec/` 文本未变，它没有被重新 enter（trace 里没有它的新行），粘合用了它的旧清单 |
| M5 之后 | Rebuilder 读 Store 行（`Replay.wrap` 的录音 = `trace/`）；Σ 加"未就绪"做并发孩子；Code 换 abstract 语法，unit 级 M | 另开计划 |

顺序：M0 → M1 → M2 → M3 → M3′ → M4。M2 之前不接真 LLM。

## 九、待拍板

1. `Query` 第一版只有 `lit` / `row` / `last n`：够不够。
2. 答卷分文件的标记行：`-- file: NAME`（是合法的 Agda 注释，单文件答卷不写也行）。
3. `transport` v1 只有 `fill` 与 `whole`；unit 级的 M 等 abstract 语法。
4. `exhausted` 作为 `Result` 的第三个构造子：它是程序的结局不是判决，但有限程序必须有它。
5. 洞阶段 `root.Test` 允许留 postulate 到粘合：留多少由 LLM 决定，verdict 行记录。
6. 根的 mock 到 M5 之后再做；M2–M4 的根是纯函数。

## 附：符号

```
 E₀      任务的语境：包的名单 + flag（含 --safe）。任务中不变
 E₀⁻     E₀ 去掉 --safe；节点帧、沙箱帧、孩子帧的 flag
 p       节点前缀（Path），如 root/kids/A/；也是它的 realm
 stub    只有签名的模块：data / record 具体，函数 postulate
 fill    搬运：stub 的签名 + 答卷的子句
 whole   搬运：整个换
 沙箱    enter 同前缀、零配额、E₀⁻ 的帧，check 完 leave
 粘合    enter 同前缀、零配额、E₀ 的帧，按依赖序 check 子树全部模块
 verdict 一次 check 的判决行；memo 笔记行；trace 提示词与答卷；draft 答卷拆出的文件
 Result  solved 清单 / refuted 键 / exhausted
```
