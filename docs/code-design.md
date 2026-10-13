# Code 类型与反射工具 v6：设计稿（2026-10-13，未动手）

接续 `docs/code-plan.md`（七条已定）与 `archive/2026-10-13-code-v5/README.md`（上一版为什么归档）。
本页把方案想到能动手的程度：Code 怎么生成、环境与 ▷ 怎么写、签名有哪些步、后端接在 agda 的哪几个入口、子实例怎么开、先做什么。
标「定」的是 code-plan 已定的；标「议」的要用户拍板。本页只是设计，`src/` 一字未动。

## 一句话

Code 是 parser 吐出来的那棵树，用脚本从 Agda 源码里的 Haskell 类型生成，糖和 unsafe 都在；
环境 E = 已检查模块的接口表 × flag（语境 × 余语境），`Code E` 由 E 算出（归纳–递归，只管模块边界）；
一拍走一步 `check m`，回应带回接口，下一拍才进 E（▷）；
余模型是 `agda` 进程自己：归约到 `move (check m) k` 时真的调 createInterface，把接口喂给 k。
和用户的 IO 例子同一个形状：IOSig 换成 AgdaSig，Haskell 那边的"真的去问 LLM"换成"真的去调 Agda 自己的入口"。

## ① 全景：三层、两种签名、一个余模型

```
 代理层   Harness.agda    Free (Sig-of x) R       ask / run / sub                        （v1，一字不改）
              │ drive：纯 Agda 的解释器子句   ask → ask    run t c → eval    sub → enter … leave
              ▼
 后端层   Later.agda      Run AgdaSig A E         quote / check / eval / enter / leave / ask / readF …
              │ 归约到 move o k                   索引 = 环境 E（Later 的 Ix；开子实例时是环境栈）
              ▼
 进程     agda-cubical-run（Haskell）   resp : W E → (o : Op E) → Σ r. W (next o r)
              ├ check   → Imports.getInterface（createInterfaceIsolated）   同一进程的 TCState 多一个模块
              ├ eval    → 临时模块按主模块模式在分支状态里检查 + normalise + reify   规范形仍是语法
              ├ quote   → Parser.parseFile moduleParser（withComments 的 token 流取注释）
              ├ goals / give / refine / case → BasicOps / MakeCase                （编辑器，第二阶段）
              └ ask / readF / writeF / log → 运行前配好的处理函数表                 （世界边界，没有 shell）
```

- `IO = Free IOSig` ↔ `Run AgdaSig A E`；`drive : Free (Sig-of x) R → IO (R × 棋谱)` ↔ 这里的 `drive`；"余模型住在 Haskell 里" ↔ 那 330 行再加一段。
- 代码 + 后端 = 完整的程序：反射（check / eval）和 cubical 的搬运（eval 里的 transp）都在同一个进程、同一个 TCState 里算，类型带着跑（code-plan 第 7 条）。
- 启动参数是唯一在 Agda 世界之外配的东西：`agda-cubical-run --cubical-drive=main --handler=ask:https://… --handler=fs:/dir Main.agda`。启动之后每一步都是 Agda 程序的 move。

## ② Code：从 Agda 源码生成

**载体。** `Agda.Syntax.Concrete`（Module、Declaration 37 个构造子、Expr 45、Pattern 17、Pragma 24、LHS / RHS / WhereClause / LamClause / DoStmt / Binder / TypedBinding / LamBinding / ModuleApplication / RecordDirective / ImportDirective 一族）、`Concrete.Name`（Name / QName / NamePart）、`Syntax.Common` 的修饰（ArgInfo = Hiding × Modality（Relevance、Quantity、Cohesion、Polarity）× Origin …、Access、IsInstance、Erased、Induction、TerminationCheck、PositivityCheck、Catchall、Fixity、Notation …）、`Literal`。约 70 个类型、250 个构造子。
`Agda.Syntax.Internal.Term`（Var / Lam / Def / Con / Pi / Sort / MetaV …）只在后端内部出现：它是检查器的树，带 de Bruijn；v2–v4 照它画就是"项的反射"。

**生成器**（Haskell，放在后端里，约 500 行）。给这些类型加 `deriving instance Generic`，用 GHC.Generics 的元数据（类型名、构造子名、字段类型）走一遍，吐出三样：
1. `src/Code.agda`：一个 mutual 块里的 data，名字照抄，`--safe --cubical` 下检查通过（都是严格正的语法树，List / Maybe 嵌套没问题）；
2. `encode : a → Term`、`decode : Term → TCM a`：两个方向由同一个 Rep 导出，一致性由构造保证；
3. flag 表：从 `Interaction.Options.Base.infectiveCoinfectiveOptions` 抄出（flag 名，infective | coinfective），给 Agda 侧的 `≼` 用。

**原子**（手写的几条翻译）：Range / KwRange 丢掉；Text / RawName → String；Integer → ℤ；Word64 → ℕ；Double → Float；Char；List1 / List2 → 非空表；Maybe / Either / 积 → cubical 库的；`NoName` 的 NameId → decode 时 `fresh`。

**范围：parser 像里的构造子。** 确定只在 parser 之后才出现的不进 Code：`OpApp`、`OpAppP`（算子解析在 scope checker 里做，parser 只给 `RawApp` / `RawAppP`）、`KnownIdent`、`KnownOpApp`、`Highlighted`（高亮）、`Generalized`、`DontCare`、`LitMeta`。其余全留：`Postulate`、`Primitive`、`UnquoteDecl`、`Pragma (OptionsPragma …)`、`TERMINATING`、`NO_POSITIVITY_CHECK` 这些 unsafe 的也在。哪些构造子真的会从 parser 出来，由回环测试说了算。

**注释。** parser 丢，lexer 的 token 流留着（`TokComment`，`parseFile` 开 `withComments`）。加一个构造子 `Comment : String → Declaration`：`quote` 按位置把注释插进声明序列，`decode` 丢掉它。编辑器要的"代码与注释的关系"就是树上的相邻。（议）

**错误位置。** decode 时按先序给每个节点一个号，号写进假 Range 的行号；Agda 报错带 Range，后端查表换回树上的路径 `Path = List ℕ`。`fail` 带（路径，报错原文，规范文本）。规范文本用 `Concrete.Pretty` 打印，一并喂给 LLM。这就是 code-plan §⑦ 说的"B 的好处另外补"。

**回环测试。** cubical 库 + Lojita 每个文件：parse → encode → decode → pretty → parse，两棵树相等（范围除外）。后端自带 `--cubical-roundtrip=FILE`，Agda 版本一变先跑它。

## ③ 环境与 Code E：归纳–递归在模块这一级

```agda
mutual
  data Env : Type
  visible : Env → List ModName                   -- 语境：能 import 谁
  exports : Env → ModName → List String          -- 它们各导出什么名

  data Env where
    base : List Iface → Flags → Env              -- 父给的库与模式
    _▸_  : (E : Env) → Checked E → Env           -- 过了检查的模块，下一拍才在这

  record Checked (E : Env) : Type where
    field m : Code E ; i : Iface

  Code : Env → Type
  Code E = Σ[ m ∈ Module ] Bool→Type (okᵇ m E)
    -- okᵇ：imports m ⊆ visible E，using 的名 ⊆ exports，options m ≼ flags E；三条都可判定
```

- `Module` 是 ② 生成的平的树。`Code E` 只在模块边界上看 E：import 谁、用谁的名、开什么 flag。声明内部的名字交给 Agda 的 scope checker，不在类型里重做。v5 把名字做进类型（层号），是把 scope checker 重写了一遍，走回"项的反射"。
- `okᵇ` 算出来，所以 `Code E` 的证明是隐式的 `tt`，写不出来就是编译错误，和 v5 的 `#` 一个技巧。
- Env 用 `Code E`，`Code E` 用 `visible E` / `exports E`，它们对 Env 递归：这就是归纳–递归，和 v5 的 `Env / Decl / count` 同一个形状，只是粒度从声明换成模块。
- `Iface`（后端算，作为数据带回，Agda 不查）：模块名、导出名及其类型（类型是 Expr，仍是 Code，给 LLM 看提示词也用它）、用的 flag、`iFullHash`。
- `Flags`：flag 名的表。`≼`：infective 的只能少（子开不了父没开的 `--cubical` / `--guardedness` / `--rewriting` …），coinfective 的只能多（父有 `--safe` / `--without-K` 子关不掉）。两面合起来就是"只降不升"。表从 Agda 源码生成（②）。这是**策略**（类型里的粗粒度）；Agda import 时的 InfectiveImport / CoInfectiveImport 是**机制**（精确），两道都在。
- 符号：环境 E、签名 Σ、不用 Γ（定）。

## ④ 签名 AgdaSig : TSig Ix（Later.agda 一字不改）

索引 `Ix = Env`；开子实例时换成栈 `List Env`，步都作用在栈顶（⑥）。

| 步 | 回应 | next | 后端做什么 |
| --- | --- | --- | --- |
| `quote s` | `Maybe Module` | E | parser；注释挂上。文本从 LLM 来 |
| `check m`，m : Code E | `ok Iface ∣ fail (Path × String × String)` | ok → `E ▸ (m , i)`；fail → E | 隔离检查；成功登记，失败回滚 |
| `eval h e`，h : Header E，e : Expr | `ok Expr ∣ fail …` | E | 临时模块 `open import …; it = e`，主模块模式在分支状态里检查，normalise it，reify 回 concrete |
| `enter h` / `leave r` | Unit / Unit | 压栈 `child E h` / 弹栈 | TCState 分支与配额账（⑥） |
| `ask p`、`readF`、`writeF`、`log` | String … | E | 运行前配好的处理函数；没配的步 = 卡住，整局失败 |
| `goals m`、`give`、`refine`、`case` | 目标表 / Expr / 子句表 | E | BasicOps.getGoals / give / MakeCase.makeCase（第二阶段） |

- ▷ 在 `check`：`k : (r : Res (check m)) → Run … (next (check m) r)`。判 ok 的分支里 `visible` 多了 m，才能 import 它；判 fail 的分支里写不出来。"新模块下一拍才能用"是类型说的。
- `eval` 的结果是语法（规范形 reify 回 concrete），所以"值是数据"闭合了一圈：文本 → quote → 树 → check → 控制 → eval → 树。要类型化的值，在 Agda 里写 `decode : Expr → Maybe (El u)`，一阶的 U 像 v5 那样；解码器是纯 Agda 函数，LLM 写不了假的。
- 没有 v5 的 `call`：工具就是被 check 过的模块里的函数，`eval` 就是调用。
- 没有 `--guarded`：程序仍是有限树，和 Game / Later 一样。

## ⑤ 后端：接在 agda 的哪几个入口（只接通）

| 要做的 | 用 Agda 已有的 | 自己写的 |
| --- | --- | --- |
| 驱动循环 | v5 的 driveLoop / respond：reduce 到 WHNF，认 done / move，按步的构造子名分派，apply 续体 | 搬过来，分派改成查表 |
| quote | `Syntax.Parser.parseFile moduleParser`，`withComments` 的 `tokensParser` | encode、注释插入 |
| check | 造 `Source`（srcText = 规范文本，srcOrigin = `srcFromPath` 登记的虚拟路径，srcModule = decode 出的树，srcAttributes 从树重算），调 `Imports.getInterface x NotMainInterface (Just src)` | decode、Path 表、算 Iface（`iInsideScope` 的公开名 + reify 类型）、`getTC` / `putTC` 兜底回滚 |
| eval | 临时模块按 check 走，但 `MainInterface TypeCheck` + `localTCState`；然后 v2 的 `runtimeNormalise`（record 先 eta）+ `reify` + `abstractToConcrete` | 临时模块的拼装 |
| enter / leave | `getTC` 快照压栈 / `putTC` 弹栈 | 配额账 |
| ask 等 | 处理函数表：构造子名 ↦ `Term → TCM Term`，启动参数给定 | LLM 的 HTTPS 客户端（Haskell 库，不开子进程）（议） |
| 编辑器 | `BasicOps.getGoals / typeOfMeta / contextOfMeta / give / introTactic / metaHelperType`，`MakeCase.makeCase` | 结果 reify 回 Code；树上的替换在 Agda 里做 |

不写的：检查器、求值器、scope checker、名字表（v5 的层号表没了，名字是字符串，Agda 自己查）。
估算：生成器 + 编解码 500 行，循环 150（搬），check / eval / enter / leave 300，处理函数 100 + HTTP，编辑器 200；Code.agda 生成约 700 行。

核对过的几处（Agda 2.9.0 源码，`/root/agda-backend/agda-source`）：
- `getInterface` 拿到 `Just src` 时自己登记 ModuleToSource，不调 findFile；非主模块不调 checkModuleName。所以虚拟模块不需要磁盘文件，只要 `srcFromPath` 给个 id。
- 成功后 `storeDecodedModule` + `visitModule` 是它自己做的；后面别的模块 import 它走 "Already visited"，不找文件。失败在 `createInterfaceIsolated` 的 `freshTCM` 里，不污染主状态。
- `iFullHash = hash(srcText) ⊕ 各 import 的哈希`：规范文本相同指纹就相同，这就是 Rebuilder 比的那个数。
- `.agdai` 写盘由 `--no-write-interfaces` 关掉。
- `BasicOps.give / getGoals / typeOfMeta / contextOfMeta`、`MakeCase.makeCase`、`Parser.parseFile`、`parseKeepComments` 都在，签名见上表。

## ⑥ 子实例：括号，不是嵌套（议）

两种写法：
- **A 嵌套**：`sub h p` 的步里带着子程序 p（数据），回应夹着子棋谱，像 Harness v1 的 `sub`。麻烦：`Res` 要提到同一个签名的 `Trace`，定义绕圈，得加燃料或改成归纳族；后端要递归开循环。
- **B 括号**：`enter h` 压栈、`leave` 弹栈，索引 `Ix = List Env`，子程序就是续体。一个循环；棋谱是平的，括号配对后得到 Harness 的树形棋谱（一个 fold，纯 Agda）。two-laters 那篇说的"账本 = 成对括号"就是它。

建议 B。
`Header E = (imports ⊆ visible E) × (flags ≼ flags E) × (配额 ≤ 父的)`；`child E h = base (h 选中的接口) (flags h)`。
父开子的自由度只有这三个坐标，且只降不升，由类型给（code-plan §⑤）。配额不是 Agda 语法，仍走 Harness 的 X / enter / leave，后端记账。
子实例在自己的栈顶 check 的模块，`leave` 后对父不可见；父要用，自己再 check 一遍（指纹相同）。这就是"子实例对父是一个点"。
`drive` 把 Harness 的 `sub k sp` 翻成 `enter h ; drive (kids st k) sp ; leave`。

## ⑦ 受限的 Code（定 + 议）

一个范畴 = 一个 module，公理在参数里（定）。
受限的 Code 不必是 Code：任何类型 D 配一个 `⟦_⟧ : D → Code E` 就行，约束写在 D 的类型里，`⟦_⟧` 的像落在 `Code E` 由类型保证。
开子实例的 `Header E` 就是第一个 D：三个坐标，翻成子模块的头两行加一个数。编辑器的"结构 / 实现"投影、数据库的"声明表"都是这种 D。

## ⑧ 编辑器与数据库的铺垫

- 洞 = `QuestionMark`；程序层的洞 = `f = ?`（Agda 自己的）。
- 结构 = TypeSig / DataSig / RecordSig，实现 = 子句 / 构造子 / 字段：同一棵树的两个投影（纯 Agda 函数）。
- 编辑器一步 = BasicOps 的一条命令：`goals` 给目标与类型，`give` 查一个 Expr，`case` 给子句；树上的替换在 Agda 里做，下一拍 `check`。
- 数据库：键 = (模块，声明名)，值 = 哈希 + 类型（Expr）+ 依赖；依赖由后端从检查后的内部项里收 `Def q`（第二阶段）；模块级的 `iFullHash` 第一阶段就有，Rebuilder 先比它。

## ⑨ 验收

- 回环：cubical 库 + Lojita 全部文件。
- 反例：v5 的四个（类型错、不停机、负性、未定义名）+ 新的四个：import 看不见的模块（Agda 编译错）、子开父没开的 flag（编译错）、`--safe` 模块 import 有 postulate 的模块（后端 fail，CoInfectiveImport）、`using` 了不存在的导出名（编译错）。
- 玩具：quote 一段文本 → check → eval 里面的函数（含一次 transport）→ enter 一个窄的子实例 → 子实例想 check 一个 import 父才看得见的模块 → 写不出来。

## ⑩ 顺序（议）

1. 生成器 → Code.agda + 编解码 + 回环（最大、最机械，最早暴露 Agda 版本的坑）。
2. Agda 侧：Env / Code E / Header / AgdaSig + 脚本余模型玩具（全 refl）。
3. 后端：循环 + quote / check / eval。
4. enter / leave + 处理函数表（LLM）。
5. 编辑器步、声明级依赖与哈希、注释。

## 待拍板

1. 子实例用括号（B）还是嵌套（A）。建议 B。
2. `leave` 只带回报告与棋谱，子实例的模块不带回。
3. 注释做成声明序列里的一个节点 `Comment`。
4. 第一版外部处理函数：ask（LLM）、readF、writeF、log；LLM 走 Haskell 的 HTTPS 库，不开子进程。
5. `Flags` 用 flag 名表 + 生成的 infective / coinfective 表，`≼` 按表算。

## 留白

- `Discrete Module`（录音回放按语法对位要它）：生成器顺手生成，或先只比指纹。
- 声明级依赖与哈希（数据库的键）：第二阶段。
- 并发的子实例：另开进程，v2 的 export / import 包过边界；第一版子实例顺序跑。
- `drive` 的正确性：平棋谱括号配对 ≡ Harness 的树形棋谱，等 drive 写出来再证。

## 实施记录（2026-10-13，同一天）

五条待拍板全部照建议定下，按 ⑩ 的顺序做到第 4 步：

| 步 | 做了什么 | 在哪 |
| --- | --- | --- |
| 1 生成器 | `Code.hs`（GHC.Generics 走树器）+ `agda-code-gen`：生成 `Syntax.agda`（74 类型 264 构造子，`--safe --cubical` 0.3 s 过）、`FlagTable.agda`；回环 1990 个文件通过 | 后端 `src/full/Agda/TypeChecking/Primitive/Cubical/Code.hs`、`src/code-gen/Main.hs`；Lojita `src/Syntax.agda`、`src/FlagTable.agda` |
| 2 Agda 侧 | `Env.agda`：Env / visible / flagsOf / Header / Code 一个归纳–递归块；栈 `Ix = Frame × List Frame`；`AgdaSig`；`mkHeader / mkCode` 运行时判定。`ToyEnv.agda` 脚本余模型全 refl；`tests/neg` 五个反例 | Lojita `src/Env.agda`、`src/ToyEnv.agda`、`neg.sh` |
| 3 后端 | `Drive.hs`：循环 + parse / check / eval / render；check 走 `getNonMainModuleInfo`，报错带树上的路径；eval 走临时模块 + normalise + reify + deOp | 后端 `Drive.hs`、`Runtime.hs` 两个选项；二进制 `agda-cubical-run.v6` |
| 4 子实例与世界 | enter / leave = TCState 快照栈；ask 四种处理函数（fixed / script / mailbox / http）、readF / writeF 限目录、log | 同上；`drive.sh` 七个程序 |
| 5 编辑器步、注释、声明级依赖 | `goals / give / split` 三个步接 BasicOps 与 MakeCase，洞的路径来自合成范围；注释从 token 流挂成 `Comment` 节点，解码跳过它但保留下标；`Iface` 的导出表每行带依赖（namesIn）与声明级哈希。`ask:http` 用 DeepSeek Flash 真跑通 | 后端 `Drive.hs`；Lojita `src/Env.agda`（Goal / Goals / Edit / Export）、`src/DriveToy.agda` §7–§8 |

和设计稿不同的几处：
- 生成的语法模块叫 `Syntax`（`Code E` 留给 Env 里的记录，两者同名会撞）；`quote` 改名 `parse`（`quote` 是 Agda 关键字）。
- import 列表放在头里由后端核对实际 ⊆ 声明，Agda 侧不生成遍历函数（§③ 的 `okᵇ` 只看头、模块名和顶上的 OPTIONS）。
- 配额进了栈的每一层（`Frame = Env × ℕ`），`ask` 扣一，`enter` 把一份给子。
- `leave` 用隐式证明 `hasParent ix` 而不是索引 `(F , G ∷ rest)`：后者在 Cubical Agda 里有不支持的索引匹配警告。
- 主文件的 OPTIONS 会被 Agda 记进持久选项；驱动器在 check / eval 期间清回默认，`base` 的 flag 才是唯一策略。
- `Generalized` 是 parser 会产出的（类型签名的类型外面套一层），保留；`DontCare` 排除。
- 回环测试的"忠实"定义：parse → toV → fromV → toV 恒等，外加 parser 用到的构造子都在 Syntax 里；pretty → parse 不作为判据（Agda 的打印器不保证可重解析），规范文本只用来算指纹。
- 编辑器的树上替换先放在后端（give / split 直接回 `edited 新树`），Agda 侧下一拍 check 它；设计稿里说"替换在 Agda 里做"，等 Syntax 有了可判定相等再搬过去核对。
- 还没做：Syntax 的可判定相等（录音回放）；`render` 不打注释。
