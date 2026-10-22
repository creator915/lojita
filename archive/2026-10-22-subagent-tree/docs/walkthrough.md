# 用 Agda 造出 Harness 的范畴：四个文件逐段讲解

2026-10-11

## 1 总图：先看一眼

整个范畴 = 沿配置铺开的一族范畴。底是配置树（规则书），每个配置 x 上面一个纤维 Fiber x：对象是棋盘，箭头是在 x 下合法的棋谱。纤维里住着一个程序（策略）和一组对手（预言机 × 世界 × 子 harness）；智能全在对手那一侧，范畴只说什么合法。

```
 编排层   配置树（底）       x ──▽ kid k──▶ x_子 ──▽──▶ …     树；本次不造它的范畴
                             │                │
                             │ Fiber x        │ Fiber x_子
                             ▼                ▼
 代理层   纤维（范畴）   棋盘 b ──棋谱 ask/run/sub──▶ 棋盘 b′     对象 = Board，箭头 = 合法棋谱
                             │ 一步 run
                             ▼
 对象层   事务范畴 Trans  棋盘 b ──世界的一列步──▶ 棋盘 b′         工具 = 这一层的程序
```

塔的规律：上层的一步 = 下层的一整条箭头。编排层开一条子线 ▽ = 子纤维里跑完一局；代理层的一步 run = 对象层的一条事务路径。想法 9 的「上层的状态是下层的环境」在这里：x 是编排层的状态、代理层的环境（它决定 Fiber x）。

| 文件 | 管什么 | 项目里的词 |
| --- | --- | --- |
| Game.agda | 签名 → 程序、对手、棋谱、跑一局 | 想法 6 的 model–comodel；「日志由签名导出」 |
| PathCat.agda | 机器（棋规）→ 范畴（合法棋谱） | 「范畴说什么合法」；一次构造，三层各用一次 |
| Harness.agda | 配置树、三类步、纤维、对手族、定理 sound、局面与产品、反射点 | 三层塔；decisions 1–3；想法 5、9 |

怎么读：每段代码不超过 12 行，后面回答三个问题——它为什么在这、它说什么、它对应项目里哪个词。符号只有四个：`Σ[ x ∈ A ] B` 是「配对，第二件依赖第一件」，`≡` 是相等，`→` 是函数，`×` 是普通配对。Agda 关键词三个：`record` 一包字段，`data` 几种构造子，`module` 一章（可以带参数）。

三个文件都开着 `--safe --cubical`，没有一个 postulate：每个未知量（预言机、世界、数据库）都是 module 的参数。所以文件里的每条定理都是「对任何预言机、任何世界」的全称命题。

## 2 Game.agda：一局棋的三件套（60 行）

这个文件只做一件事：把规则、程序、对手三样东西的形状定下来，再说明三样碰面会跑出什么。全文件已通过 `--safe --cubical` 的类型检查。

### 2.1 签名 Sig（第 17–21 行）

```agda
record Sig : Type₁ where
  field
    Op  : Type           -- 能走的步，参数已经带在里面
    Res : Op → Type      -- 走了这步之后能收到的回应
open Sig public
```

```
   Op ──Res──▶ Type        一步 o ↦ 它的回应类型 Res o
```

为什么在这：规则书的内容只有两件事——能做什么，做了会得到什么类型的回应。

它说什么：一包两个字段。`Op` 是步，`Res` 给每一步配一个回应类型。`open … public` 让后面可以直接写 `Op S`、`Res S o`。

项目里的词：dev-order-draft 的 Σ = {ask, run}。签名是一切的起点：日志、程序都从它导出。

### 2.2 程序 Free（第 27–34 行）

```agda
data Free (S : Sig) (A : Type) : Type where
  done : A → Free S A
  move : (o : Op S) → (Res S o → Free S A) → Free S A
```

```
          move o₁
         /   |   \         每个分叉 = 对手的一种可能回应
      done  move o₂ …
             /  \
          done  done
```

为什么在这：程序 = 策略 = 「下一步走什么，每种回应之后怎么接」。

它说什么：一棵树。叶子 `done a` 交出结果；节点 `move o k` 走一步 o，`k` 对每个回应给出子树。树是有限的，所以每条路必到 `done`：停机由形状保证，续命 = 再开一局（预算、停机谓词留到 S1）。紧接着的 `_>>=_` 把两棵树接起来：先跑完第一棵，用它的结果开始第二棵；三条单子律留到 S0。

项目里的词：「自由模型里的项」。想法 1 在这里的样子是：程序是一份数据（一棵树），不是一段会跑的代码。

### 2.3 棋谱 Trace（第 38–42 行）

```agda
Step  S = Σ[ o ∈ Op S ] Res S o     -- 一步的记录 = (走了什么 , 收到什么)
Trace S = List (Step S)             -- 棋谱 = 一列记录
```

为什么在这：日志是唯一真相，但日志的类型不是手写的，是签名的推论。

它说什么：一条记录是依赖对——先记步 o，再记类型为 `Res o` 的回应。棋谱是这些记录的列表。

项目里的词：two-schedulers 的「日志文法」、dev-order-draft 的「日志由签名导出」。DSH 手写事件文法，付了 4 个迁移包 7700 行；这里是两行。

### 2.4 对手 Comodel（第 46–49 行）

```agda
record Comodel (S : Sig) (W : Type) : Type₁ where
  field
    resp : W → (o : Op S) → Res S o × W
```

```
   程序（模型）                 对手（余模型）
   move o k  ──── o ────▶    resp w o = (r , w′)
   k r       ◀─── r ────
```

为什么在这：智能和世界都住在对手这一侧；对手只需要会「答题并更新自己」。

它说什么：`W` 是对手的内部状态，写在类型参数里（LLM 的记忆、世界的数据库）。`resp` 拿一个状态和一步，交回回应和新状态。

项目里的词：想法 6 的 model–comodel。`Free` 是模型（自由模型里的项），`Comodel` 是余模型（按步作答的状态机）。W 放在类型参数而不是字段里，这个选择在 Harness.agda 里救了命，见 4.6。

### 2.5 跑一局 play（第 53–60 行）

```agda
module Play {S : Sig} {W : Type} (C : Comodel S W) where
  play : {A : Type} → Free S A → W → A × W × Trace S
  play (done a)   w = a , w , []
  play (move o k) w =
    let r    = fst (resp C w o)          -- 对手的回应
        w′   = snd (resp C w o)          -- 对手的新状态
        rest = play (k r) w′             -- 接着走
    in fst rest , fst (snd rest) , ((o , r) ∷ snd (snd rest))
```

为什么在这：程序和对手一碰面就跑；跑出的三样东西（结果、对手新状态、棋谱）正是后面要研究的对象。

它说什么：`done` 就停，棋谱为空。`move`：问对手，拿回应，接着跑子树，把这一步的记录放在棋谱最前面。递归沿着程序这棵有限树走，所以一定停。

项目里的词：Plotkin–Power 的「模型 ⊗ 余模型 = 运行」。llm-replay 的回放 = 换一个 `Comodel`，程序一个字不改——这就是 S2 要的「同一程序、两种解释」。

## 3 PathCat.agda：机器 → 范畴（103 行）

一个构造，三层各用一次：给我一本棋规（什么步合法），我还你一个范畴（对象 = 局面，箭头 = 合法棋谱）。范畴只说什么合法；谁来走、走哪步，它不管。

```
   Machine Pos Move  ──Build──▶  Category
   ok p m q（事实）               Ob = Pos，Hom p q = 棋谱 + 合法证明
                                  id = 空棋谱，f ⋆ g = 接棋谱
```

### 3.1 范畴 Category（第 16–25 行）

```agda
record Category : Type₁ where
  field
    Ob     : Type
    Hom    : Ob → Ob → Type
    id     : ∀ {a} → Hom a a
    _⋆_    : ∀ {a b c} → Hom a b → Hom b c → Hom a c      -- 先 f 后 g
    ⋆IdL   : ∀ {a b} (f : Hom a b) → id ⋆ f ≡ f
    ⋆IdR   : ∀ {a b} (f : Hom a b) → f ⋆ id ≡ f
    ⋆Assoc : … (f ⋆ g) ⋆ h ≡ f ⋆ (g ⋆ h)
```

为什么在这：自己写一个，而不用 cubical 库的 `Category`，因为库的版本多一条「箭头是集合」。它要求所有数据都先证明是集合，这次先不背这笔账。

它说什么：对象、箭头、恒等、合成（先 f 后 g，和棋谱的时间方向一致）、三条律。

项目里的词：这就是用 `record` 造范畴、用 `module` 造实例，没有 postulate。

### 3.2 机器 Machine（第 29–35 行）

```agda
record Machine (Pos Move : Type) : Type₁ where
  field
    ok       : Pos → Move → Pos → Type
    isSetPos : isSet Pos                                      -- 局面是数据
    okProp   : ∀ p m q → isProp (ok p m q)                    -- 合法是事实，不是另一份数据
    okDet    : ∀ {p m q q′} → ok p m q → ok p m q′ → q ≡ q′    -- 记录定了，落点就定了
```

```
        m
   p ──────▶ q        ok p m q：这条边存在，是事实（okProp），且 q 唯一（okDet）
```

为什么在这：棋规就是一张有标签的转移图；三条字段把它钉成「确定的、合法性可判的」图。

它说什么：`Pos` 局面、`Move` 一步的记录，写在类型参数里。`ok p m q` 是「在 p 记下 m，落到 q」这个事实。`isSetPos`：局面是数据。`okProp`：合法与否是命题，没有两种不同的合法方式。`okDet`：同一局面、同一条记录，落点唯一。

项目里的词：`okDet` 就是「状态 = 日志的 fold」——日志定了，状态就定了。`okProp` 就是「证明是事实不是数据」，它让后面的范畴律一行写完。Pos/Move 进类型参数是这次改出来的（见 4.6）：局面和记录是什么属于类型，什么合法才是数据。

### 3.3 合法棋谱 Legal（第 40–42 行）

```agda
Legal : Pos → List Move → Pos → Type
Legal p []       q = p ≡ q
Legal p (m ∷ ms) q = Σ[ p₁ ∈ Pos ] (ok M p m p₁ × Legal p₁ ms q)
```

```
   p ──m──▶ p₁ ──ms……──▶ q      空棋谱：p 就是 q
```

为什么在这：一列记录合不合法，要逐步串：第一步合法落到 p₁，剩下的从 p₁ 合法走到 q。

它说什么：递归定义。空列表要求起点等于终点；一步加一列要求存在中间局面 p₁。

项目里的词：这是 Thm 16 那种「同一条线上的括号」的最小版——不交叉的顺序串接。

### 3.4 三条引理（第 45–60 行）

```agda
isPropLegal : ∀ p ms q → isProp (Legal p ms q)       -- 合法证明唯一
legalDet    : ∀ ms → Legal p ms q → Legal p ms q′ → q ≡ q′   -- 终点由棋谱决定
Legal-++    : Legal p ms q → Legal q ns r → Legal p (ms ++ ns) r   -- 棋谱接棋谱
```

为什么在这：范畴律要用到的三件事。第一件靠 `okProp` + `okDet`，第二件靠 `okDet`，第三件就是接列表。

它说什么：都按棋谱的长度归纳。`isPropLegal` 那三行密一点：先用 `okDet` 把两个中间局面对齐，再说剩下的部分因为是命题所以相等（`ΣPathP`、`toPathP` 是 cubical 里「配对相等 = 两边分别相等」的写法）。

### 3.5 范畴 Cat（第 63–79 行）

```agda
Hom p q = Σ[ ms ∈ List Move ] Legal p ms q      -- 箭头 = 棋谱 + 合法证明
idH = [] , refl
(ms , l) ⋆H (ns , l′) = ms ++ ns , Legal-++ ms ns l l′

Cat = record { … ; ⋆IdL = λ f → Σ≡Prop (λ xs → isPropLegal _ xs _) refl
                 ; ⋆IdR = … (++-unit-r (fst f)) ; ⋆Assoc = … (++-assoc …) }
```

为什么在这：这就是「范畴说什么合法」的落地：箭头的第一分量是棋谱，第二分量是它合法的证明。

它说什么：恒等 = 空棋谱；合成 = 接棋谱。三条律：第一分量是 List 的律（`[] ++ xs`、`xs ++ []`、结合），第二分量因为是命题自动相等（`Σ≡Prop`）。

项目里的词：局面 (s, t)「棋盘 + 棋谱」在这里就是这个范畴在起点 b₀ 下的余切片的对象——见 Harness 的 `Position`。

### 3.6 确定的对手 ⇒ 机器，以及第一条定理（第 85–103 行）

```agda
module Det {S} {W} (C : Comodel S W) (isSetW : isSet W) (isSetRes : ∀ o → isSet (Res S o)) where
  MachOf : Machine W (Step S)
  MachOf = record { ok = λ w m w′ → resp C w (fst m) ≡ (snd m , w′) ; … }

  soundDet : (P : Free S A) (w : W) → Legal w (棋谱 (play P w)) (终点 (play P w))
  soundDet (done a)   w = refl
  soundDet (move o k) w = snd (resp C w o) , refl , soundDet (k (fst (resp C w o))) (snd (resp C w o))
```

```
   对手确定：resp w o = (r , w′)
   合法 ⇔ 对手确实这么答了：  w ──(o , r)──▶ w′
```

为什么在这：对手是函数时，「合法」没有别的意思，就是「对手确实这么答了」。对象层的世界（Store）正是这种对手。

它说什么：`MachOf` 把余模型变成机器。`soundDet`：对任何程序、任何起点，`play` 跑出的棋谱从起点合法走到终点。两行证明：空棋谱是 `refl`；一步，中间局面取对手给的新状态，这一步的合法性是 `refl`（对手确实这么答了），剩下的归纳。

项目里的词：这条定理在对象层就是「每次工具调用跑出的事务是 Trans 里的一条箭头」（Harness 的 `transOf`）。预言机不是函数（只受类型约束），所以代理层的机器要另造，这是 Harness §3 的事。

## 4 Harness.agda：三层塔（209 行）

这个文件把 Game 和 PathCat 拼成整个范畴：底是配置树，每个配置上一个纤维，纤维里程序对上对手，最后一条定理说「不管预言机怎么答，棋谱都在纤维里」。十段，每段一件事。

### 4.1 参数替代公理（第 18–28 行）

```agda
module Harness
  (Oracle : Type) (Q : Oracle → Type) (A : Oracle → Type)          -- ① 预言机：问题、回答
  (OState : Type) (oracle : OState → (o : Oracle) → Q o → A o × OState)
  (WSig : Sig) (Board : Type) (isSetBoard : isSet Board)           -- ② 世界：签名、棋盘
  (isSetWRes : ∀ o → isSet (Res WSig o))
  (world : Board → (o : Op WSig) → Res WSig o × Board)
  (Spec Report : Type)                                             -- ③ 子线两端传的数据
  where
```

为什么在这：不准全局公理，所以每个「我们不知道、也不该知道」的东西都成为模块参数。文件里每条定理因此自动是「对任何预言机、任何世界」的全称命题。

它说什么：① `Oracle` 是预言机的种类（LLM、人、时钟各一个），`Q o`、`A o` 是它的问答类型，`OState` 是它们共享的不透明状态，`oracle` 是答题函数。② 世界有自己的签名 `WSig`（读写事务）、状态 `Board`（棋盘）、答题函数 `world`。③ 开子线时递进去的 `Spec`、收回来的 `Report`。

项目里的词：decisions 3「人定的规格是可信计算基」——这几个参数就是规格的位置。`Board` 以后 = Store（键 ↦ 值），`world` 以后 = 事务；这次只要它是一个确定的对手。

### 4.2 对象层：Store 与事务范畴 Trans（第 33–38 行）

```agda
Store : Comodel WSig Board
Store = record { resp = world }

Trans : Category
Trans = Build.Cat (Det.MachOf Store isSetBoard isSetWRes)
```

为什么在这：世界是一个确定的对手，所以 PathCat 的 `Det` 直接给出它的范畴。

它说什么：`Store` 把 `world` 包成余模型。`Trans` 的对象是棋盘，箭头是世界确实走过的一列步——一次事务。

项目里的词：à la Carte 的 Build :: Store → Store。可变性全在箭头上，棋盘是不动的值。

### 4.3 底：规则书 Rules 与配置树 Config（第 44–56 行）

```agda
record Rules : Type₁ where
  field
    Tool        : Type
    Call        : Tool → Type
    Result      : Tool → Type
    isSetResult : ∀ t → isSet (Result t)
    impl        : (t : Tool) → Call t → Free WSig (Result t)   -- 工具 = 对象层的程序

data Config : Type₁ where
  node : (r : Rules) (Kids : Type) (kid : Kids → Config) → Config
```

```
   x = node r Kids kid
        │ kid k₁        │ kid k₂
        ▼               ▼
     x_子₁            x_子₂  …        底是一棵树；▽ 只能往下长
```

为什么在这：规则书 = 工具表；一个配置 = 规则书 + 能开出的子配置。子配置在开子线时就定了，整条子线不换配置，所以根本没有「沿底搬纤维」这回事——你定的。

它说什么：`Rules` 给每个工具一个调用类型、一个结果类型、一段实现。实现是 `Free WSig` 里的一个程序：工具是对象层的态射。`Config` 是一棵树：节点带规则书，`kid` 给每个孩子名一个子配置。

项目里的词：想法 4「态射取代堆砌」——工具不是胶水，是对象层的程序。sigma-vs-names 的「键是角色、名字是实例」：`Tool` 是键，`Kids` 是孩子的名字。

### 4.4 三类步与配置的签名（第 61–72 行；策略树 Strat 在第 76–86 行）

```agda
data Act (r : Rules) (Kids : Type) : Type where
  ask : (o : Oracle) → Q o → Act r Kids          -- 问预言机
  run : (t : Tool r) → Call r t → Act r Kids      -- 动世界
  sub : (k : Kids) → Spec → Act r Kids            -- 开子线

Sig-of (node r Kids kid) = record { Op = Act r Kids ; Res = res }
  where res (ask o q)  = A o
        res (run t c)  = Result r t
        res (sub k sp) = Report × Trace (Sig-of (kid k))   -- 回报 + 子棋谱
```

```
   ask ──▶ 预言机的回答        run ──▶ 世界的结果        sub ──▶ (回报 , 子棋谱)
```

为什么在这：这是代理层的规则书的内容——三类步，各配回应。

它说什么：`Sig-of` 由配置算出签名。`sub` 的回应里带着子线的整条棋谱，所以父棋谱是树形：子线是一条支路，△ 时整条并进来。递归 `Sig-of (kid k)` 落在树的孩子上，所以 Agda 接受它停机。

项目里的词：上一轮的表「签名的加数：ask、run、sub」；two-laters 的「一条线上同一区间的开括号闭括号」——`sub` 的一步就是一对括号，中间夹着子棋谱。

### 4.5 纤维：在 x 下什么合法（第 92–124 行）

```agda
okOf (node r Kids kid) b (ask o q  , a)         b′ = b ≡ b′                 -- 预言机：任何回答都合法，棋盘不动
okOf (node r Kids kid) b (run t c  , rs)        b′ = exec r t c b ≡ (rs , b′) -- 世界：结果和新棋盘由世界定
okOf (node r Kids kid) b (sub k sp , (rep , t)) b′ = Build.Legal (Mach (kid k)) b t b′   -- 子线：子棋谱在子配置下合法

Mach x = record { ok = okOf x ; isSetPos = isSetBoard ; okProp = okPropOf x ; okDet = … }
Fiber x = Build.Cat (Mach x)
```

```
                 (ask , a)                (run , rs)                 (sub , (rep , t))
   b ──────────▶ b      b ──────────▶ exec 的新棋盘      b ────子线整条────▶ b′
   合法 = 真          合法 = 世界这么说             合法 = t 在 Fiber (kid k) 里从 b 到 b′
```

为什么在这：代理层的机器不能用 `Det.MachOf`，因为预言机不是函数。合法性要「不看预言机的内部」：它的任何回答都算合法。

它说什么：三类步三条规则。`ask`：棋盘不动。`run`：`exec` 跑一次工具程序，取（结果，新棋盘），记录必须和它一致。`sub`：子棋谱必须在孩子的纤维里合法——这是递归，`Mach (kid k)` 落在树的孩子上。`okPropOf`、`okDetOf` 两组各三行，给 `Machine` 要的两条事实。`Fiber x` 就是这个机器的范畴。紧接着的 `transOf`（120–124 行）说：代理层的一步 `run`，在对象层是一条箭头——上层的步是下层的路。

项目里的词：这就是「范畴说合法」。sigma-vs-names 里 Σ 的作用（把键换成现任者）在这里是 `exec`：从工具名和参数算出世界的回答。

### 4.6 对手族与策略树：预言机 × 世界 × 子 harness（第 76–86、130–140 行）

```agda
record Strat (x : Config) : Type where          -- 策略树：形状跟着配置树走
  field
    prog : Spec → Free (Sig-of x) Report          -- 这一层的程序
    kids : (k : KidsOf x) → Strat (kidOf x k)     -- 每个孩子的策略

module Dynamics where
  respOf (node r Kids kid) st (s , b) (ask o q)  = let e = oracle s o q in fst e , (snd e , b)
  respOf (node r Kids kid) st (s , b) (run t c)  = let e = exec r t c b   in fst e , (s , snd e)
  respOf (node r Kids kid) st (s , b) (sub k sp) =
    let e = Play.play (opp (kid k) (kids st k)) (prog (kids st k) sp) (s , b)   -- 子线：整条跑完才回来
    in (fst e , snd (snd e)) , fst (snd e)
  opp x st = record { resp = respOf x st }
```

```
   对手 opp x 的状态 = (预言机状态 s , 棋盘 b)
   ask ──▶ 预言机动 s，b 不动      run ──▶ 世界动 b，s 不动      sub ──▶ 子 harness 跑一局，s 和 b 都可能动
   对手之间不直接说话：每一类只碰自己那一格，传话全经程序
```

为什么在这：这是动态——谁真的来答。策略不是「对所有配置」的一个函数，而是一棵和配置树同形的树 Strat x：每个节点一段程序 prog，每个孩子一棵子树 kids（玩具实例逼出来的，见第 8 节）。程序里怎么拼提示词、怎么解析回答、何时停，S1/S4 再定。

它说什么：`opp x` 是配置 x 的对手，状态是（预言机状态，棋盘）。`ask` 交给 `oracle`，`run` 交给 `exec`，`sub` 交给另一个 harness：拿孩子的配置 kid k、策略树里孩子那一支 kids st k、当前的 (s, b)，整条跑完，回报 + 子棋谱作为回应，跑完的 (s, b) 作为新状态。递归 `opp (kid k)` 在树的孩子上。

项目里的词：想法 6 的调用链——子 harness 对父亲是余模型（回答 sub），对世界和预言机是模型（自己发 ask、run）。「子棋盘直接接回父棋盘、不做合并」是因为子线顺序执行、包在父的一拍里；交错与合并留给 decisions 2 那次。

一次改出来的教训：`Comodel` 和 `Machine` 一开始把状态/局面当字段，`opp (kid k)` 在递归里还没定义时 `W (opp (kid k))` 化简不了，类型检查卡住。把 W、Pos、Move 挪进类型参数后就通了。读法：「状态是什么」属于类型，「怎么答」才是数据。

### 4.7 定理 sound：范畴说合法，智能在参数里（第 152–164 行）

```agda
sound : (x : Config) (st : Strat x) (P : Free (Sig-of x) R) (s : OState) (b : Board)
      → Build.Legal (Mach x) b (traceOf x st P s b) (endOf x st P s b)
sound x st (done a) s b = refl
sound (node r Kids kid) st (move (ask o q) k) s b =
  b , refl , sound (node r Kids kid) st (k (fst (oracle s o q))) (snd (oracle s o q)) b
sound (node r Kids kid) st (move (run t c) k) s b =
  snd (exec r t c b) , refl , sound (node r Kids kid) st (k (fst (exec r t c b))) s (snd (exec r t c b))
sound (node r Kids kid) st (move (sub k sp) kk) s b =
  let e = Play.play (opp (kid k) (kids st k)) (prog (kids st k) sp) (s , b)
  in snd (fst (snd e)) , sound (kid k) (kids st k) (prog (kids st k) sp) s b , sound (node r Kids kid) st (kk …) …
```

```
   动态：opp x 跑出 棋谱 t、终点 b′          静态：Fiber x 里 b ──t──▶ b′ 合法
            └──────────── sound：前者一定是后者 ───────────┘
   预言机的状态 s 在动态里有、在静态里没有：sound 就是「把 s 忘掉之后仍然合法」
```

为什么在这：这是整个文件的目的。安全（不走进非法局面）对任何预言机、任何策略成立，可证；进展（做完、做对）靠智能，只能测。

它说什么：按配置和程序双重归纳。`done`：空棋谱，`refl`。`ask`：中间棋盘取 b，合法性是 `refl`，剩下归纳。`run`：中间棋盘取 `exec` 的新棋盘，合法性是 `refl`（世界确实这么答了）。`sub`：合法性由孩子那层的 `sound` 给（配置变小），剩下的由父亲这层归纳（程序变小）。

项目里的词：上一轮说的「∀ 预言机，harness 不走进非法局面」现在是一条已通过检查的定理。录音回放是这个对手的一个确定子余模型，所以 S2 的「两解释器一致」以后就是：两个 `oracle` 参数、同一个 `sound`。

### 4.8 局面、一局的产出、产品（第 170–180 行）

```agda
Position x b₀ = Σ[ b ∈ Board ] Build.Hom (Mach x) b₀ b      -- 局面 = 棋盘 + 到它的合法棋谱
finish x st P s b₀ = endOf x st P s b₀ , traceOf x st P s b₀ , sound x st P s b₀   -- 一局跑完 = 一个局面
Product Accept = Σ[ b ∈ Board ] Accept b                     -- 产品 = 终局棋盘 + 验收证明
```

为什么在这：回答你这轮开头的问题「产出的东西是哪个类型」。

它说什么：局面是 Fiber x 在起点 b₀ 下的余切片的对象：棋盘 b 加一条从 b₀ 到 b 的箭头，棋盘由箭头决定（`okDet`）。`finish` 说一局跑完就得到一个局面——棋谱即证据。产品另有验收谓词 `Accept`（测试通过），由任务给。

项目里的词：想法 1 在产品层：`Product` 和 decisions 3 的「插件 = (程序, 证明)」同形。

### 4.9 反射点：数据 → Maybe 一步（第 188–200 行）

```agda
module Reflect (r : Rules) (Kids : Type) (kid : Kids → Config)
               (llm : Oracle) (check : A llm → Maybe (Act r Kids)) where
  turn : Q llm → Free (Sig-of x) (Maybe (Step (Sig-of x)))
  turn q = move (ask llm q) (λ a → next (check a))
    where next nothing  = done nothing
          next (just m) = move m (λ rs → done (just (m , rs)))
```

```
   回答 a : A llm（数据）──check──▶ nothing（还是数据，停）
                                 ╲
                                  just m（一步：调工具 / 开子线 / 再问）──move m──▶ 记下回应
```

为什么在这：产出既是数据又是控制，但不融合：控制是数据通过检查器之后获得的身份。

它说什么：一回合的骨架：问一次模型，把回答交给 `check`；检查出一步就走它并记下回应，否则停。`check` 由程序调用，不由对手调用——对手只答题，程序决定这段话算不算一步。若 `check a = just (sub k sp)`，模型的文本就变成了一条子线的开端，子配置 `kid k` 由 `check` 选定：子实例就是这样被产出的。

项目里的词：想法 5「物化与反射，区分不融合」；decisions 3「类型检查器是唯一的反射点」——这里 `check` 占的就是那个位置，以后换成真正的检查器。装插件（新配置 x′）是编排层的反射，留到 S7。

### 4.10 三层塔（第 203–209 行）

| 层 | 环境（范畴） | 状态（点） | 一步 | 由谁答 |
| --- | --- | --- | --- | --- |
| 编排 | Config 树（本次不造范畴） | x : Config | ▽ 开子线 (k, sp) | 程序经 check 决定 |
| 代理 | Fiber x | b : Board | ask / run / sub | 预言机 / 世界 / 子 harness |
| 对象 | Trans | b : Board | WSig 的一步 | 世界（确定） |

上层的一步是下层的一条路：`sub` 的一步夹着子纤维里的一整条棋谱，`run` 的一步对应 `transOf` 给出的一条事务箭头。棋盘里面（键 ↦ 值、代码态射）本次没进去，对象层只到「棋盘之间」。

## 5 防住了哪些 TS 兜底

上一轮列的六条，加上这次代码里才看出来的三条。每条写明：DSH 的做法、它为什么需要那样、这三个文件里对应的是哪一行。

| DSH 的做法（TS 兜底） | 为什么 TS 需要它 | 这里的对应物 |
| --- | --- | --- |
| 世界 = OS，账本撤不到文件 | 没有值能持有仓库 | `Board` 是值，`world` 是它上面的函数；IO 以后只是另一个 `Comodel` |
| workspace-changes 事后捕获文件变化 | 产品不是值，只能事后观察 | `exec` 的结果就是新棋盘；`transOf` 把它记成事务范畴里的一条箭头 |
| 工具表会话中途变，靠 epoch / notify / 快照兜底 | 允许缩签名 | 一个配置 `node r Kids kid` 的签名 `Sig-of x` 定死；换表 = 开新子线或新配置 |
| 撤销只撤安装，改坏文件交给 git | 产品在边界外 | 产品层在 `Board` 上定 `Accept`；消除影响以后是「重算到自洽」，不是求逆 |
| 并发安全 = 一个布尔 isConcurrencySafe | 无交换性语义 | 子线顺序执行、包在父的一拍里（`sub` 的回应夹着整条子棋谱）；交错要独立性证明，留 decisions 2 |
| 一切皆插件，系统状态 = 谁装着 | 插件运行时的世界观 | 底（`Config` 树）与纤维（`Fiber x`）分两层；被编辑的东西在纤维里 |
| 日志事件文法手写，4 个迁移包 7700 行 | 日志不是从签名导出的 | `Trace S = List (Step S)`，两行，由签名推出 |
| 依赖中途可撤（guard 是运行时补丁） | 签名可以缩 | 子配置在 `sub` 时定死，整条子线不换；没有「沿底搬纤维」 |
| 模型输出直接当控制（PTC、install\_bundle 经 loader） | loader 是反射点 | `Reflect.check : A llm → Maybe (Act r Kids)`：数据经检查器才成为一步 |

两条反面提醒，是这几个文件里仍然像 TS 的地方：策略树 `Strat x` 的每段 `prog` 还是实例自己写的（提示词怎么拼、回答怎么解析，骨架没定）；`Board` 还是抽象的（没有键、值、事务的内部）。这两处正是下面留白的位置。

## 6 留白与动机：下次补什么、为什么要补

每一处留白都已经在代码里占好了位置；补的时候只换一个参数或加一个 module，不改核心。

```
   Board / WSig / world ──▶ 数据库（Store：键 ↦ 值；事务；版本是值）        ← 你带着动机想清楚再回来
   Strat 的每段 prog   ──▶ S1 一步与循环、S4 提示词投影：step : Trace → Free …
   sub 顺序执行         ──▶ decisions 2：子线交错、棋盘快照与 △ 合并（独立性证明）
   Category 无 isSetHom ──▶ 数据都是集合时一行补上，接进 cubical 库的 Category
   Config 树不造范畴    ──▶ S7：把配置写成数据（岗位表），编排层才有集合、才有范畴
```

**数据库（最大的一块）。** 现在 `Board` 只是一个集合，`world` 只是一个函数。动机：à la Carte 已经给了形状——槽 = 键，数据 = 某个 Store 值在该键上的取值，变 = Store 值之间的箭头，版本是内容的指纹不是计数器。要回答的问题只有一个：`world` 的签名 `WSig` 里放哪几个事务（读、写、还是更粗的「一次提交」），以及两个事务什么时候交换（decisions 2 的合拢条件）。想清楚之后，`Trans` 自动变细。

**策略。** 策略树 `Strat x` 的每个 `prog : Spec → Free (Sig-of x) Report` 现在由实例自己写（玩具里是「读一次，然后预算内反复问 → 检查 → 走」）。动机：它是三样东西的合成——投影（从棋谱和棋盘拼提示词，一个 fold）、`Reflect.turn`（问一次、检查一次）、循环（预算、停机谓词）。`sound` 对任何策略成立，所以写策略时不用再管安全，只管进展。

**子线的交错与合并。** 现在 `sub` 整条跑完才回来，子棋盘直接接回父棋盘。动机：这是不对偶的默认选择（上一轮第 6 节），交错要独立性证明。补的时候 `Res (sub k sp)` 不变，变的是对手 `respOf` 的 `sub` 分支和一个合并参数。

**箭头是集合。** `PathCat.Category` 比库里的少一条 `isSetHom`。动机：`Legal` 已经是命题，`List` 保持集合，只差 `Move` 是集合——即 `Act r Kids` 和各回应类型是集合。参数都取 `hSet` 之后一行补上，就能接 `Cubical.Categories`（函子、displayed category）。

**编排层的范畴。** `Config` 含类型，不是集合，所以这次没造它的范畴。动机：DSH 的编排状态是岗位表（名字和键），是数据；配置先写成数据再解释成 `Rules`，反射 = 数据 → 配置（想法 5 的第三种控制：装插件）。这正是 S7。

**观察等价 ≃。** 文件里没有。10-10 定的：≃ 只在桥上（两个解释器之间），不在环境内。动机：S2 的「同一程序两解释器一致」= 两个 `oracle` / `world` 参数下 `traceOf` 的关系，到时在 Game 层加一个 module 说明两对手何时「说同样的话」。

## 7 在服务器上编译

仓库根目录下一条命令（检查全部四个模块）：

```
./check.sh            # 等于 LC_ALL=C.UTF-8 agda src/Toy.agda
```

你的 `/usr/local/bin/agda` 就是 `agda-cubical-run`，不带 `--cubical-*` 参数时等于原版 Agda 2.9.0；cubical 库已在 `~/.agda/defaults` 里，不用再配。Agda 会按 import 顺序自己先查 Game、PathCat。第一次会顺带检查库里的 `Foundations`、`Data.List`、`Data.Maybe` 等模块，几分钟；之后有 `.agdai` 缓存，秒级。

这里的验证环境是原版 Agda 2.6.3 + cubical v0.5（commit 132a2a3），文件都是 `--safe --cubical`，零警告。用到的库名只有七个，都是多年未变的：`Σ≡Prop`、`ΣPathP`、`toPathP`、`isProp×`、`isSet×`、`++-unit-r`、`++-assoc`。若 2.9.0 配的新库改了其中某个名字，报错会直指那一行，改名即可，不涉及结构。

两点注意：

- 错误信息里有 Σ、≡ 这类字符，locale 不是 UTF-8 时 Agda 会把错误本身吞掉，只剩一句 `cannot encode character`。所以命令前面加 `LC_ALL=C.UTF-8`。
- 可以 `--cubical-run` 的封闭项在 Toy.agda 里：`fst (snd demo)`（棋谱）、`fst demo`（终局）、`fst both`（两局接成的箭头）。骨架本身全是模块参数，没有封闭项；要跑，就填一个实例。

## 8 Toy.agda：玩具实例（184 行，已通过检查）

把 Harness 的 12 个参数全填上最小的东西，让范畴的每一格都有一个能看见的值。任务：把一个计数器从 0 弄到 5。文件末尾的几个 `refl` 就是 Agda 算出来的棋谱和终局。

```
   棋盘 = 计数器 ℕ          世界 WSig = { get , add k }        world b get = (b , b)；world b (add k) = (tt , b + k)
   工具 = inc k（加 k 回报新值）= add k ; get       peek = get      工具是 Free WSig 里的两步程序
   预言机 = llm 一种，按脚本答：add! k / delegate! k / stop!
   配置树：root（Kids = Unit，一个孩子）──▶ leaf（Kids = Empty，没有孩子）
   策略树：root 读一次，然后预算内反复「问 → check → 走」；leaf 不问模型，加 k 就回报
```

### 8.1 填参数（第 3 节，一行）

```agda
open import Harness OK Q A (List Reply) oracle WSig ℕ isSetℕ isSetWRes world ℕ ℕ
```

为什么在这：这一行就是「没有公理」的另一面——公理变成了参数，参数在这里被兑现。从这行起 `Config`、`Fiber`、`sound` 全有了具体形状。

### 8.2 跑一局，看棋谱（第 7 节）

```agda
script = add! 2 ∷ delegate! 3 ∷ stop! ∷ []          -- 模型的脚本
demo   = finish root rootStrat (rootProg 3) script 0  -- 预算 3，起点 0

accepted : Product (λ b → b ≡ 5)
accepted = fst demo , refl                           -- 终局 = 5，验收由计算直接给出

trace-is : fst (snd demo) ≡ expected
trace-is = refl                                      -- 棋谱逐条等于下面这个
```

```
 根的棋谱（6 条记录，一条 sub 里夹着子棋谱）：
   0 ─(run peek , 0)─▶ 0 ─(ask 0 , add! 2)─▶ 0 ─(run inc 2 , 2)─▶ 2 ─(ask 2 , delegate! 3)─▶ 2
     ─(sub tt 3 , (5 , [ (run inc 3 , 5) ]))─▶ 5 ─(ask 5 , stop!)─▶ 5
                        └── 子线：叶纤维里一条长度 1 的箭头 2 ──▶ 5，对根是一个点
```

为什么在这：这是「子实例对父是点还是段」的实物：根看到的是第 5 条记录一个点，点里装着叶的整段。

它说什么：`ask` 不动棋盘，`run` 按世界动，`sub` 整条跑完才回来。`accepted` 的 `refl` 能过，是因为所有东西都是封闭项，Agda 把 `fst demo` 直接算成了 5——这就是 dev-order-draft 的「行为尺」：终态等于预期，由归约给出。

### 8.3 范畴在干什么（第 8 节）

```agda
demo′ = finish root rootStrat (rootProg 3) script 5     -- 同一脚本从 5 再跑到 10
both  = _⋆_ (Fiber root) (snd demo) (snd demo′)          -- 两局接起来 = 0 → 10 的一条箭头，12 条记录

one-tx : Hom Trans 0 2
one-tx = transOf rules inc 2 0                           -- 代理层一步 run inc 2 = 对象层两步 (add 2 , tt) ∷ (get , 2)
```

```
 Fiber root：   0 ──demo──▶ 5 ──demo′──▶ 10        both = demo ⋆ demo′
 Trans：        0 ──(add 2 , tt)──▶ 2 ──(get , 2)──▶ 2     one-tx = 上面 run inc 2 那一步的展开
```

为什么在这：范畴律在这里第一次有用：两局的棋谱接起来仍是一条合法箭头，合法证明自动接上，不用重新证。`transOf` 则把「上层的一步是下层的一条路」变成一个可以算出来的值。

### 8.4 玩具逼出的一处骨架修改

原来 `Dynamics` 要一个「对所有配置」的策略 `(x : Config) → Spec → Free (Sig-of x) Report`。写玩具时发现写不出来：策略必须知道自己配置的工具表（要写 `run inc`），而对任意 x 这张表是未知的。改成策略树 `Strat x`（每个配置一段程序，每个孩子一棵子树），形状跟着配置树走，叶子的 `kids = λ ()`。读法：子 harness 的策略是父策略的一部分，正如 DSH 里子代理的定义是父配置的一部分。

**决定（2026-10-11）：用 B。** 理由（用户原话）：配置本来就要自带程序。工具是类型，不是要解码的数据；点了不存在的工具是编译错误。「所有节点跑同一个循环」的通用策略 A 不丢，它是 B 的特例：`mkStrat x = record { prog = strategy x ; kids = λ k → mkStrat (kidOf x k) }`，到 S4 有提示词与解码时再写。

### 8.5 它给下一步的动机

- `valueOf`（从记录里读「现在计数是多少」）和 `rootProg` 里的 `loop` 都是手写的；S1 要把它们换成「状态 = 棋谱的 fold、提示词 = 投影」，手写的部分就消失。
- 脚本预言机只有一种；换成真模型 = 换 `oracle` 参数，`sound` 不动，`trace-is` 变成一条要测的性质而不是 `refl`——这就是 S2 的两解释器。
- 棋盘是一个数，世界只有读和加；换成 Store（键 ↦ 值）时，`Trans` 的箭头会从「两步」变成真正的事务，两个 `inc` 什么时候交换就成了可以问的问题（decisions 2）。
- 叶子不问模型。让叶子也问模型只要给它一个自己的 `check`，根的任何东西都不改——子实例的智能是局部的。
