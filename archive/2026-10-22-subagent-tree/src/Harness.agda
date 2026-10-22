{-# OPTIONS --safe --cubical #-}
------------------------------------------------------------------------
-- Harness.agda —— 整个范畴的骨架（三层塔）
--   底      配置 x（规则书 + 能开的子配置 + 每条边上的运输），一棵树
--   纤维    Fiber x：对象 = 棋盘，箭头 = 在 x 下合法的棋谱
--   纤维里  程序（策略） 对上 对手（预言机 × 世界 × 子 harness）
--   诚实    Honest：一步一步按 Mach x 走的对手。执行者、录音器的唯一义务
--   定理    任何诚实的对手、任何策略，跑出来的棋谱都是 Fiber x 里的一条箭头
-- 没有全局公理：预言机、世界、数据库、运输……全是下面这个模块的参数。
------------------------------------------------------------------------
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Data.Sigma
open import Cubical.Data.List
open import Cubical.Data.Maybe
open import Game
open import PathCat

module Harness
  -- ① 预言机：智能与外部性的来源（LLM、人、时钟……）。只受类型约束，内容是参数
  (Oracle : Type) (Q : Oracle → Type) (A : Oracle → Type)
  (OState : Type) (oracle : OState → (o : Oracle) → Q o → A o × OState)
  -- ② 世界：对象层的签名与数据库（Store.agda 交出这五样）
  (WSig : Sig) (Board : Type) (isSetBoard : isSet Board)
  (isSetWRes : ∀ o → isSet (Res WSig o))
  (world : Board → (o : Op WSig) → Res WSig o × Board)
  -- ③ 子线两端传的数据
  (Spec Report : Type)
  -- ④ 运输：kid 边上面，棋盘怎么下去（restrict）、怎么回来（merge）
  --    运输是数据（Lifting），解释成两个函数；Store.Lifts 给出 whole / realm 两种
  (Lifting : Type) (restrict : Lifting → Board → Board) (merge : Lifting → Board → Board → Board)
  where

------------------------------------------------------------------------
-- §0 对象层：世界是一个确定的对手；事务范畴
------------------------------------------------------------------------
Store : Comodel WSig Board
Store = record { resp = world }

Trans : Category
Trans = Build.Cat (Det.MachOf Store isSetBoard isSetWRes)

------------------------------------------------------------------------
-- §1 底：配置 = 规则书 + 孩子 + 每条边上的运输
------------------------------------------------------------------------
record Rules : Type₁ where
  field
    Tool        : Type
    Call        : Tool → Type
    Result      : Tool → Type
    isSetResult : ∀ t → isSet (Result t)
    impl        : (t : Tool) → Call t → Free WSig (Result t)
open Rules public

-- 子配置在开子线时就定了，整条子线不换；运输也定在边上（结构，不是执行者的事）
data Config : Type₁ where
  node : (r : Rules) (Kids : Type) (kid : Kids → Config) (lf : Kids → Lifting) → Config

------------------------------------------------------------------------
-- §2 一层能走的三类步，与它们的回应：配置的签名
------------------------------------------------------------------------
data Act (r : Rules) (Kids : Type) : Type where
  ask : (o : Oracle) → Q o → Act r Kids          -- 问预言机
  run : (t : Tool r) → Call r t → Act r Kids      -- 动世界（走一次事务）
  sub : (k : Kids) → Spec → Act r Kids            -- 开子线

Sig-of : Config → Sig
Sig-of (node r Kids kid lf) = record { Op = Act r Kids ; Res = res }
  where
    res : Act r Kids → Type
    res (ask o q)  = A o
    res (run t c)  = Result r t
    res (sub k sp) = Report × Trace (Sig-of (kid k))   -- 回报 + 子棋谱

KidsOf : Config → Type
KidsOf (node r Kids kid lf) = Kids
kidOf : (x : Config) → KidsOf x → Config
kidOf (node r Kids kid lf) = kid
liftOf : (x : Config) → KidsOf x → Lifting
liftOf (node r Kids kid lf) = lf

-- 策略树：形状跟着配置树走
record Strat (x : Config) : Type where
  inductive
  no-eta-equality
  field
    prog : Spec → Free (Sig-of x) Report
    kids : (k : KidsOf x) → Strat (kidOf x k)
open Strat public

------------------------------------------------------------------------
-- §3 纤维：在 x 下什么棋谱合法（静态：不看预言机的内部、不看执行者）
------------------------------------------------------------------------
exec : (r : Rules) (t : Tool r) → Call r t → Board → Result r t × Board
exec r t c b = let e = Play.play Store (impl r t c) b in fst e , fst (snd e)

Mach : (x : Config) → Machine Board (Step (Sig-of x))

okOf : (x : Config) → Board → Step (Sig-of x) → Board → Type
okOf (node r Kids kid lf) b (ask o q  , a)         b′ = b ≡ b′
okOf (node r Kids kid lf) b (run t c  , rs)        b′ = exec r t c b ≡ (rs , b′)
okOf (node r Kids kid lf) b (sub k sp , (rep , t)) b′ =      -- 子线：下去、子棋谱合法、回来
  Σ[ c ∈ Board ] (Build.Legal (Mach (kid k)) (restrict (lf k) b) t c × (merge (lf k) b c ≡ b′))

okPropOf : (x : Config) → ∀ b m b′ → isProp (okOf x b m b′)
okPropOf (node r Kids kid lf) b (ask o q  , a)         b′ = isSetBoard b b′
okPropOf (node r Kids kid lf) b (run t c  , rs)        b′ = isSet× (isSetResult r t) isSetBoard _ _
okPropOf (node r Kids kid lf) b (sub k sp , (rep , t)) b′ (c₁ , l₁ , e₁) (c₂ , l₂ , e₂) =
  ΣPathP (Build.legalDet (Mach (kid k)) t l₁ l₂ ,
          toPathP (isProp× (Build.isPropLegal (Mach (kid k)) _ t c₂) (isSetBoard _ _) _ _))

okDetOf : (x : Config) → ∀ b m {b′ b″} → okOf x b m b′ → okOf x b m b″ → b′ ≡ b″
okDetOf (node r Kids kid lf) b (ask o q  , a)         e e′ = sym e ∙ e′
okDetOf (node r Kids kid lf) b (run t c  , rs)        e e′ = cong snd (sym e ∙ e′)
okDetOf (node r Kids kid lf) b (sub k sp , (rep , t)) (c₁ , l₁ , e₁) (c₂ , l₂ , e₂) =
  sym e₁ ∙ cong (merge (lf k) b) (Build.legalDet (Mach (kid k)) t l₁ l₂) ∙ e₂

Mach x = record
  { ok = okOf x ; isSetPos = isSetBoard
  ; okProp = okPropOf x ; okDet = λ {b} {m} → okDetOf x b m }

Fiber : Config → Category
Fiber x = Build.Cat (Mach x)

transOf : (r : Rules) (t : Tool r) (c : Call r t) (b : Board)
        → Category.Hom Trans b (snd (exec r t c b))
transOf r t c b = snd (snd (Play.play Store (impl r t c) b))
                , Det.soundDet Store isSetBoard isSetWRes (impl r t c) b

------------------------------------------------------------------------
-- §4 诚实的对手，与执行者
--   Honest：对手每答一步，都是 Mach x 的一步（在棋盘投影 board 下）。
--   结构（Mach x）不知道对手是谁；对手只需要诚实。真对手、录音对手都诚实（见 Dynamics、Replay）。
------------------------------------------------------------------------
Honest : (x : Config) {W : Type} → Comodel (Sig-of x) W → (W → Board) → Type
Honest x C board = ∀ w o → okOf x (board w) (o , fst (resp C w o)) (board (snd (resp C w o)))

-- 诚实 ⇒ 整局合法：一步一步接起来
soundHonest : (x : Config) {W : Type} (C : Comodel (Sig-of x) W) (board : W → Board) → Honest x C board
            → {R : Type} (P : Free (Sig-of x) R) (w : W)
            → Build.Legal (Mach x) (board w) (snd (snd (Play.play C P w))) (board (fst (snd (Play.play C P w))))
soundHonest x C board h (done a)   w = refl
soundHonest x C board h (move o k) w =
  board (snd (resp C w o)) , h w o , soundHonest x C board h (k (fst (resp C w o))) (snd (resp C w o))

-- 执行者：拿一个诚实的对手和一个程序，跑出（结果、终态、棋谱），并担保棋谱合法。
-- 这是 à la Carte 的 Scheduler 槽：结构只要求这一个证明字段，不规定怎么跑。
-- 默认 = Play.play（suspending：开了就跑到底）。中止/并发的执行者要改 Σ，到时填进同一个槽。
record Exec : Type₁ where
  field
    execute : (x : Config) {W : Type} (C : Comodel (Sig-of x) W) (board : W → Board) → Honest x C board
        → {R : Type} → Free (Sig-of x) R → W → R × W × Trace (Sig-of x)
    execute-sound : (x : Config) {W : Type} (C : Comodel (Sig-of x) W) (board : W → Board) (h : Honest x C board)
              → {R : Type} (P : Free (Sig-of x) R) (w : W)
              → Build.Legal (Mach x) (board w) (snd (snd (execute x C board h P w))) (board (fst (snd (execute x C board h P w))))

playExec : Exec
playExec = record { execute = λ x C board h P w → Play.play C P w ; execute-sound = soundHonest }

------------------------------------------------------------------------
-- §5 对手族（动态）：预言机 × 世界 × 子 harness，沿 sub 边用三个 lens 下去、回来
--   棋盘：restrict / merge（结构，定在边上）
--   预言机状态：原样传给孩子、原样收回（共享会话；独立会话 = 把它并进 X）
--   X：上下文的其余部分——资源账的位子。enter = 对父的 Σ 做一次更新（扣账），leave = 归还
------------------------------------------------------------------------
module Dynamics (X : Type) (enter : X → Spec → X) (leave : X → X → X) (E : Exec) where

  W : Type
  W = OState × Board × X

  board : W → Board
  board (s , b , xx) = b

  opp    : (x : Config) → Strat x → Comodel (Sig-of x) W
  honest : (x : Config) (st : Strat x) → Honest x (opp x st) board
  respOf : (x : Config) → Strat x → W → (m : Op (Sig-of x)) → Res (Sig-of x) m × W

  respOf (node r Kids kid lf) st (s , b , xx) (ask o q) = let e = oracle s o q in fst e , (snd e , b , xx)
  respOf (node r Kids kid lf) st (s , b , xx) (run t c) = let e = exec r t c b   in fst e , (s , snd e , xx)
  respOf (node r Kids kid lf) st (s , b , xx) (sub k sp) =
    let e  = Exec.execute E (kid k) (opp (kid k) (kids st k)) board (honest (kid k) (kids st k))
                        (prog (kids st k) sp) (s , restrict (lf k) b , enter xx sp)   -- 下去
        w′ = fst (snd e)
    in (fst e , snd (snd e)) , (fst w′ , merge (lf k) b (board w′) , leave xx (snd (snd w′)))   -- 回来
  opp x st = record { resp = respOf x st }

  honest (node r Kids kid lf) st (s , b , xx) (ask o q) = refl
  honest (node r Kids kid lf) st (s , b , xx) (run t c) = refl
  honest (node r Kids kid lf) st (s , b , xx) (sub k sp) =
    board (fst (snd e))
    , Exec.execute-sound E (kid k) (opp (kid k) (kids st k)) board (honest (kid k) (kids st k))
                       (prog (kids st k) sp) (s , restrict (lf k) b , enter xx sp)
    , refl
    where
      e = Exec.execute E (kid k) (opp (kid k) (kids st k)) board (honest (kid k) (kids st k))
                     (prog (kids st k) sp) (s , restrict (lf k) b , enter xx sp)

  -- 一局的产出
  endOf   : (x : Config) (st : Strat x) {R : Type} → Free (Sig-of x) R → W → Board
  endOf   x st P w = board (fst (snd (Play.play (opp x st) P w)))
  traceOf : (x : Config) (st : Strat x) {R : Type} → Free (Sig-of x) R → W → Trace (Sig-of x)
  traceOf x st P w = snd (snd (Play.play (opp x st) P w))

  -- §6 定理：对任何策略、任何预言机、任何执行者、任何运输，跑出的棋谱在 Fiber x 里合法
  sound : (x : Config) (st : Strat x) {R : Type} (P : Free (Sig-of x) R) (w : W)
        → Build.Legal (Mach x) (board w) (traceOf x st P w) (endOf x st P w)
  sound x st = soundHonest x (opp x st) board (honest x st)

  -- 局面 = 棋盘 + 从起点到它的合法棋谱；一局跑完 = 一个局面
  Position : Config → Board → Type
  Position x b₀ = Σ[ b ∈ Board ] Build.Hom (Mach x) b₀ b

  finish : (x : Config) (st : Strat x) {R : Type} (P : Free (Sig-of x) R) (w : W) → Position x (board w)
  finish x st P w = endOf x st P w , traceOf x st P w , sound x st P w

-- 产品 = 终局棋盘 + 验收证明
Product : (Accept : Board → Type) → Type
Product Accept = Σ[ b ∈ Board ] Accept b

------------------------------------------------------------------------
-- §7 反射点：数据 → Maybe 一步
------------------------------------------------------------------------
module Reflect (r : Rules) (Kids : Type) (kid : Kids → Config) (lf : Kids → Lifting)
               (llm : Oracle) (check : A llm → Maybe (Act r Kids)) where

  x : Config
  x = node r Kids kid lf

  turn : Q llm → Free (Sig-of x) (Maybe (Step (Sig-of x)))
  turn q = move (ask llm q) (λ a → next (check a))
    where
      next : Maybe (Act r Kids) → Free (Sig-of x) (Maybe (Step (Sig-of x)))
      next nothing  = done nothing
      next (just m) = move m (λ rs → done (just (m , rs)))

------------------------------------------------------------------------
-- §8 三层塔，与 à la Carte 的槽
--  层    环境（范畴）     状态（点）        一步              由谁答
--  编排  Config 树        x : Config        ▽ 开子线 (k , sp)  程序经 check 决定
--  代理  Fiber x          b : Board         ask / run / sub   预言机 / 世界 / 子 harness
--  对象  Trans            b : Board         WSig 的一步        世界（确定）
--  槽：  Lifting（每条边的运输，结构）× (X, enter, leave)（上下文 lens）× Exec（执行者）× 对手（真 / 录音）
--        结构只认 Honest；换槽里的东西，sound 不动。
------------------------------------------------------------------------
