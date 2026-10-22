{-# OPTIONS --safe --cubical #-}
------------------------------------------------------------------------
-- Replay.agda —— Rebuilder：要不要重跑
--   手里有一份录音（上一局的棋谱）。再跑一局时：
--     ask  录音里下一条是同一个问题 → 直接放答案，不问预言机
--     run  世界照跑（便宜且确定）；结果和录音一样 → 继续放，不一样 → 扔掉录音
--     sub  校验录音里夹的子棋谱（verify = 可判定的合法性）：通过 → 整条子线不跑，直接记账
--   verify 就是 à la Carte 的 verifying trace；放录音就是 constructive trace。
--   录音对手诚实（wrap-honest），所以 sound 对它照样成立——它只是又一个对手。
-- 参数与 Harness 相同，另加可判定相等（DecCfg）。
------------------------------------------------------------------------
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Relation.Nullary
open import Cubical.Relation.Nullary.Properties
open import Cubical.Data.Sigma
open import Cubical.Data.Sigma.Properties using (discreteΣ)
open import Cubical.Data.Sum
open import Cubical.Data.Sum.Properties using (discrete⊎)
open import Cubical.Data.List
open import Cubical.Data.Maybe
open import Cubical.Data.Maybe.Properties using (just-inj ; ¬nothing≡just)
open import Cubical.Data.Empty renaming (rec to ⊥rec)
open import Game
open import PathCat

module Replay
  (Oracle : Type) (Q : Oracle → Type) (A : Oracle → Type)
  (OState : Type) (oracle : OState → (o : Oracle) → Q o → A o × OState)
  (WSig : Sig) (Board : Type) (isSetBoard : isSet Board)
  (isSetWRes : ∀ o → isSet (Res WSig o))
  (world : Board → (o : Op WSig) → Res WSig o × Board)
  (Spec Report : Type)
  (Lifting : Type) (restrict : Lifting → Board → Board) (merge : Lifting → Board → Board → Board)
  where

import Harness
open Harness Oracle Q A OState oracle WSig Board isSetBoard isSetWRes world Spec Report Lifting restrict merge

------------------------------------------------------------------------
-- §0 每个配置要能判定：步相等吗（对录音）、工具结果相等吗（对世界）
--   形状跟配置树走（同 Strat）；DecAct 从规则书里的零件拼出 decOp
------------------------------------------------------------------------
rulesOf : Config → Rules
rulesOf (node r Kids kid lf) = r

record DecCfg (x : Config) : Type where
  inductive
  no-eta-equality
  field
    decOp  : Discrete (Op (Sig-of x))
    decRes : (t : Tool (rulesOf x)) → Discrete (Result (rulesOf x) t)
    kids   : (k : KidsOf x) → DecCfg (kidOf x k)
open DecCfg public

module DecAct (decO : Discrete Oracle) (decQ : ∀ o → Discrete (Q o)) (decSpec : Discrete Spec) where

  decAct : (r : Rules) (Kids : Type) → Discrete (Tool r) → (∀ t → Discrete (Call r t)) → Discrete Kids
         → Discrete (Act r Kids)
  decAct r Kids decT decC decK =
    isoPresDiscrete (iso from to from-to to-from)
      (discrete⊎ (discreteΣ decO decQ) (discrete⊎ (discreteΣ decT decC) (discreteΣ decK (λ _ → decSpec))))
    where
      Sum : Type
      Sum = (Σ Oracle Q) ⊎ ((Σ (Tool r) (Call r)) ⊎ (Kids × Spec))
      from : Sum → Act r Kids
      from (inl (o , q))        = ask o q
      from (inr (inl (t , c)))  = run t c
      from (inr (inr (k , sp))) = sub k sp
      to : Act r Kids → Sum
      to (ask o q)  = inl (o , q)
      to (run t c)  = inr (inl (t , c))
      to (sub k sp) = inr (inr (k , sp))
      from-to : ∀ a → from (to a) ≡ a
      from-to (ask o q)  = refl
      from-to (run t c)  = refl
      from-to (sub k sp) = refl
      to-from : ∀ s → to (from s) ≡ s
      to-from (inl (o , q))        = refl
      to-from (inr (inl (t , c)))  = refl
      to-from (inr (inr (k , sp))) = refl

------------------------------------------------------------------------
-- §1 校验：一段录音从棋盘 b 出发还合法吗？合法就算出终点
--   ask 任何答案都合法；run 重算一次比结果；sub 递归校验子棋谱，再按运输回来
------------------------------------------------------------------------
onJust : {X Y : Type} → Maybe X → (X → Maybe Y) → Maybe Y
onJust nothing  f = nothing
onJust (just x) f = f x

verify : (x : Config) → DecCfg x → Board → Trace (Sig-of x) → Maybe Board
verify x d b [] = just b
verify (node r Kids kid lf) d b ((ask o q  , a)          ∷ t) = verify (node r Kids kid lf) d b t
verify (node r Kids kid lf) d b ((run tl c , rs)         ∷ t) =
  decRec (λ _ → verify (node r Kids kid lf) d (snd (exec r tl c b)) t) (λ _ → nothing)
         (decRes d tl (fst (exec r tl c b)) rs)
verify (node r Kids kid lf) d b ((sub k sp , (rep , ct)) ∷ t) =
  onJust (verify (kid k) (kids d k) (restrict (lf k) b) ct)
         (λ c → verify (node r Kids kid lf) d (merge (lf k) b c) t)

-- 校验通过 ⇒ 真的合法（可判定的检查蕴含命题）
verify-sound : (x : Config) (d : DecCfg x) (b : Board) (t : Trace (Sig-of x)) (b′ : Board)
             → verify x d b t ≡ just b′ → Build.Legal (Mach x) b t b′
verify-sound x d b [] b′ h = just-inj _ _ h
verify-sound (node r Kids kid lf) d b ((ask o q , a) ∷ t) b′ h =
  b , refl , verify-sound (node r Kids kid lf) d b t b′ h
verify-sound (node r Kids kid lf) d b ((run tl c , rs) ∷ t) b′ h with decRes d tl (fst (exec r tl c b)) rs
... | yes p = snd (exec r tl c b) , (λ i → p i , snd (exec r tl c b))
            , verify-sound (node r Kids kid lf) d (snd (exec r tl c b)) t b′ h
... | no  _ = ⊥rec (¬nothing≡just h)
verify-sound (node r Kids kid lf) d b ((sub k sp , (rep , ct)) ∷ t) b′ h =
  lemma (verify (kid k) (kids d k) (restrict (lf k) b) ct) refl h
  where
    lemma : (m : Maybe Board) → verify (kid k) (kids d k) (restrict (lf k) b) ct ≡ m
          → onJust m (λ c → verify (node r Kids kid lf) d (merge (lf k) b c) t) ≡ just b′
          → Build.Legal (Mach (node r Kids kid lf)) b ((sub k sp , (rep , ct)) ∷ t) b′
    lemma nothing  e h′ = ⊥rec (¬nothing≡just h′)
    lemma (just c) e h′ =
      merge (lf k) b c
      , (c , verify-sound (kid k) (kids d k) (restrict (lf k) b) ct c e , refl)
      , verify-sound (node r Kids kid lf) d (merge (lf k) b c) t b′ h′

------------------------------------------------------------------------
-- §2 录音对手：包住任何诚实的对手
--   需要对手的状态里能读、能写棋盘（一个 lens；Dynamics 的 W 直接给出）
------------------------------------------------------------------------
record BoardLens (W : Type) : Type where
  field
    board   : W → Board
    setB    : W → Board → W
    set-get : ∀ w b → board (setB w b) ≡ b
open BoardLens public

dynLens : (X : Type) → BoardLens (OState × Board × X)
dynLens X = record { board = λ { (s , b , xx) → b } ; setB = λ { (s , b , xx) b′ → s , b′ , xx } ; set-get = λ _ _ → refl }

caseM : {X Y : Type} → Maybe X → (X → Y) → Y → Y
caseM nothing  f y = y
caseM (just x) f y = f x

module _ (x : Config) (d : DecCfg x) {W : Type} (C : Comodel (Sig-of x) W) (L : BoardLens W) where

  WR : Type
  WR = W × Trace (Sig-of x)            -- 原对手的状态 × 还没放完的录音

  real : W → (o : Op (Sig-of x)) → Res (Sig-of x) o × WR     -- 回到真对手；录音清空
  real w o = fst (resp C w o) , (snd (resp C w o) , [])

-- 录音对上了之后，按步的种类处理（x 要拆开才知道步长什么样）
stepR : (x : Config) (d : DecCfg x) {W : Type} (C : Comodel (Sig-of x) W) (L : BoardLens W)
      → W → Trace (Sig-of x) → (o : Op (Sig-of x)) → Res (Sig-of x) o → Res (Sig-of x) o × (W × Trace (Sig-of x))
stepR (node r Kids kid lf) d C L w t (ask o q)  a          = a , (w , t)
stepR (node r Kids kid lf) d C L w t (run tl c) rs         =
  let e = resp C w (run tl c)
  in fst e , (snd e , decRec (λ _ → t) (λ _ → []) (decRes d tl (fst e) rs))
stepR (node r Kids kid lf) d C L w t (sub k sp) (rep , ct) =
  caseM (verify (kid k) (kids d k) (restrict (lf k) (board L w)) ct)
        (λ c → (rep , ct) , (setB L w (merge (lf k) (board L w) c) , t))     -- 校验通过：记账，不跑
        (real (node r Kids kid lf) d C L w (sub k sp))                          -- 不通过：真跑

respR : (x : Config) (d : DecCfg x) {W : Type} (C : Comodel (Sig-of x) W) (L : BoardLens W)
      → WR x d C L → (o : Op (Sig-of x)) → Res (Sig-of x) o × WR x d C L
respR x d C L (w , [])            o = real x d C L w o
respR x d C L (w , (o′ , r′) ∷ t) o with decOp d o o′
... | no  _ = real x d C L w o
... | yes p = stepR x d C L w t o (subst (Res (Sig-of x)) (sym p) r′)

wrap : (x : Config) (d : DecCfg x) {W : Type} (C : Comodel (Sig-of x) W) (L : BoardLens W)
     → Comodel (Sig-of x) (WR x d C L)
wrap x d C L = record { resp = respR x d C L }

------------------------------------------------------------------------
-- §3 录音对手诚实 ⇒ sound 对它成立（Harness.soundHonest）
------------------------------------------------------------------------
stepR-honest : (x : Config) (d : DecCfg x) {W : Type} (C : Comodel (Sig-of x) W) (L : BoardLens W)
             → Honest x C (board L) → ∀ w t o r
             → okOf x (board L w) (o , fst (stepR x d C L w t o r)) (board L (fst (snd (stepR x d C L w t o r))))
stepR-honest (node r Kids kid lf) d C L h w t (ask o q)  a          = refl
stepR-honest (node r Kids kid lf) d C L h w t (run tl c) rs         = h w (run tl c)
stepR-honest (node r Kids kid lf) d C L h w t (sub k sp) (rep , ct) =
  lemma (verify (kid k) (kids d k) (restrict (lf k) (board L w)) ct) refl
  where
    lemma : (m : Maybe Board) → verify (kid k) (kids d k) (restrict (lf k) (board L w)) ct ≡ m
          → okOf (node r Kids kid lf) (board L w)
                 (sub k sp , fst (caseM m (λ c → (rep , ct) , (setB L w (merge (lf k) (board L w) c) , t))
                                          (real (node r Kids kid lf) d C L w (sub k sp))))
                 (board L (fst (snd (caseM m (λ c → (rep , ct) , (setB L w (merge (lf k) (board L w) c) , t))
                                              (real (node r Kids kid lf) d C L w (sub k sp))))))
    lemma nothing  e = h w (sub k sp)
    lemma (just c) e = c , verify-sound (kid k) (kids d k) (restrict (lf k) (board L w)) ct c e
                         , sym (set-get L w (merge (lf k) (board L w) c))

wrap-honest : (x : Config) (d : DecCfg x) {W : Type} (C : Comodel (Sig-of x) W) (L : BoardLens W)
            → Honest x C (board L) → Honest x (wrap x d C L) (λ wr → board L (fst wr))
wrap-honest x d C L h (w , [])            o = h w o
wrap-honest x d C L h (w , (o′ , r′) ∷ t) o with decOp d o o′
... | no  _ = h w o
... | yes p = stepR-honest x d C L h w t o (subst (Res (Sig-of x)) (sym p) r′)
