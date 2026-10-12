{-# OPTIONS --safe --cubical #-}
------------------------------------------------------------------------
-- PathCat.agda —— 一次构造，三层各用一次
--   机器（棋规） ───▶ 范畴（对象 = 局面，箭头 = 合法棋谱）
-- 范畴只说"什么合法"；谁来走、走哪步，它不管。
------------------------------------------------------------------------
module PathCat where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Data.Sigma
open import Cubical.Data.List
open import Game

-- 范畴（先不要求"箭头是集合"；库里的 Category 多那一条，数据定成集合后可补）
record Category : Type₁ where
  field
    Ob     : Type
    Hom    : Ob → Ob → Type
    id     : ∀ {a} → Hom a a
    _⋆_    : ∀ {a b c} → Hom a b → Hom b c → Hom a c            -- 先 f 后 g
    ⋆IdL   : ∀ {a b} (f : Hom a b) → id ⋆ f ≡ f
    ⋆IdR   : ∀ {a b} (f : Hom a b) → f ⋆ id ≡ f
    ⋆Assoc : ∀ {a b c d} (f : Hom a b) (g : Hom b c) (h : Hom c d)
           → (f ⋆ g) ⋆ h ≡ f ⋆ (g ⋆ h)

-- 机器 = 棋规。Pos = 局面，Move = 一步的记录，都写在类型里；字段只说 ok
--   ok p m q   事实："在 p 记下 m，落到 q" 是合法的
record Machine (Pos Move : Type) : Type₁ where
  field
    ok       : Pos → Move → Pos → Type
    isSetPos : isSet Pos                                     -- 局面是数据（集合）
    okProp   : ∀ p m q → isProp (ok p m q)                   -- 合法是事实，不是另一份数据
    okDet    : ∀ {p m q q′} → ok p m q → ok p m q′ → q ≡ q′   -- 记录定了，落点就定了：状态 = 棋谱的 fold
open Machine public

module Build {Pos Move : Type} (M : Machine Pos Move) where

  -- 一列记录从 p 合法地走到 q（逐步串起来）
  Legal : Pos → List Move → Pos → Type
  Legal p []       q = p ≡ q
  Legal p (m ∷ ms) q = Σ[ p₁ ∈ Pos ] (ok M p m p₁ × Legal p₁ ms q)

  -- 合法性是命题：同一列记录、同一起点，证明唯一
  isPropLegal : ∀ p ms q → isProp (Legal p ms q)
  isPropLegal p []       q = isSetPos M p q
  isPropLegal p (m ∷ ms) q (p₁ , o₁ , l₁) (p₂ , o₂ , l₂) =
    ΣPathP (okDet M o₁ o₂ ,
            toPathP (isProp× (okProp M p m p₂) (isPropLegal p₂ ms q) _ _))

  -- 终点由棋谱决定
  legalDet : ∀ {p q q′} ms → Legal p ms q → Legal p ms q′ → q ≡ q′
  legalDet []       e           e′            = sym e ∙ e′
  legalDet (m ∷ ms) (_ , o , l) (_ , o′ , l′) =
    legalDet ms (subst (λ x → Legal x ms _) (okDet M o o′) l) l′

  -- 棋谱接棋谱
  Legal-++ : ∀ {p q r} ms ns → Legal p ms q → Legal q ns r → Legal p (ms ++ ns) r
  Legal-++ []       ns e            l = subst (λ x → Legal x ns _) (sym e) l
  Legal-++ (m ∷ ms) ns (p₁ , o , l₁) l = p₁ , o , Legal-++ ms ns l₁ l

  -- 箭头 = 棋谱 + 它合法的证明
  Hom : Pos → Pos → Type
  Hom p q = Σ[ ms ∈ List Move ] Legal p ms q

  idH : ∀ {p} → Hom p p
  idH = [] , refl

  _⋆H_ : ∀ {p q r} → Hom p q → Hom q r → Hom p r
  (ms , l) ⋆H (ns , l′) = ms ++ ns , Legal-++ ms ns l l′

  -- 范畴律：第一分量是 List 的律，第二分量因为是命题自动相等
  Cat : Category
  Cat = record
    { Ob = Pos ; Hom = Hom ; id = idH ; _⋆_ = _⋆H_
    ; ⋆IdL   = λ f → Σ≡Prop (λ xs → isPropLegal _ xs _) refl
    ; ⋆IdR   = λ f → Σ≡Prop (λ xs → isPropLegal _ xs _) (++-unit-r (fst f))
    ; ⋆Assoc = λ f g h → Σ≡Prop (λ xs → isPropLegal _ xs _)
                                (++-assoc (fst f) (fst g) (fst h)) }

------------------------------------------------------------------------
-- 确定的对手 ⇒ 机器：合法 = "对手确实这么答了"
-- （预言机不确定，所以代理层的机器要另造，见 Harness.agda §3）
------------------------------------------------------------------------
module Det {S : Sig} {W : Type} (C : Comodel S W)
           (isSetW : isSet W) (isSetRes : ∀ o → isSet (Res S o)) where

  MachOf : Machine W (Step S)
  MachOf = record
    { ok = λ w m w′ → resp C w (fst m) ≡ (snd m , w′)
    ; isSetPos = isSetW
    ; okProp = λ w m w′ → isSet× (isSetRes (fst m)) isSetW _ _
    ; okDet = λ e e′ → cong snd (sym e ∙ e′) }

  open Build MachOf
  open Play C

  -- 定理：跑出来的棋谱一定合法（对任何程序、任何起点）
  soundDet : {A : Type} (P : Free S A) (w : W)
           → Legal w (snd (snd (play P w))) (fst (snd (play P w)))
  soundDet (done a)   w = refl
  soundDet (move o k) w =
    snd (resp C w o) , refl , soundDet (k (fst (resp C w o))) (snd (resp C w o))
