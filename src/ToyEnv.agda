{-# OPTIONS --safe --cubical #-}
------------------------------------------------------------------------
-- ToyEnv.agda —— 用脚本余模型跑一局：check 两个模块、开一个窄的子实例、问一次、回来。全部 refl
--   真后端（agda 进程）和这里的脚本后端住同一个槽（Comodel AgdaSig W）
------------------------------------------------------------------------
module ToyEnv where

open import Cubical.Foundations.Prelude using (Type; _≡_; refl)
open import Cubical.Data.List.Base using (List; []; _∷_)
open import Cubical.Data.Bool.Base using (Bool; true; false)
open import Cubical.Data.Nat.Base using (ℕ; zero; suc)
open import Cubical.Data.Sigma
open import Cubical.Data.Maybe.Base using (Maybe; nothing; just)
open import Cubical.Data.Unit.Base using (Unit; tt)
open import Cubical.Data.Sum.Base using (inr)
open import Agda.Builtin.String using (String)
open import Syntax
open import Env
open import Later using (Run; done; move; Comodel; module Play; module Traces)

------------------------------------------------------------------------
-- §1 手写几个 Code 值（真实运行时它们从 quote 来）
------------------------------------------------------------------------
name : String → Name
name s = Name′ InScope (Id s ∷¹ [])

qn : String → QName
qn s = QName′ (name s)

natQ : QName                                      -- Cubical.Data.Nat
natQ = Qual (name "Cubical") (Qual (name "Data") (qn "Nat"))

natM : ModName
natM = "Cubical" ∷ "Data" ∷ "Nat" ∷ []

noErase : Erased
noErase = NotErased QωInferred

everything : ImportDirective Name Name
everything = ImportDirective′ UseEverything [] [] nothing

openImport : QName → Declaration                  -- open import q
openImport q = Import DoOpen q (inr []) everything

-- {-# OPTIONS fl #-} module m where ds
file : String → List String → List Declaration → Module
file m fl ds = Mod (qn m) (OptionsPragma fl ∷ []) (Module′ noErase (qn m) [] ds ∷ [])

safeCubical : Flags
safeCubical = "--safe" ∷ "--cubical" ∷ []

------------------------------------------------------------------------
-- §2 起点：只看得见 Cubical.Data.Nat，模式 --safe --cubical，配额 3
------------------------------------------------------------------------
E₀ : Env
E₀ = base (_=ₘ natM) safeCubical

ix₀ : Ix
ix₀ = (E₀ , 3) , []

-- M1 import Nat；头里的两条证明都是算出来的 tt
M1 : Code E₀
M1 = code (header (natM ∷ []) safeCubical tt tt)
          (file "M1" safeCubical (openImport natQ ∷ []))
          tt tt

-- M2 import M1：只有 check M1 过了之后才写得出来（visible 里多了 M1）；它不看接口 i 的内容
M2 : (i : Iface) → Code (E₀ ▸ (M1 , i))
M2 i = code (header (("M1" ∷ []) ∷ []) safeCubical tt tt)
            (file "M2" safeCubical (openImport (qn "M1") ∷ []))
            tt tt

-- 子实例的头：只给它 M1、同样的模式。给 M2 或 Nat 以外的名字、或多开 --guardedness，都是编译错误
hKid : (i₁ i₂ : Iface) → Header (E₀ ▸ (M1 , i₁) ▸ (M2 i₁ , i₂))
hKid i₁ i₂ = header (("M1" ∷ []) ∷ []) safeCubical tt tt

------------------------------------------------------------------------
-- §3 程序：check M1 → check M2 → enter（配额 1）→ ask → leave → done（LLM 的回答）
------------------------------------------------------------------------
A : Ix → Type
A _ = String

prog : Run AgdaSig A ix₀
prog =
  move (check M1) λ
    { (ok i₁) → move (check (M2 i₁)) λ
        { (ok i₂) → move (enter (hKid i₁ i₂) 1) λ _ →
                    move (ask "下一步做什么") λ a →
                    move leave λ _ →
                    done a
        ; (fail _ m) → done m }
    ; (fail _ m) → done m }

------------------------------------------------------------------------
-- §4 脚本余模型：check 按脚本判，脚本用完一律 ok；ask 固定答 "yes"
------------------------------------------------------------------------
W : Ix → Type
W _ = List Verdict

ifaceOf : Module → Iface
ifaceOf m = iface (modNameOf m) [] (optionsOf m) 0

respS : {ix : Ix} → W ix → (o : Op ix) → Σ[ r ∈ Res o ] W (next o r)
respS w        (parse _)    = nothing , w
respS []       (check c)    = ok (ifaceOf (body c)) , []
respS (v ∷ vs) (check c)    = v , vs
respS w        (eval _ _)   = error "scripted" , w
respS w        (render _)   = "" , w
respS w        (enter _ _)  = tt , w
respS w        leave        = tt , w
respS w        (ask _)      = "yes" , w
respS w        (readF _)    = nothing , w
respS w        (writeF _ _) = false , w
respS w        (log _)      = tt , w

backend : Comodel AgdaSig W
backend = record { resp = respS }

------------------------------------------------------------------------
-- §5 跑一局，全部 refl
------------------------------------------------------------------------
open Traces AgdaSig using (Trace) renaming ([] to ε; _∷_ to _◁_)

run : Σ[ j ∈ Ix ] (A j × W j × Trace ix₀ j)
run = Play.play backend prog []

final : Ix
final = fst run

len : {i j : Ix} → Trace i j → ℕ
len ε       = 0
len (_ ◁ t) = suc (len t)

_ : fst (snd run) ≡ "yes"                               -- LLM 的回答交出来了
_ = refl

_ : visible (envOf final) ("M2" ∷ []) ≡ true            -- 回到父实例：M1、M2 都看得见
_ = refl

_ : visible (envOf final) ("M3" ∷ []) ≡ false
_ = refl

_ : quotaOf final ≡ 2                                   -- 父给了子 1 份配额
_ = refl

_ : len (snd (snd (snd run))) ≡ 5                       -- check、check、enter、ask、leave
_ = refl

-- 第三条声明被驳回：环境停在 E₀ ▸ M1，结果是报错原文
run′ : Σ[ j ∈ Ix ] (A j × W j × Trace ix₀ j)
run′ = Play.play backend prog (ok (ifaceOf (body M1)) ∷ fail [] "no" ∷ [])

_ : fst (snd run′) ≡ "no"
_ = refl

_ : visible (envOf (fst run′)) ("M2" ∷ []) ≡ false
_ = refl
