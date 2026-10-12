{-# OPTIONS --safe --cubical #-}
------------------------------------------------------------------------
-- ToyCode.agda —— 让反射工具跑一遍：写一段程序，逐条装进环境，然后调用新工具
--   库：一个数据类型 ℕ（0 个参数），两个构造子 zero、suc
--   程序：data Color where red green；twice : ℕ → ℕ（工具）；twice n = suc (suc n)
--   §4 脚本后端全通过：四条都装进去，call twice 5 = 7，终点环境 = Γ₄，棋谱 5 条，全部 refl
--   §5 第三条被驳回：环境停在 Γ₂，程序停下，棋谱 3 条
--   §6 装之前调不了：call (# 0) 在 ε 上是编译错误（注释里）
------------------------------------------------------------------------
module ToyCode where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat
open import Cubical.Data.Sigma
open import Cubical.Data.List
open import Cubical.Data.Maybe
open import Cubical.Data.Unit
open import Cubical.Data.SumFin.Base using (Fin ; fzero ; fsuc)
open import Later
open import Code 1 2 (λ _ → 0)
open import Load 1 2 (λ _ → 0)

------------------------------------------------------------------------
-- 1 名字：库里 ℕ 是定义 0 号，zero / suc 是构造子 0 / 1 号
------------------------------------------------------------------------
-- 2 程序：四条声明，每条都写在它要扩展的那个环境上
------------------------------------------------------------------------
Γ₁ : Env                                                   -- data Color : Set
Γ₁ = ε ▸ datasig 0 (sort 0)

colorDef : Decl Γ₁                                         -- red green : Color（Color 是定义 1 号）
colorDef = datadef (# 1) 2 (def (# 1) [] , def (# 1) [] , tt)

Γ₂ : Env
Γ₂ = Γ₁ ▸ colorDef

Γ₃ : Env                                                   -- twice : El nat → El nat（定义 2 号，工具 0 号）
Γ₃ = Γ₂ ▸ tool nat nat

twiceDef : Decl Γ₃                                         -- twice n = suc (suc n)
twiceDef = fun (# 2)
  ( clause 1 ((vis , pvar (# 0)) ∷ [])
      (con (# 1) ((vis , con (# 1) ((vis , var (# 0) []) ∷ [])) ∷ []))
  ∷ [] )

Γ₄ : Env
Γ₄ = Γ₃ ▸ twiceDef

prog : Code ε Γ₄                                           -- 程序 = 从 ε 到 Γ₄ 的箭头
prog = datasig 0 (sort 0) ▹ colorDef ▹ tool nat nat ▹ twiceDef ▹ ∅

-- 环境就是程序的 fold：从 ε 走 prog 恰好到 Γ₄，而 Γ₄ 自己的日志就是 prog
path-is : path Γ₄ ≡ prog
path-is = refl

------------------------------------------------------------------------
-- 3 策略：装完整段程序，再调 twice 5；哪条没装进去就交 nothing
--   call (# 0) 写在 Γ₄ 上：工具 0 号此时才存在——这就是 ▷
------------------------------------------------------------------------
strat : Run CodeSig (λ _ → Maybe ℕ) ε
strat = loadThen prog (move (call (# 0) 5) λ n → done (just n)) nothing

------------------------------------------------------------------------
-- 4 脚本后端：nat → nat 的工具一律算 twice（真后端按体算）；脚本为空 ⇒ 全通过
------------------------------------------------------------------------
newImpl : NewImpl
newImpl (tool nat nat) fzero n = suc (suc n)
newImpl (tool c   r)   fzero _ = dflt r

open Scripted newImpl

noImpls : Impls ε
noImpls ()

run₁ : Σ[ Γ ∈ Env ] (Maybe ℕ × W Γ × Trace ε Γ)
run₁ = Play.play backend strat (noImpls , [])

env₁ : fst run₁ ≡ Γ₄                                        -- 终点环境
env₁ = refl

result₁ : fst (snd run₁) ≡ just 7                           -- twice 5
result₁ = refl

trace₁ : snd (snd (snd run₁)) ≡
    (load (datasig 0 (sort 0)) , ok 0)
  ∷ (load colorDef            , ok 0)
  ∷ (load (tool nat nat)      , ok 0)
  ∷ (load twiceDef            , ok 0)
  ∷ (call (# 0) 5             , 7)
  ∷ []
trace₁ = refl

accepted₁ : accepted (snd (snd (snd run₁))) ≡ prog           -- 棋谱里通过的声明就是程序
accepted₁ = refl

------------------------------------------------------------------------
-- 5 第三条被驳回（脚本：过、过、驳）：环境停在 Γ₂，后面的不装、不调
------------------------------------------------------------------------
run₂ : Σ[ Γ ∈ Env ] (Maybe ℕ × W Γ × Trace ε Γ)
run₂ = Play.play backend strat (noImpls , ok 1 ∷ ok 2 ∷ fail "not a tool" ∷ [])

env₂ : fst run₂ ≡ Γ₂
env₂ = refl

result₂ : fst (snd run₂) ≡ nothing
result₂ = refl

trace₂ : snd (snd (snd run₂)) ≡
    (load (datasig 0 (sort 0)) , ok 1)
  ∷ (load colorDef            , ok 2)
  ∷ (load (tool nat nat)      , fail "not a tool")
  ∷ []
trace₂ = refl

------------------------------------------------------------------------
-- 6 装之前调不了。把下面两行取消注释，Agda 拒绝：# 0 要的隐式证明是
--   Bool→Type (ltᵇ 0 (count tn ε)) = ⊥，填不上，call 的回应类型卡住，报 UnequalTypes / 未解元变量
--   ——在 ε 上没有 0 号工具；它只在 load (tool nat nat) 判 ok 之后的那一拍才存在
-- tooEarly : Run CodeSig (λ _ → Maybe ℕ) ε
-- tooEarly = move (call (# 0) 5) λ n → done (just n)
------------------------------------------------------------------------
