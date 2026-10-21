{-# OPTIONS --safe --cubical #-}
-- 必须编译失败：父只有 3 份配额，想给子 5 份
module NegQuota where
open import Cubical.Foundations.Prelude using (Type)
open import Cubical.Data.List.Base using ([]; _∷_)
open import Cubical.Data.Unit.Base using (tt)
open import Agda.Builtin.String using (String)
open import Env
open import ToyEnv using (E₀; ix₀; natM; safeCubical)
open import Later using (Run; done; move)

A : Ix → Type
A _ = String

bad : Run AgdaSig A ix₀
bad = move (enter (header (natM ∷ []) safeCubical tt tt) 5 "") λ _ → done "too generous"
