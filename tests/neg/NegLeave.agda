{-# OPTIONS --safe --cubical #-}
-- 必须编译失败：根上 leave（hasParent 算出 false）
module NegLeave where
open import Cubical.Foundations.Prelude using (Type)
open import Agda.Builtin.String using (String)
open import Env
open import ToyEnv using (ix₀)
open import Later using (Run; done; move)

A : Ix → Type
A _ = String

bad : Run AgdaSig A ix₀
bad = move leave λ _ → done "escaped"
