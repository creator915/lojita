{-# OPTIONS --safe --cubical #-}
-- 必须编译失败：子实例的 realm 是 "a/"，想写 "b/x"（confineL：孩子碰不到 R 外的键）
module NegRealm where
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
bad = move (enter (header (natM ∷ []) safeCubical tt tt) 1 "a/") λ _ →
      move (set "b/x" "1") λ _ → done "out of realm"
