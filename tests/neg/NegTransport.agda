{-# OPTIONS --safe --cubical #-}
-- 必须编译失败：transport 的目标键在 realm 外（子实例的 realm 是 "a" ∷ []，想把答卷搬到 "b" ∷ "code" ∷ "X.agda" ∷ []）
module NegTransport where
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
bad = move (enter (header (natM ∷ []) safeCubical tt tt) 1 ("a" ∷ [])) λ _ →
      move (transport whole ("b" ∷ "code" ∷ "X.agda" ∷ []) [] ("a" ∷ "draft" ∷ "1" ∷ "X.agda" ∷ [])) λ _ → done "out of realm"
