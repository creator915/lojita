{-# OPTIONS --safe --cubical #-}
-- 必须编译失败：子实例想开父没开的 --guardedness（infective，只降不升）
module NegFlags where
open import Cubical.Data.List.Base using ([]; _∷_)
open import Cubical.Data.Unit.Base using (tt)
open import Env
open import ToyEnv using (E₀; natM)

bad : Header E₀
bad = header (natM ∷ []) ("--safe" ∷ "--cubical" ∷ "--guardedness" ∷ []) tt tt
