{-# OPTIONS --safe --cubical #-}
-- 必须编译失败：父 --safe，子想关掉它（coinfective，父有子必有）
module NegUnsafe where
open import Cubical.Data.List.Base using ([]; _∷_)
open import Cubical.Data.Unit.Base using (tt)
open import Env
open import ToyEnv using (E₀; natM)

bad : Header E₀
bad = header (natM ∷ []) ("--cubical" ∷ []) tt tt
