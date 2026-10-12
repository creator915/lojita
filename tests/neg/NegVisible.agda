{-# OPTIONS --safe --cubical #-}
-- 必须编译失败：头里 import 了环境里看不见的 M1（imports-ok 算出 false，tt 填不上）
module NegVisible where
open import Cubical.Data.List.Base using ([]; _∷_)
open import Cubical.Data.Unit.Base using (tt)
open import Env
open import ToyEnv using (E₀; safeCubical)

bad : Header E₀
bad = header (("M1" ∷ []) ∷ []) safeCubical tt tt
