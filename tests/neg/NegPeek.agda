{-# OPTIONS --safe --cubical #-}
-- 必须编译失败：孩子帧的头想 import 父在节点帧里刚 check 过的模块 M1。
-- 孩子的环境 = child (E₀ ▸ i) h，只看得见 h 里列的 Nat；imports-ok 算出 false，tt 填不上（运行时 mkHeader 回 nothing）
module NegPeek where
open import Cubical.Data.List.Base using ([]; _∷_)
open import Cubical.Data.Unit.Base using (tt)
open import Env
open import ToyEnv using (E₀; natM; safeCubical)

hKid : (i : Iface) → Header (E₀ ▸ i)                   -- 父给孩子的头：只有 Nat（算得出：visible E₀ natM = true）
hKid i = header (natM ∷ []) safeCubical tt tt

bad : (i : Iface) → Header (child (E₀ ▸ i) (hKid i))    -- 孩子想 import M1：看不见
bad i = header (("M1" ∷ []) ∷ []) safeCubical tt tt
