{-# OPTIONS --safe --cubical #-}
-- 必须编译失败：在 Run NodeSig 里想用 set 写 code/…。NodeSig 没有裸的 set（Env.Op 的 set 不是 NodeOp 的步），
-- setN 的 Note 也只有 memo / verdict / result / dropped 四种，没有 code：code 行只能经 transport 写（N2）
module NegNote where
open import Cubical.Foundations.Prelude using (Type)
open import Cubical.Data.List.Base using ([]; _∷_)
open import Cubical.Data.Unit.Base using (tt)
open import Cubical.Data.Sigma using (_,_)
open import Agda.Builtin.String using (String)
open import Env
open import ToyEnv using (natM; safeCubical)
open import Later using (Run; done; move)
import Node

module N = Node (natM ∷ []) safeCubical ("--cubical" ∷ []) tt tt tt
open N using (E⁻; NodeSig)

A : Ix → Type
A _ = String

ix : Ix
ix = (E⁻ , 3 , "t" ∷ []) , []

bad : Run NodeSig A ix
bad = move (set ("t" ∷ "code" ∷ "X.agda" ∷ []) "twice n = n + n") λ _ → done "wrote code with set"
