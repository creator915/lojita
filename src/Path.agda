{-# OPTIONS --safe --cubical #-}
------------------------------------------------------------------------
-- Path.agda —— 路径键：Store 的键与 realm 按段存成列表，前缀判定用可判定相等
--   Path            一段一个字符串；"a/x" 写成 "a" ∷ "x" ∷ []；根 realm 是 []
--   isPrefix p k    k 以 p 开头。逐段比，用 Keys.discreteString（可判定相等，能 with 分情况）；
--                   不用 primStringEquality：primStringEquality x x ≡ true 没有内建引理，变量前缀的引理证不出
--   prefix-++ p s   isPrefix p (p ++ s) ≡ true     变量前缀下写键的证明（Node 的 setN、transport、enter 孩子）
--   prefix-refl p   isPrefix p p ≡ true            同前缀开沙箱 / 粘合帧
--   _≤ᵇ_ ≤ᵇ-refl half half-≤                       配额：给孩子一半，half q ≤ᵇ q
--   join p          后端的键："a" ∷ "x" ∷ [] ↦ "a/x"（脚本余模型 ToyEnv 用它存 S.Board；日志里的键也长这样）
--   字面量键的前置条件照旧自动算成 tt；变量前缀用引理 subst 过去（见 Node.agda §3）
------------------------------------------------------------------------
module Path where

open import Cubical.Foundations.Prelude using (Type; _≡_; refl)
open import Cubical.Data.List.Base using (List; []; _∷_; _++_)
open import Cubical.Data.List.Properties using (discreteList)
open import Cubical.Data.Bool.Base using (Bool; true; false)
open import Cubical.Data.Bool.Properties using (false≢true)
open import Cubical.Data.Nat.Base using (ℕ; zero; suc)
open import Cubical.Data.Empty as ⊥ using ()
open import Cubical.Relation.Nullary using (Discrete; yes; no; decRec)
open import Agda.Builtin.String using (String; primStringAppend)
open import Keys using (discreteString)

------------------------------------------------------------------------
-- §1 路径与前缀
------------------------------------------------------------------------
Path : Type
Path = List String

discretePath : Discrete Path
discretePath = discreteList discreteString

isPrefix : Path → Path → Bool
isPrefix []       _        = true
isPrefix (_ ∷ _)  []       = false
isPrefix (p ∷ ps) (k ∷ ks) = decRec (λ _ → isPrefix ps ks) (λ _ → false) (discreteString p k)

-- 对 p 归纳；每段 with discreteString x x，no 的分支用 ¬p refl 排除
prefix-++ : ∀ p s → isPrefix p (p ++ s) ≡ true
prefix-++ []      s = refl
prefix-++ (x ∷ p) s with discreteString x x
... | yes _  = prefix-++ p s
... | no  ¬p = ⊥.rec (¬p refl)

prefix-refl : ∀ p → isPrefix p p ≡ true
prefix-refl []      = refl
prefix-refl (x ∷ p) with discreteString x x
... | yes _  = prefix-refl p
... | no  ¬p = ⊥.rec (¬p refl)

------------------------------------------------------------------------
-- §2 配额的算术
------------------------------------------------------------------------
_≤ᵇ_ : ℕ → ℕ → Bool
zero  ≤ᵇ _     = true
suc _ ≤ᵇ zero  = false
suc m ≤ᵇ suc n = m ≤ᵇ n

≤ᵇ-refl : ∀ q → q ≤ᵇ q ≡ true
≤ᵇ-refl zero    = refl
≤ᵇ-refl (suc q) = ≤ᵇ-refl q

≤ᵇ-suc : ∀ m n → m ≤ᵇ n ≡ true → m ≤ᵇ suc n ≡ true
≤ᵇ-suc zero    n       _ = refl
≤ᵇ-suc (suc m) zero    e = ⊥.rec (false≢true e)
≤ᵇ-suc (suc m) (suc n) e = ≤ᵇ-suc m n e

-- 给孩子分配额：half 0 = 0 ; half 1 = 0 ; half (2+n) = 1 + half n
half : ℕ → ℕ
half zero          = zero
half (suc zero)    = zero
half (suc (suc n)) = suc (half n)

half-≤ : ∀ q → half q ≤ᵇ q ≡ true
half-≤ zero          = refl
half-≤ (suc zero)    = refl
half-≤ (suc (suc n)) = ≤ᵇ-suc (half n) n (half-≤ n)

------------------------------------------------------------------------
-- §3 后端的键：段间 "/"
------------------------------------------------------------------------
join : Path → String
join []      = ""
join (s ∷ p) = primStringAppend s (rest p)
  where
  rest : Path → String
  rest []      = ""
  rest (t ∷ p) = primStringAppend "/" (primStringAppend t (rest p))

------------------------------------------------------------------------
-- §4 验收 E4：字面量键自动算出
------------------------------------------------------------------------
_ : isPrefix ("a" ∷ []) ("a" ∷ "x" ∷ []) ≡ true
_ = refl

_ : isPrefix ("a" ∷ []) ("b" ∷ "x" ∷ []) ≡ false
_ = refl

_ : isPrefix [] ("a" ∷ []) ≡ true
_ = refl

_ : join ("a" ∷ "x" ∷ []) ≡ "a/x"
_ = refl
