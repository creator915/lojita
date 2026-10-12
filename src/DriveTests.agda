{-# OPTIONS --safe --cubical #-}
------------------------------------------------------------------------
-- DriveTests.agda —— 喂给后端驱动器的几段程序（./drive-tests.sh）
--   Agda 侧只负责把它们写成 Code；判决由后端（Agda 的检查器）给。
--   前四段都该被驳回（fail，程序交 nothing），最后一段该通过（just 0）
------------------------------------------------------------------------
module DriveTests where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat
open import Cubical.Data.Sigma
open import Cubical.Data.List
open import Cubical.Data.Maybe
open import Later
open import Code 1 2 (λ _ → 0)
open import Load 1 2 (λ _ → 0)

-- 装一段程序，装完交 just 0；哪条被驳回就交 nothing（原因在 [drive] 日志里）
try : {Γ : Env} → Code ε Γ → Run CodeSig (λ _ → Maybe ℕ) ε
try P = loadThen P (done (just 0)) nothing

-- 1 类型错：f n = suc "x"
badType : Run CodeSig (λ _ → Maybe ℕ) ε
badType = try
  ( tool nat nat
  ▹ fun (# 1) (clause 1 ((vis , pvar (# 0)) ∷ []) (con (# 1) ((vis , lit (strL "x")) ∷ [])) ∷ [])
  ▹ ∅ )

-- 2 不停机：f n = f n
loop : Run CodeSig (λ _ → Maybe ℕ) ε
loop = try
  ( tool nat nat
  ▹ fun (# 1) (clause 1 ((vis , pvar (# 0)) ∷ []) (def (# 1) ((vis , var (# 0) []) ∷ [])) ∷ [])
  ▹ ∅ )

-- 3 负性：data Bad : Set where mk : (Bad → Bad) → Bad
negData : Run CodeSig (λ _ → Maybe ℕ) ε
negData = try
  ( datasig 0 (sort 0)
  ▹ datadef (# 1) 1 (pi vis (pi vis (def (# 1) []) (def (# 1) [])) (def (# 1) []) , tt)
  ▹ ∅ )

-- 4 用了声明过但没定义的名字（等于用公理）：f : ℕ 没有体；g n = f
useUndefined : Run CodeSig (λ _ → Maybe ℕ) ε
useUndefined = try
  ( sig (def (# 0) [])
  ▹ tool nat nat
  ▹ fun (# 2) (clause 1 ((vis , pvar (# 0)) ∷ []) (def (# 1) []) ∷ [])
  ▹ ∅ )

-- 5 该通过：一般的签名 id : ℕ → ℕ（不是工具），id n = n
sigOk : Run CodeSig (λ _ → Maybe ℕ) ε
sigOk = try
  ( sig (pi vis (def (# 0) []) (def (# 0) []))
  ▹ fun (# 1) (clause 1 ((vis , pvar (# 0)) ∷ []) (var (# 0) []) ∷ [])
  ▹ ∅ )
