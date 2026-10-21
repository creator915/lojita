{-# OPTIONS --safe --cubical #-}
------------------------------------------------------------------------
-- Keys.agda —— 后端要实现的那个 Store：键和值都是字符串
--   S = Store String String。后端 --cubical-handler=store:DIR 在硬盘上实现的就是 S.world：
--   目录是唯一的那块盘，每一步进一个盘出一个盘（线性地调用，所以可以就地改）。
--   discreteString 由内建引理推出（primStringToListInjective、primCharToNatInjective），零 postulate。
------------------------------------------------------------------------
module Keys where

open import Cubical.Foundations.Prelude using (cong)
open import Cubical.Relation.Nullary using (Discrete; yes; no)
open import Cubical.Data.Nat.Properties using (discreteℕ)
open import Cubical.Data.List.Properties using (discreteList)
open import Cubical.Data.Equality.Conversion using (eqToPath; pathToEq)
open import Agda.Builtin.Char using (Char; primCharToNat)
open import Agda.Builtin.Char.Properties using (primCharToNatInjective)
open import Agda.Builtin.String using (String; primStringToList)
open import Agda.Builtin.String.Properties using (primStringToListInjective)
import Store

-- 字符可判定相等：经 primCharToNat 嵌进 ℕ
discreteChar : Discrete Char
discreteChar a b with discreteℕ (primCharToNat a) (primCharToNat b)
... | yes p = yes (eqToPath (primCharToNatInjective a b (pathToEq p)))
... | no ¬p = no (λ q → ¬p (cong primCharToNat q))

-- 字符串可判定相等：经 primStringToList 嵌进 List Char
discreteString : Discrete String
discreteString a b with discreteList discreteChar (primStringToList a) (primStringToList b)
... | yes p = yes (eqToPath (primStringToListInjective a b (pathToEq p)))
... | no ¬p = no (λ q → ¬p (cong primStringToList q))

-- 实例 S.Board、写 S.upd、签名 S.WSig、余模型 S.world、事务 S.runTx、子 schema S.Realm / S.Lifting
module S = Store String String discreteString discreteString
