{-# OPTIONS --safe --cubical #-}
------------------------------------------------------------------------
-- Str.agda —— 字符串零件：拼接、分行、围栏、修剪、掐中间。Solve（任务一）和 Bench（ProgramBench）共用
------------------------------------------------------------------------
module Str where

open import Cubical.Data.List.Base using (List; []; _∷_; _++_; length; rev)
open import Cubical.Data.Nat.Base using (ℕ; zero; suc; _+_; _∸_; _<ᵇ_)
open import Cubical.Data.Bool.Base using (Bool; true; false)
open import Cubical.Data.Maybe.Base using (Maybe; nothing; just)
open import Agda.Builtin.Char using (Char)
open import Agda.Builtin.String using (String; primStringAppend; primStringToList; primStringFromList; primStringEquality; primShowNat)

_++ₛ_ : String → String → String
_++ₛ_ = primStringAppend
infixr 5 _++ₛ_

_=ₛ_ : String → String → Bool
_=ₛ_ = primStringEquality

------------------------------------------------------------------------
-- §1 行
------------------------------------------------------------------------
-- 按换行切成行
splitLines : List Char → List (List Char)
splitLines []          = [] ∷ []
splitLines ('\n' ∷ cs) = [] ∷ splitLines cs
splitLines (c ∷ cs)    = cons (splitLines cs)
  where
  cons : List (List Char) → List (List Char)
  cons []       = (c ∷ []) ∷ []
  cons (l ∷ ls) = (c ∷ l) ∷ ls

unlines : List (List Char) → List Char
unlines []       = []
unlines (l ∷ ls) = l ++ ('\n' ∷ unlines ls)

-- 围栏行：去掉前导空格后以 ` 开头（``` 或 ```agda、```bash）
isFence : List Char → Bool
isFence (' ' ∷ cs) = isFence cs
isFence ('`' ∷ _)  = true
isFence _          = false

dropFences : List (List Char) → List (List Char)
dropFences []       = []
dropFences (l ∷ ls) with isFence l
... | true  = dropFences ls
... | false = l ∷ dropFences ls

-- LLM 常把代码包在 ``` 里：整行的围栏丢掉，其余原样
stripFences : String → String
stripFences s = primStringFromList (unlines (dropFences (splitLines (primStringToList s))))

-- 第一个围栏块的内容（不含围栏行）；没有围栏 → nothing
inside : List (List Char) → List (List Char)
inside []       = []
inside (l ∷ ls) with isFence l
... | true  = []
... | false = l ∷ inside ls

fenced : List (List Char) → Maybe (List (List Char))
fenced []       = nothing
fenced (l ∷ ls) with isFence l
... | true  = just (inside ls)
... | false = fenced ls

firstBlock : String → Maybe String
firstBlock s with fenced (splitLines (primStringToList s))
... | nothing = nothing
... | just ls = just (primStringFromList (unlines ls))

------------------------------------------------------------------------
-- §2 修剪、掐中间
------------------------------------------------------------------------
isSpace : Char → Bool
isSpace ' '  = true
isSpace '\n' = true
isSpace '\t' = true
isSpace '\r' = true
isSpace _    = false

dropSpaces : List Char → List Char
dropSpaces []       = []
dropSpaces (c ∷ cs) with isSpace c
... | true  = dropSpaces cs
... | false = c ∷ cs

trim : String → String
trim s = primStringFromList (rev (dropSpaces (rev (dropSpaces (primStringToList s)))))

takeC : ℕ → List Char → List Char
takeC zero    _        = []
takeC _       []       = []
takeC (suc n) (c ∷ cs) = c ∷ takeC n cs

dropC : ℕ → List Char → List Char
dropC zero    cs       = cs
dropC _       []       = []
dropC (suc n) (_ ∷ cs) = dropC n cs

-- 超过 limit 个字符就只留头 keep、尾 keep，中间写明掐掉了多少
elide : ℕ → ℕ → String → String
elide limit keep s with primStringToList s
... | cs with length cs
...   | n with limit <ᵇ n
...     | false = s
...     | true  = primStringFromList (takeC keep cs)
                  ++ₛ "\n<elided_chars>\n" ++ₛ primShowNat (n ∸ (keep + keep)) ++ₛ " characters elided\n</elided_chars>\n"
                  ++ₛ primStringFromList (dropC (n ∸ keep) cs)
