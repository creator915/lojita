{-# OPTIONS --safe --cubical #-}
------------------------------------------------------------------------
-- ToyNode.agda —— node 在脚本余模型（ToyEnv.backend）上的六局，全部 refl（docs/harness/04-node.md §9）
--   每局：造剧本 → Play.play backend (embedRun (node d q p "X")) → 断言结局、enter / ask 次数、关键行
--   E₀ = Cubical.Data.Nat；E₀ 的 flag --safe --cubical；E₀⁻ 只有 --cubical。三条证明都算成 tt
------------------------------------------------------------------------
module ToyNode where

open import Cubical.Foundations.Prelude using (Type; _≡_; refl)
open import Cubical.Data.List.Base using (List; []; _∷_)
open import Cubical.Data.Bool.Base using (Bool; true; false; if_then_else_; not; _and_)
open import Cubical.Data.Nat.Base using (ℕ; zero; suc; _+_)
open import Cubical.Data.Sigma using (_×_; _,_; fst; snd; Σ-syntax)
open import Cubical.Data.Maybe.Base using (Maybe; nothing; just)
open import Cubical.Data.Unit.Base using (tt)
open import Agda.Builtin.String using (String; primStringEquality)
open import Env
open import Path using (Path; join)
open import ToyEnv using (natM; safeCubical; backend; W; Script; script; emptyBoard)
open import Keys using (module S)
open import Later using (Run; done; move; module Play; module Traces)
import Node

------------------------------------------------------------------------
-- §1 实例化 Node：E₀ 名单、E₀、E₀⁻；根前缀 "t"
------------------------------------------------------------------------
cubicalOnly : Flags
cubicalOnly = "--cubical" ∷ []

module N = Node (natM ∷ []) safeCubical cubicalOnly tt tt tt
open N using (E⁻; Result; solved; refuted; exhausted; node; embedRun; codeOf; kidOf)

t : Path
t = "t" ∷ []

ixN : ℕ → Ix
ixN q = (E⁻ , q , t) , []

open Traces AgdaSig using (Trace) renaming ([] to ε; _∷_ to _◁_)

play : (d q : ℕ) → Script → Σ[ j ∈ Ix ] (Result × W j × Trace (ixN q) j)
play d q sc = Play.play backend (embedRun (node d q t "X")) (sc , 0 , emptyBoard)

result : (d q : ℕ) → Script → Result
result d q sc = fst (snd (play d q sc))

board : (d q : ℕ) → Script → S.Board
board d q sc = snd (snd (fst (snd (snd (play d q sc)))))

trace : (d q : ℕ) (sc : Script) → Trace (ixN q) (fst (play d q sc))
trace d q sc = snd (snd (snd (play d q sc)))

------------------------------------------------------------------------
-- §2 数棋谱：enter 的次数、ask 的次数、开某个孩子的次数（目标前缀 = s 且不等于当前 realm：排除孩子自己的沙箱 / 粘合）
------------------------------------------------------------------------
enters : {i j : Ix} → Trace i j → ℕ
enters ε                          = 0
enters ((enter _ _ _ , _) ◁ tr)   = suc (enters tr)
enters (_ ◁ tr)                   = enters tr

asks : {i j : Ix} → Trace i j → ℕ
asks ε                     = 0
asks ((ask _ , _) ◁ tr)    = suc (asks tr)
asks (_ ◁ tr)              = asks tr

kidEnters : String → {i j : Ix} → Trace i j → ℕ
kidEnters s ε                              = 0
kidEnters s {i} ((enter _ _ p , _) ◁ tr)   =
  (if primStringEquality (join p) s and not (primStringEquality (join (realmOf i)) s) then 1 else 0) + kidEnters s tr
kidEnters s (_ ◁ tr)                       = kidEnters s tr

------------------------------------------------------------------------
-- §3 答卷（文本内容玩具不看，只有改设计时逐字比对孩子的 spec 两段）
------------------------------------------------------------------------
sheetXY : List (String × String)                   -- 解答：X.agda、XTest.agda
sheetXY = ("X.agda" , "module X where\nopen import Cubical.Data.Nat\ntwice : ℕ → ℕ\ntwice n = n + n\n")
        ∷ ("XTest.agda" , "module XTest where\nopen import X\ntest : twice 3 ≡ 6\ntest = refl\n") ∷ []

stubK testK : String                               -- 孩子 K 的 spec 第一版
stubK = "module K where\nopen import Cubical.Data.Nat\npostulate\n  mul : ℕ → ℕ → ℕ\n"
testK = "module KTest where\nopen import K\npostulate\n  t1 : mul 2 3 ≡ 6\n  t2 : mul 2 3 ≡ 7\n"

stubK′ testK′ : String                             -- 第二版：改了测试
stubK′ = stubK
testK′ = "module KTest where\nopen import K\npostulate\n  t1 : mul 2 3 ≡ 6\n"

sheetDesign : String → String → List (String × String)   -- 分解：根 import K，带 K 的两段 stub
sheetDesign s u = ("X.agda" , "module X where\nopen import K\npow : ℕ → ℕ → ℕ\npow = …\n")
                ∷ ("XTest.agda" , "module XTest where\nopen import X\nopen import KTest\ntest = …\n")
                ∷ ("K.agda" , s) ∷ ("KTest.agda" , u) ∷ []

sheetK : List (String × String)                    -- 孩子 K 的解答
sheetK = ("K.agda" , "module K where\nmul = _·_\n") ∷ ("KTest.agda" , "module KTest where\nt1 = refl\n") ∷ []

sheetKRefute : List (String × String)              -- 孩子 K 的反驳
sheetKRefute = ("KRefute.agda" , "module KRefute where\nopen import K\nopen import KTest\nabsurd : ⊥\nabsurd = …\n") ∷ []

stubA testA : String
stubA = "module A where\npostulate\n  a : ℕ\n"
testA = "module ATest where\nopen import A\npostulate\n  ta : a ≡ 1\n"

stubB testB testB′ : String
stubB  = "module B where\npostulate\n  b : ℕ\n"
testB  = "module BTest where\nopen import B\npostulate\n  tb1 : b ≡ 1\n  tb2 : b ≡ 2\n"
testB′ = "module BTest where\nopen import B\npostulate\n  tb : b ≡ 2\n"

sheetAB : String → List (String × String)         -- 两个孩子 A、B；A 的 spec 两版相同，B 的测试换
sheetAB u = ("X.agda" , "module X where\nopen import A\nopen import B\n") ∷ ("XTest.agda" , "module XTest where\n")
          ∷ ("A.agda" , stubA) ∷ ("ATest.agda" , testA) ∷ ("B.agda" , stubB) ∷ ("BTest.agda" , u) ∷ []

sheetA sheetB sheetBRefute : List (String × String)
sheetA = ("A.agda" , "module A where\na = 1\n") ∷ ("ATest.agda" , "module ATest where\nta = refl\n") ∷ []
sheetB = ("B.agda" , "module B where\nb = 2\n") ∷ ("BTest.agda" , "module BTest where\ntb = refl\n") ∷ []
sheetBRefute = ("BRefute.agda" , "module BRefute where\nabsurd : ⊥\nabsurd = …\n") ∷ []

ifX : Iface
ifX = iface ("X" ∷ []) [] cubicalOnly 0

------------------------------------------------------------------------
-- §4 键
------------------------------------------------------------------------
codeX codeXTest : Path
codeX     = codeOf t "X.agda"
codeXTest = codeOf t "XTest.agda"

kidK kidKTest kidA kidATest kidB kidBTest : Path
kidK     = codeOf (kidOf t "K") "K.agda"
kidKTest = codeOf (kidOf t "K") "KTest.agda"
kidA     = codeOf (kidOf t "A") "A.agda"
kidATest = codeOf (kidOf t "A") "ATest.agda"
kidB     = codeOf (kidOf t "B") "B.agda"
kidBTest = codeOf (kidOf t "B") "BTest.agda"

------------------------------------------------------------------------
-- S1 单节点一轮过：ask → [X.agda, XTest.agda]；fill ×2 → filled 0；沙箱 2 ok；粘合 2 ok
------------------------------------------------------------------------
S1 : Script
S1 = script [] (sheetXY ∷ []) [] []

_ : result 2 4 S1 ≡ solved (codeX ∷ codeXTest ∷ [])
_ = refl

_ : enters (trace 2 4 S1) ≡ 2                      -- 沙箱、粘合
_ = refl

_ : board 2 4 S1 "t/result" ≡ just "solved 2 t/code/X.agda t/code/XTest.agda"
_ = refl

_ : board 2 4 S1 "t/memo/0" ≡ just "quota=4"
_ = refl

------------------------------------------------------------------------
-- S2 一轮没过再过：第一次沙箱第二个 check 回 fail；第二轮全 ok
------------------------------------------------------------------------
S2 : Script
S2 = script (ok ifX ∷ fail [] "boom" ∷ []) (sheetXY ∷ sheetXY ∷ []) [] []

_ : result 2 4 S2 ≡ solved (codeX ∷ codeXTest ∷ [])
_ = refl

_ : board 2 4 S2 "t/verdict/1" ≡ just "boom"          -- fail 的原文
_ = refl

_ : asks (trace 2 4 S2) ≡ 2
_ = refl

------------------------------------------------------------------------
-- S3 分解一个孩子：ask → [X, XTest, K, KTest]；whole ×3；fill → filled 1；洞阶段 4 ok；
--    孩子：ask → [K, KTest]、fill ×2、沙箱、粘合；回来粘合 4 ok
------------------------------------------------------------------------
S3 : Script
S3 = script [] (sheetDesign stubK testK ∷ sheetK ∷ []) (filled 0 ∷ filled 0 ∷ filled 0 ∷ filled 1 ∷ []) []

_ : result 2 4 S3 ≡ solved (kidK ∷ kidKTest ∷ codeX ∷ codeXTest ∷ [])
_ = refl

_ : enters (trace 2 4 S3) ≡ 5                      -- 沙箱、孩子、孩子的沙箱、孩子的粘合、粘合
_ = refl

_ : board 2 4 S3 "t/verdict/1" ≡ just "deferred=1"    -- 洞阶段留下的 postulate 数
_ = refl

_ : board 2 4 S3 "t/kids/K/result" ≡ just "solved 2 t/kids/K/code/K.agda t/kids/K/code/KTest.agda"
_ = refl

_ : board 2 4 S3 "t/kids/K/spec/test" ≡ just testK    -- 父写给孩子的 spec
_ = refl

------------------------------------------------------------------------
-- S4 孩子反驳、父改设计：孩子 ask → [KRefute]；audit true；沙箱 ok → refuted；父 memo；
--    父 ask → 新设计（K 的测试变了）；孩子再跑，这次 solved；粘合
------------------------------------------------------------------------
S4 : Script
S4 = script [] (sheetDesign stubK testK ∷ sheetKRefute ∷ sheetDesign stubK′ testK′ ∷ sheetK ∷ []) [] []

_ : result 2 8 S4 ≡ solved (kidK ∷ kidKTest ∷ codeX ∷ codeXTest ∷ [])
_ = refl

_ : board 2 8 S4 "t/memo/0" ≡ just "quota=8"             -- 父 memo/ 恰 2 行：quota 行 + 反驳行
_ = refl

_ : board 2 8 S4 "t/memo/1" ≡ just "kid K refuted its spec: t/kids/K/code/KRefute.agda"
_ = refl

_ : board 2 8 S4 "t/memo/2" ≡ nothing
_ = refl

_ : board 2 8 S4 "t/kids/K/dropped" ≡ nothing         -- 没有丢弃
_ = refl

_ : board 2 8 S4 "t/kids/K/spec/test" ≡ just testK′   -- spec 是第二版
_ = refl

_ : asks (trace 2 8 S4) ≡ 4                            -- 父 2 次、孩子 2 次
_ = refl

------------------------------------------------------------------------
-- S5 两个孩子一个 keep：A solved；B refuted；父改设计，A 的两段 spec 逐字相同、B 的变了
------------------------------------------------------------------------
S5 : Script
S5 = script [] (sheetAB testB ∷ sheetA ∷ sheetBRefute ∷ sheetAB testB′ ∷ sheetB ∷ []) [] []

_ : result 2 16 S5 ≡ solved (kidA ∷ kidATest ∷ kidB ∷ kidBTest ∷ codeX ∷ codeXTest ∷ [])   -- 清单含 A 的旧清单
_ = refl

_ : kidEnters "t/kids/A" (trace 2 16 S5) ≡ 1        -- A 只被 enter 1 次
_ = refl

_ : kidEnters "t/kids/B" (trace 2 16 S5) ≡ 2        -- B 2 次
_ = refl

_ : board 2 16 S5 "t/kids/A/dropped" ≡ nothing
_ = refl

_ : board 2 16 S5 "t/memo/1" ≡ just "kid B refuted its spec: t/kids/B/code/BRefute.agda"
_ = refl

------------------------------------------------------------------------
-- S6 配额耗尽：配额 1；沙箱 fail
------------------------------------------------------------------------
S6 : Script
S6 = script (fail [] "boom" ∷ []) (sheetXY ∷ []) [] []

_ : result 1 1 S6 ≡ exhausted
_ = refl

_ : board 1 1 S6 "t/result" ≡ just "exhausted"
_ = refl

_ : asks (trace 1 1 S6) ≡ 1
_ = refl
