{-# OPTIONS --safe --cubical #-}
------------------------------------------------------------------------
-- DriveToy.agda —— 真后端跑一局（agda-cubical-run.v6 --cubical-drive=…）
--   prog   parse 一段文本 → check → eval 里面的函数（twice 3 → 6）
--   bad    同一流程，但模块有类型错：check 驳回，拿到报错原文和树上的路径
--   kid    check 过 M1 之后开一个只看得见 M1 的子实例（realm 是路径 []），问一次 LLM，回来交出文件名表
-- 用脚本余模型（ToyEnv）跑不了 parse/eval 的真结果，所以这三个只在真后端上跑：./drive.sh
------------------------------------------------------------------------
module DriveToy where

open import Cubical.Foundations.Prelude using (Type)
open import Cubical.Data.List.Base using (List; []; _∷_)
open import Cubical.Data.Nat.Base using (ℕ; zero; suc; _+_)
open import Cubical.Data.Int.Base using (pos)
open import Cubical.Data.Sigma hiding (Path)
open import Cubical.Data.Maybe.Base using (Maybe; nothing; just)
open import Agda.Builtin.String using (String)
open import Syntax
open import Env
open import Later using (Run; done; move)
open import ToyEnv using (qn; natM; safeCubical; E₀; ix₀)

------------------------------------------------------------------------
-- §1 LLM 写的文本（这里是常量；真实运行时从 ask 来）
------------------------------------------------------------------------
src1 : String
src1 = "{-# OPTIONS --safe --cubical #-}\nmodule M1 where\nopen import Cubical.Data.Nat\n\ntwice : ℕ → ℕ\ntwice n = n + n\n"

srcBad : String
srcBad = "{-# OPTIONS --safe --cubical #-}\nmodule M1 where\nopen import Cubical.Data.Nat\n\ntwice : ℕ → ℕ\ntwice n = n + twice\n"

twice3 : Expr                                     -- twice 3
twice3 = RawApp (List2′ (Ident (qn "twice")) (Lit (LitNat (pos 3))) [])

A : Ix → Type
A _ = Answer

------------------------------------------------------------------------
-- §2 parse → check → eval
------------------------------------------------------------------------
module Flow (src : String) where
  prog : Run AgdaSig A ix₀
  prog = move (parse src) step1
    where
    step5 : (c : Code E₀) (i : Iface) → Maybe (Header (E₀ ▸ i)) → Run AgdaSig A ((E₀ ▸ i , 3 , []) , [])
    step5 c i nothing  = done (error "M1 not visible")
    step5 c i (just h) = move (eval h twice3) λ a → done a

    step4 : (c : Code E₀) (r : Verdict) → Run AgdaSig A (next {ix₀} (check c) r)
    step4 c (fail _ msg) = done (error msg)
    step4 c (ok i)       = step5 c i (mkHeader (E₀ ▸ i) (("M1" ∷ []) ∷ []) safeCubical)

    step3 : Maybe (Code E₀) → Run AgdaSig A ix₀
    step3 nothing  = done (error "module name not fresh, or OPTIONS wider than the header")
    step3 (just c) = move (check c) (step4 c)

    step2 : Maybe (Header E₀) → Module → Run AgdaSig A ix₀
    step2 nothing  m = done (error "header rejected")
    step2 (just h) m = step3 (mkCode E₀ h m)

    step1 : Maybe Module → Run AgdaSig A ix₀
    step1 nothing  = done (error "parse failed")
    step1 (just m) = step2 (mkHeader E₀ (natM ∷ []) safeCubical) m

prog : Run AgdaSig A ix₀
prog = Flow.prog src1

bad : Run AgdaSig A ix₀
bad = Flow.prog srcBad

------------------------------------------------------------------------
-- §3 check → enter（只给 M1，配额 1）→ ask → leave → 交出 ask 的回应（步号 ∷ 文件名）
------------------------------------------------------------------------
S : Ix → Type
S _ = List String                                 -- ask 的回应：步号 ∷ 答卷拆出的文件名

kid : Run AgdaSig S ix₀
kid = move (parse src1) step1
  where
  step4 : (c : Code E₀) (i : Iface) → Maybe (Header (E₀ ▸ i)) → Run AgdaSig S ((E₀ ▸ i , 3 , []) , [])
  step4 c i nothing  = done ("M1 not visible" ∷ [])
  step4 c i (just h) = move (enter h 1 []) λ _ → move (ask (lit "下一步做什么" ∷ [])) λ a → move leave λ _ → done a
  step3 : (c : Code E₀) (r : Verdict) → Run AgdaSig S (next {ix₀} (check c) r)
  step3 c (fail _ msg) = done (msg ∷ [])
  step3 c (ok i)       = step4 c i (mkHeader (E₀ ▸ i) (("M1" ∷ []) ∷ []) safeCubical)
  step2 : Maybe (Header E₀) → Module → Run AgdaSig S ix₀
  step2 nothing  m = done ("header rejected" ∷ [])
  step2 (just h) m with mkCode E₀ h m
  ... | nothing = done ("module rejected" ∷ [])
  ... | just c  = move (check c) (step3 c)
  step1 : Maybe Module → Run AgdaSig S ix₀
  step1 nothing  = done ("parse failed" ∷ [])
  step1 (just m) = step2 (mkHeader E₀ (natM ∷ []) safeCubical) m

------------------------------------------------------------------------
-- §4 只看判决：A = Verdict。接口（导出名与类型）长什么样，头里没写的 import 怎么被驳回
------------------------------------------------------------------------
V : Ix → Type
V _ = Verdict

-- 在环境 E（配额 q）下：parse → 造头 → 造 Code → check → 交出判决
module CheckOne (E : Env) (q : ℕ) (src : String) (is : List ModName) (fl : Flags) where
  ix : Ix
  ix = (E , q , []) , []

  run : Run AgdaSig V ix
  run = move (parse src) step1
    where
    step3 : (c : Code E) (r : Verdict) → Run AgdaSig V (next {ix} (check c) r)
    step3 c r = done r

    step2 : Maybe (Header E) → Module → Run AgdaSig V ix
    step2 nothing  m = done (fail [] "header rejected")
    step2 (just h) m with mkCode E h m
    ... | nothing = done (fail [] "module rejected")
    ... | just c  = move (check c) (step3 c)

    step1 : Maybe Module → Run AgdaSig V ix
    step1 nothing  = done (fail [] "parse failed")
    step1 (just m) = step2 (mkHeader E is fl) m

showIface : Run AgdaSig V ix₀                     -- ok (iface ["M1"] (("twice" , ℕ → ℕ) ∷ []) … hash)
showIface = CheckOne.run E₀ 3 src1 (natM ∷ []) safeCubical

srcUndeclared : String                            -- 文本里多 import 了 Bool，头里只给了 Nat
srcUndeclared = "{-# OPTIONS --safe --cubical #-}\nmodule M1 where\nopen import Cubical.Data.Nat\nopen import Cubical.Data.Bool\n\nb : Bool\nb = true\n"

undeclared : Run AgdaSig V ix₀                    -- fail [] "imports not in the header: Cubical.Data.Bool"
undeclared = CheckOne.run E₀ 3 srcUndeclared (natM ∷ []) safeCubical

------------------------------------------------------------------------
-- §5 两个虚拟模块：M2 import M1（M1 是这局里刚 check 过的），再 eval M2 里的 four
------------------------------------------------------------------------
srcM2 : String
srcM2 = "{-# OPTIONS --safe --cubical #-}\nmodule M2 where\nopen import Cubical.Data.Nat\nopen import M1\n\nfour : ℕ\nfour = twice 2\n"

chain : Run AgdaSig A ix₀                         -- value (Lit (LitNat (pos 4)))
chain = move (parse src1) step1
  where
  E₁ : (c : Code E₀) (i : Iface) → Env
  E₁ c i = E₀ ▸ i

  step6 : (c : Code E₀) (i : Iface) (c₂ : Code (E₁ c i)) (i₂ : Iface)
        → Maybe (Header (E₁ c i ▸ i₂)) → Run AgdaSig A ((E₁ c i ▸ i₂ , 3 , []) , [])
  step6 c i c₂ i₂ nothing  = done (error "M2 not visible")
  step6 c i c₂ i₂ (just h) = move (eval h (Ident (qn "four"))) λ a → done a

  step5 : (c : Code E₀) (i : Iface) (c₂ : Code (E₁ c i)) (r : Verdict)
        → Run AgdaSig A (next {(E₁ c i , 3 , []) , []} (check c₂) r)
  step5 c i c₂ (fail _ msg) = done (error msg)
  step5 c i c₂ (ok i₂)      = step6 c i c₂ i₂ (mkHeader (E₁ c i ▸ i₂) (("M2" ∷ []) ∷ []) safeCubical)

  step4 : (c : Code E₀) (i : Iface) → Maybe Module → Run AgdaSig A ((E₁ c i , 3 , []) , [])
  step4 c i nothing   = done (error "parse failed")
  step4 c i (just m₂) with mkHeader (E₁ c i) (natM ∷ ("M1" ∷ []) ∷ []) safeCubical
  ... | nothing = done (error "header rejected")
  ... | just h with mkCode (E₁ c i) h m₂
  ...   | nothing = done (error "M2 rejected")
  ...   | just c₂ = move (check c₂) (step5 c i c₂)

  step3 : (c : Code E₀) (r : Verdict) → Run AgdaSig A (next {ix₀} (check c) r)
  step3 c (fail _ msg) = done (error msg)
  step3 c (ok i)       = move (parse srcM2) (step4 c i)

  step2 : Maybe (Header E₀) → Module → Run AgdaSig A ix₀
  step2 nothing  m = done (error "header rejected")
  step2 (just h) m with mkCode E₀ h m
  ... | nothing = done (error "M1 rejected")
  ... | just c  = move (check c) (step3 c)

  step1 : Maybe Module → Run AgdaSig A ix₀
  step1 nothing  = done (error "parse failed")
  step1 (just m) = step2 (mkHeader E₀ (natM ∷ []) safeCubical) m

------------------------------------------------------------------------
-- §6 机制兜底策略：父实例不 --safe，所以策略允许子模块不 --safe；
--    U 有 postulate，S 是 --safe 的、import U：Agda 自己的 CoInfectiveImport 驳回 S
------------------------------------------------------------------------
E₂ : Env
E₂ = base (_=ₘ natM) ("--cubical" ∷ [])

srcU : String
srcU = "{-# OPTIONS --cubical #-}\nmodule U where\npostulate\n  magic : Set\n"

srcS : String
srcS = "{-# OPTIONS --safe --cubical #-}\nmodule S where\nopen import U\n"

coinf : Run AgdaSig V ((E₂ , 3 , []) , [])            -- fail … CoInfectiveImport
coinf = move (parse srcU) step1
  where
  step3 : (c : Code E₂) (r : Verdict) → Run AgdaSig V (next {(E₂ , 3 , []) , []} (check c) r)
  step3 c (fail p msg) = done (fail p msg)
  step3 c (ok i)       = CheckOne.run (E₂ ▸ i) 3 srcS (("U" ∷ []) ∷ []) safeCubical

  step2 : Maybe (Header E₂) → Module → Run AgdaSig V ((E₂ , 3 , []) , [])
  step2 nothing  m = done (fail [] "header rejected")
  step2 (just h) m with mkCode E₂ h m
  ... | nothing = done (fail [] "U rejected")
  ... | just c  = move (check c) (step3 c)

  step1 : Maybe Module → Run AgdaSig V ((E₂ , 3 , []) , [])
  step1 nothing  = done (fail [] "parse failed")
  step1 (just m) = step2 (mkHeader E₂ [] ("--cubical" ∷ [])) m

------------------------------------------------------------------------
-- §7 注释是声明序列里的节点：parse 从 token 流把它们按位置挂上（check 前剥掉）
------------------------------------------------------------------------
srcC : String
srcC = "-- 文件头\n{-# OPTIONS --safe --cubical #-}\nmodule M3 where\n-- 导入\nopen import Cubical.Data.Nat\n\n{- 两倍 -}\ntwice : ℕ → ℕ\ntwice n = n + n  -- 行尾\n"

countComments : List Declaration → ℕ
countComments []                          = 0
countComments (Comment _ ∷ ds)            = suc (countComments ds)
countComments (Module′ _ _ _ inner ∷ ds)  = countComments inner + countComments ds
countComments (_ ∷ ds)                    = countComments ds

N : Ix → Type
N _ = ℕ

comments : Run AgdaSig N ix₀                      -- 4：文件头、导入、两倍、行尾
comments = move (parse srcC) λ { nothing → done 0 ; (just (Mod _ _ ds)) → done (countComments ds) }

------------------------------------------------------------------------
-- §8 编辑器：洞是 Agda 自己的 ?。goals 列出洞，give 填洞，split 分情况；改过的树下一拍再 check
------------------------------------------------------------------------
srcHole : String
srcHole = "{-# OPTIONS --safe --cubical #-}\nmodule M4 where\nopen import Cubical.Data.Nat\n\ntwice : ℕ → ℕ\ntwice n = ?\n"

G : Ix → Type
G _ = Goals

-- 在 E₀ 下 parse 一段带洞的文本、造头，然后交给 k
module WithHole (src : String) {R : Ix → Type} (k : Header E₀ → Module → Run AgdaSig R ix₀) (bad : String → R ix₀) where
  run : Run AgdaSig R ix₀
  run = move (parse src) step1
    where
    step2 : Maybe (Header E₀) → Module → Run AgdaSig R ix₀
    step2 nothing  m = done (bad "header rejected")
    step2 (just h) m = k h m
    step1 : Maybe Module → Run AgdaSig R ix₀
    step1 nothing  = done (bad "parse failed")
    step1 (just m) = step2 (mkHeader E₀ (natM ∷ []) safeCubical) m

showGoals : Run AgdaSig G ix₀                     -- holes ((goal 0 路径 ℕ) ∷ [])
showGoals = WithHole.run srcHole (λ h m → move (goals h m) λ g → done g) noCheck

nPlusN : Expr                                     -- n + n
nPlusN = RawApp (List2′ (Ident (qn "n")) (Ident (qn "+")) (Ident (qn "n") ∷ []))

-- give 填好洞 → check 填好的模块 → eval twice 3
fillHole : Run AgdaSig A ix₀                      -- value (Lit (LitNat (pos 6)))
fillHole = WithHole.run srcHole step error
  where
  step4 : (h : Header E₀) (c : Code E₀) (i : Iface) → Maybe (Header (E₀ ▸ i)) → Run AgdaSig A ((E₀ ▸ i , 3 , []) , [])
  step4 h c i nothing   = done (error "M4 not visible")
  step4 h c i (just h′) = move (eval h′ twice3) λ a → done a
  step3 : (h : Header E₀) (c : Code E₀) (r : Verdict) → Run AgdaSig A (next {ix₀} (check c) r)
  step3 h c (fail _ msg) = done (error msg)
  step3 h c (ok i)       = step4 h c i (mkHeader (E₀ ▸ i) (("M4" ∷ []) ∷ []) safeCubical)
  step2 : Header E₀ → Edit → Run AgdaSig A ix₀
  step2 h (rejected msg) = done (error msg)
  step2 h (edited m′) with mkCode E₀ h m′
  ... | nothing = done (error "edited module rejected")
  ... | just c  = move (check c) (step3 h c)
  step : Header E₀ → Module → Run AgdaSig A ix₀
  step h m = move (give h m 0 nPlusN) (step2 h)

-- split 在洞 0 按 n 分情况，再列洞：两个
splitN : Run AgdaSig G ix₀                        -- holes (两个 goal)
splitN = WithHole.run srcHole (λ h m → move (split h m 0 "n") λ { (rejected s) → done (noCheck s) ; (edited m′) → move (goals h m′) λ g → done g }) noCheck

------------------------------------------------------------------------
-- §9 扩展 λ 里的洞也能分情况：新子句接回 λ { … } 的分支表
------------------------------------------------------------------------
srcLam : String
srcLam = "{-# OPTIONS --safe --cubical #-}\nmodule M5 where\nopen import Cubical.Data.Nat\n\ng : ℕ → ℕ\ng = λ { n → ? }\n"

splitLam : Run AgdaSig G ix₀                      -- holes (两个)
splitLam = WithHole.run srcLam (λ h m → move (split h m 0 "n") λ { (rejected s) → done (noCheck s) ; (edited m′) → move (goals h m′) λ g → done g }) noCheck
