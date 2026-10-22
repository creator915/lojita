{-# OPTIONS --safe --cubical #-}
------------------------------------------------------------------------
-- ToyEnv.agda —— 用脚本余模型跑一局：check 两个模块、开一个窄的子实例、问一次、回来。全部 refl
--   真后端（agda 进程）和这里的脚本后端住同一个槽（Comodel AgdaSig W）
--   §4 的脚本余模型是"纯手"：不接 Agda 进程，按剧本答每一步；ToyNode 的六局也用它
------------------------------------------------------------------------
module ToyEnv where

open import Cubical.Foundations.Prelude using (Type; _≡_; refl)
open import Cubical.Data.List.Base using (List; []; _∷_; _++_; map; rev)
open import Cubical.Data.Bool.Base using (Bool; true; false; if_then_else_)
open import Cubical.Data.Nat.Base using (ℕ; zero; suc)
open import Cubical.Data.Sigma hiding (Path)
open import Cubical.Data.Maybe.Base using (Maybe; nothing; just)
open import Cubical.Data.Unit.Base using (Unit; tt)
open import Cubical.Data.Sum.Base using (inr)
open import Agda.Builtin.String using (String; primShowNat; primStringToList; primStringFromList)
open import Agda.Builtin.Char using (Char)
open import Syntax
open import Env
open import Path using (join)
open import Keys using (module S)
open import Later using (Run; done; move; Comodel; module Play; module Traces)

------------------------------------------------------------------------
-- §1 手写几个 Code 值（真实运行时它们从 quote 来）
------------------------------------------------------------------------
name : String → Name
name s = Name′ InScope (Id s ∷¹ [])

qn : String → QName
qn s = QName′ (name s)

natQ : QName                                      -- Cubical.Data.Nat
natQ = Qual (name "Cubical") (Qual (name "Data") (qn "Nat"))

natM : ModName
natM = "Cubical" ∷ "Data" ∷ "Nat" ∷ []

noErase : Erased
noErase = NotErased QωInferred

everything : ImportDirective Name Name
everything = ImportDirective′ UseEverything [] [] nothing

openImport : QName → Declaration                  -- open import q
openImport q = Import DoOpen q (inr []) everything

-- {-# OPTIONS fl #-} module m where ds
file : String → List String → List Declaration → Module
file m fl ds = Mod (qn m) (OptionsPragma fl ∷ []) (Module′ noErase (qn m) [] ds ∷ [])

safeCubical : Flags
safeCubical = "--safe" ∷ "--cubical" ∷ []

------------------------------------------------------------------------
-- §2 起点：只看得见 Cubical.Data.Nat，模式 --safe --cubical，配额 3，realm 整张表
------------------------------------------------------------------------
E₀ : Env
E₀ = base (_=ₘ natM) safeCubical

ix₀ : Ix
ix₀ = (E₀ , 3 , []) , []

-- M1 import Nat；头里的两条证明都是算出来的 tt
M1 : Code E₀
M1 = code (header (natM ∷ []) safeCubical tt tt)
          (file "M1" safeCubical (openImport natQ ∷ []))
          tt tt

-- M2 import M1：只有 check M1 过了之后才写得出来（visible 里多了 M1 的接口）。
-- "M1 看得见"取决于接口 i 的名字，i 是跑出来的数据，所以证明在运行时用 mkHeader / mkCode 算：名字对就 just
m2 : Module
m2 = file "M2" safeCubical (openImport (qn "M1") ∷ [])

M2 : (i : Iface) → Maybe (Code (E₀ ▸ i))
M2 i with mkHeader (E₀ ▸ i) (("M1" ∷ []) ∷ []) safeCubical
... | nothing = nothing
... | just h  = mkCode (E₀ ▸ i) h m2

-- 子实例的头：只给它 M1、同样的模式。给 M2 或 Nat 以外的名字、或多开 --guardedness，都造不出来
hKid : (i₁ i₂ : Iface) → Maybe (Header (E₀ ▸ i₁ ▸ i₂))
hKid i₁ i₂ = mkHeader (E₀ ▸ i₁ ▸ i₂) (("M1" ∷ []) ∷ []) safeCubical

------------------------------------------------------------------------
-- §3 程序：check M1 → check M2 → enter（配额 1）→ ask → leave → done（答卷里第一个文件的名字）
------------------------------------------------------------------------
A : Ix → Type
A _ = String

firstFile : List String → String                  -- ask 回 步号 ∷ 文件名表；取第一个文件名
firstFile (_ ∷ f ∷ _) = f
firstFile _           = ""

prog : Run AgdaSig A ix₀
prog = move (check M1) step1
  where
  step4 : (i₁ i₂ : Iface) → Maybe (Header (E₀ ▸ i₁ ▸ i₂)) → Run AgdaSig A ((E₀ ▸ i₁ ▸ i₂ , 3 , []) , [])
  step4 i₁ i₂ nothing  = done "M1 not visible"
  step4 i₁ i₂ (just h) = move (enter h 1 []) λ _ →
                         move (ask (lit "下一步做什么" ∷ [])) λ names →
                         move leave λ _ →
                         done (firstFile names)

  step3 : (i₁ : Iface) (c : Code (E₀ ▸ i₁)) (r : Verdict) → Run AgdaSig A (next {(E₀ ▸ i₁ , 3 , []) , []} (check c) r)
  step3 i₁ c (fail _ m) = done m
  step3 i₁ c (ok i₂)    = step4 i₁ i₂ (hKid i₁ i₂)

  step2 : (i₁ : Iface) → Maybe (Code (E₀ ▸ i₁)) → Run AgdaSig A ((E₀ ▸ i₁ , 3 , []) , [])
  step2 i₁ nothing  = done "M2 rejected"
  step2 i₁ (just c) = move (check c) (step3 i₁ c)

  step1 : (r : Verdict) → Run AgdaSig A (next {ix₀} (check M1) r)
  step1 (fail _ m) = done m
  step1 (ok i₁)    = step2 i₁ (M2 i₁)

------------------------------------------------------------------------
-- §4 脚本余模型：按剧本答，剧本用完按默认答
--   Script  checks      check / checkAt 按序答；用完一律 ok
--           asks        每次 ask 一份答卷：(文件名 , 文本) 的表；用完回只有步号的表（同后端拒收时的回应）
--           transports  transport 按序答；用完一律 filled 0
--           audits      audit 按序答；用完一律 true
--   W = 剧本 × 步号 × 内存里的 Store；键 join 成 "a/x" 存进 S.Board，和后端一致
------------------------------------------------------------------------
record Script : Type where
  constructor script
  field
    checks     : List Verdict
    asks       : List (List (String × String))
    transports : List Filled
    audits     : List Bool

noScript : Script
noScript = script [] [] [] []

W : Ix → Type
W _ = Script × ℕ × S.Board

emptyBoard : S.Board
emptyBoard _ = nothing

w₀ : W ix₀
w₀ = noScript , 0 , emptyBoard

ifaceOf : Module → Iface
ifaceOf m = iface (modNameOf m) [] (optionsOf m) 0

-- 取剧本的头一项；用完给默认值
pop : {A : Type} → List A → A → A × List A
pop []       d = d , []
pop (x ∷ xs) _ = x , xs

-- checkAt 的默认接口：名字取键的最后一段去掉 .agda
lastSeg : Path → String
lastSeg []      = ""
lastSeg (s ∷ p) = go s p
  where
  go : String → Path → String
  go s []      = s
  go _ (t ∷ p) = go t p

dropN : {A : Type} → ℕ → List A → List A
dropN zero    xs       = xs
dropN (suc n) []       = []
dropN (suc n) (_ ∷ xs) = dropN n xs

stripAgda : String → String
stripAgda s = primStringFromList (rev (dropN 5 (rev (primStringToList s))))

-- ask：把答卷的每个文件写到 realm/draft/<步号>/<名字>
writeFiles : Path → List (String × String) → S.Board → S.Board
writeFiles d []             b = b
writeFiles d ((f , t) ∷ fs) b = writeFiles d fs (S.upd (join (d ++ f ∷ [])) (just t) b)

respS : {ix : Ix} → W ix → (o : Op ix) → Σ[ r ∈ Res o ] W (next o r)
respS w (parse _) = nothing , w
respS (sc , n , b) (check c) =
  fst (pop (Script.checks sc) (ok (ifaceOf (body c)))) , (record sc { checks = snd (pop (Script.checks sc) (ok (ifaceOf (body c)))) } , n , b)
respS (sc , n , b) (checkAt h k) =
  fst (pop (Script.checks sc) dflt) , (record sc { checks = snd (pop (Script.checks sc) dflt) } , n , b)
  where dflt = ok (iface (stripAgda (lastSeg k) ∷ []) [] (flags h) 0)
respS w (eval _ _)    = error "scripted" , w
respS w (render _)    = "" , w
respS w (enter _ _ _) = tt , w
respS w leave         = tt , w
respS {ix} (sc , n , b) (ask _) =
  (primShowNat n ∷ map fst sheet) , (record sc { asks = snd (pop (Script.asks sc) []) } , suc n , writeFiles (realmOf ix ++ "draft" ∷ primShowNat n ∷ []) sheet b)
  where sheet = fst (pop (Script.asks sc) [])
respS {ix} w (get k)  = (if isPrefix (realmOf ix) k then snd (snd w) (join k) else nothing) , w   -- restrictL
respS (sc , n , b) (set k v) = tt , (sc , n , S.upd (join k) (just v) b)                          -- 推前，造新版本
respS (sc , n , b) (transport _ t _ d) =                                                           -- 玩具不真拼：board[t] := board[d]
  fst (pop (Script.transports sc) (filled 0)) , (record sc { transports = snd (pop (Script.transports sc) (filled 0)) } , n , S.upd (join t) (b (join d)) b)
respS (sc , n , b) (audit _) =
  fst (pop (Script.audits sc) true) , (record sc { audits = snd (pop (Script.audits sc) true) } , n , b)
respS w (log _)       = tt , w
respS w (sh _)        = (0 , "") , w
respS w (goals _ _)     = noCheck "scripted" , w
respS w (give _ _ _ _)  = rejected "scripted" , w
respS w (split _ _ _ _) = rejected "scripted" , w

backend : Comodel AgdaSig W
backend = record { resp = respS }

------------------------------------------------------------------------
-- §5 跑一局，全部 refl
------------------------------------------------------------------------
open Traces AgdaSig using (Trace) renaming ([] to ε; _∷_ to _◁_)

-- 剧本：没有 check 脚本（一律 ok）；一份答卷，里面一个叫 "yes" 的文件
run : Σ[ j ∈ Ix ] (A j × W j × Trace ix₀ j)
run = Play.play backend prog (script [] ((("yes" , "") ∷ []) ∷ []) [] [] , 0 , emptyBoard)

final : Ix
final = fst run

len : {i j : Ix} → Trace i j → ℕ
len ε       = 0
len (_ ◁ t) = suc (len t)

_ : fst (snd run) ≡ "yes"                               -- LLM 的回答交出来了
_ = refl

_ : visible (envOf final) ("M2" ∷ []) ≡ true            -- 回到父实例：M1、M2 都看得见
_ = refl

_ : visible (envOf final) ("M3" ∷ []) ≡ false
_ = refl

_ : quotaOf final ≡ 2                                   -- 父给了子 1 份配额
_ = refl

_ : len (snd (snd (snd run))) ≡ 5                       -- check、check、enter、ask、leave
_ = refl

-- 答卷落在了子实例的 draft/ 下（步号 0）
_ : snd (snd (fst (snd (snd run)))) "draft/0/yes" ≡ just ""
_ = refl

-- 第三条声明被驳回：环境停在 E₀ ▸ M1，结果是报错原文
run′ : Σ[ j ∈ Ix ] (A j × W j × Trace ix₀ j)
run′ = Play.play backend prog (script (ok (ifaceOf (body M1)) ∷ fail [] "no" ∷ []) [] [] [] , 0 , emptyBoard)

_ : fst (snd run′) ≡ "no"
_ = refl

_ : visible (envOf (fst run′)) ("M2" ∷ []) ≡ false
_ = refl
