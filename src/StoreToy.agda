{-# OPTIONS --safe --cubical #-}
------------------------------------------------------------------------
-- StoreToy.agda —— Store 的程序：同一批程序，两个对手
--   纯对手  ToyEnv.backend：S.world 在内存里答，本文件 §7 全部 refl（验收 A2）
--   真对手  后端 --cubical-handler=store:DIR 在硬盘上答：./store.sh 跑，打印的答案必须和 §7 一样（验收 B）
-- 程序：roundtrip missing overwrite ∣ kidSees kidWrites ∣ persist1 persist2 ∣ commuteXY commuteYX ∣ big ∣ stress
-- 键是路径："a" ∷ "x" ∷ [] 在后端和日志里是 "a/x"；字面量键的前置条件自动算成 tt，不写任何证明（验收 E2）
------------------------------------------------------------------------
module StoreToy where

open import Cubical.Foundations.Prelude using (Type; _≡_; refl)
open import Cubical.Data.List.Base using (List; []; _∷_)
open import Cubical.Data.Nat.Base using (ℕ; zero; suc)
open import Cubical.Data.Bool.Base using (Bool; true; false; if_then_else_)
open import Cubical.Data.Sigma hiding (Path)
open import Cubical.Data.Maybe.Base using (Maybe; nothing; just)
open import Cubical.Data.Unit.Base using (Unit; tt)
open import Agda.Builtin.String using (String; primStringAppend; primStringEquality; primShowNat)
open import Env
open import ToyEnv using (natM; safeCubical; E₀; ix₀; backend; W; emptyBoard; noScript)
open import Later using (Run; done; move; module Play)

M : Ix → Type
M _ = Maybe String

P : Ix → Type
P _ = Maybe String × Maybe String

------------------------------------------------------------------------
-- §1 回环：写后读、读缺席、同键后写赢（B1）
------------------------------------------------------------------------
roundtrip : Run AgdaSig M ix₀
roundtrip = move (set ("a" ∷ "x" ∷ []) "1") λ _ → move (get ("a" ∷ "x" ∷ [])) λ r → done r

missing : Run AgdaSig M ix₀
missing = move (get ("nope" ∷ [])) λ r → done r

overwrite : Run AgdaSig M ix₀
overwrite = move (set ("a" ∷ "x" ∷ []) "1") λ _ → move (set ("a" ∷ "x" ∷ []) "2") λ _ → move (get ("a" ∷ "x" ∷ [])) λ r → done r

------------------------------------------------------------------------
-- §2 子实例：realm "a" ∷ []。看不见 "b" ∷ …（restrictL），写的 "a" ∷ … 回到父实例看得见（mergeL）（B2）
------------------------------------------------------------------------
hA : Header E₀
hA = header (natM ∷ []) safeCubical tt tt

kidSees : Run AgdaSig P ix₀
kidSees = move (set ("a" ∷ "x" ∷ []) "1") λ _ → move (set ("b" ∷ "y" ∷ []) "2") λ _ →
          move (enter hA 1 ("a" ∷ [])) λ _ →
          move (get ("a" ∷ "x" ∷ [])) λ r₁ → move (get ("b" ∷ "y" ∷ [])) λ r₂ →
          move leave λ _ → done (r₁ , r₂)

kidWrites : Run AgdaSig M ix₀
kidWrites = move (enter hA 1 ("a" ∷ [])) λ _ → move (set ("a" ∷ "z" ∷ []) "9") λ _ → move leave λ _ →
            move (get ("a" ∷ "z" ∷ [])) λ r → done r

------------------------------------------------------------------------
-- §3 换进程：persist1 写三个键，persist2 在同一个目录读回来（B3、B4）
------------------------------------------------------------------------
L : Ix → Type
L _ = List (Maybe String)

persist1 : Run AgdaSig M ix₀
persist1 = move (set ("p" ∷ "1" ∷ []) "one") λ _ → move (set ("p" ∷ "2" ∷ []) "two") λ _ → move (set ("p" ∷ "3" ∷ []) "three") λ _ →
           move (get ("p" ∷ "3" ∷ [])) λ r → done r

persist2 : Run AgdaSig L ix₀
persist2 = move (get ("p" ∷ "1" ∷ [])) λ r₁ → move (get ("p" ∷ "2" ∷ [])) λ r₂ → move (get ("p" ∷ "3" ∷ [])) λ r₃ → done (r₁ ∷ r₂ ∷ r₃ ∷ [])

------------------------------------------------------------------------
-- §4 不同键可换：两种写序，快照一样（B5；Agda 侧是 S.upd-comm）
------------------------------------------------------------------------
commuteXY : Run AgdaSig P ix₀
commuteXY = move (set ("a" ∷ "x" ∷ []) "1") λ _ → move (set ("a" ∷ "y" ∷ []) "2") λ _ →
            move (get ("a" ∷ "x" ∷ [])) λ r₁ → move (get ("a" ∷ "y" ∷ [])) λ r₂ → done (r₁ , r₂)

commuteYX : Run AgdaSig P ix₀
commuteYX = move (set ("a" ∷ "y" ∷ []) "2") λ _ → move (set ("a" ∷ "x" ∷ []) "1") λ _ →
            move (get ("a" ∷ "x" ∷ [])) λ r₁ → move (get ("a" ∷ "y" ∷ [])) λ r₂ → done (r₁ , r₂)

------------------------------------------------------------------------
-- §5 大字段：100 × 2¹⁰ = 102400 个字符，写两次（去重），读回来比较（B6）
--   比较用 primStringEquality：大内容不拆成 List Char
------------------------------------------------------------------------
dbl : ℕ → String → String
dbl zero    s = s
dbl (suc n) s = dbl n (primStringAppend s s)

bigVal : String
bigVal = dbl 10 "0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"

eqM : Maybe String → String → Bool
eqM nothing  _ = false
eqM (just r) s = primStringEquality r s

B : Ix → Type
B _ = Bool

big : Run AgdaSig B ix₀
big = move (set ("big" ∷ "x" ∷ []) bigVal) λ _ → move (set ("big" ∷ "x" ∷ []) bigVal) λ _ → move (get ("big" ∷ "x" ∷ [])) λ r → done (eqM r bigVal)

------------------------------------------------------------------------
-- §6 压力：一万次写后读，交出读错的次数（B7：时间、RSS 平直、日志线性）
------------------------------------------------------------------------
C : Ix → Type
C _ = ℕ

key : ℕ → Path
key n = "s" ∷ primShowNat n ∷ []

loop : ℕ → ℕ → Run AgdaSig C ix₀
loop zero    bad = done bad
loop (suc n) bad = move (set (key n) (primShowNat n)) λ _ → move (get (key n)) λ r →
                   tally (eqM r (primShowNat n))
  where
  -- 先按比较结果分支再递归：累加器不会在归约器里积成一万层的 if（懒惰累加器）
  tally : Bool → Run AgdaSig C ix₀
  tally true  = loop n bad
  tally false = loop n (suc bad)

stress : Run AgdaSig C ix₀
stress = loop 10000 0

------------------------------------------------------------------------
-- §7 纯对手上全部 refl（验收 A2）：没有剧本、空盘
------------------------------------------------------------------------
w₀ : W ix₀
w₀ = noScript , 0 , emptyBoard

val : {A : Ix → Type} (p : Run AgdaSig A ix₀) → A (fst (Play.play backend p w₀))
val p = fst (snd (Play.play backend p w₀))

after : {A : Ix → Type} (p : Run AgdaSig A ix₀) → W (fst (Play.play backend p w₀))   -- 跑完后的盘
after p = fst (snd (snd (Play.play backend p w₀)))

_ : val roundtrip ≡ just "1"
_ = refl

_ : val missing ≡ nothing
_ = refl

_ : val overwrite ≡ just "2"
_ = refl

_ : val kidSees ≡ (just "1" , nothing)
_ = refl

_ : val kidWrites ≡ just "9"
_ = refl

-- 换进程 = 把跑完 persist1 的盘交给 persist2
_ : fst (snd (Play.play backend persist2 (after persist1))) ≡ (just "one" ∷ just "two" ∷ just "three" ∷ [])
_ = refl

_ : val commuteXY ≡ val commuteYX
_ = refl

_ : val big ≡ true
_ = refl

_ : val (loop 10 0) ≡ 0
_ = refl
