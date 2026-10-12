{-# OPTIONS --safe --cubical #-}
------------------------------------------------------------------------
-- Store.agda —— 对象层的数据库：底是 schema，上面铺着实例
--   正侧（数据）   实例 Board = 键 ↦ 值；写 = 推前，造一个新版本
--   负侧（观察）   查询 = 快照读；读 = cut，不造版本
--   方块           两条事务何时可换：不同键机器填满，同键留空等证书
--   底箭头         schema 的变化：运输是「选定」的 lens（三条律），不是泛的；
--                  schema 等价时沿路径搬（ua），这才是泛提升
-- 没有公理：schema（键、值、可判定相等）全是模块参数。
------------------------------------------------------------------------
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Univalence
open import Cubical.Relation.Nullary
open import Cubical.Relation.Nullary.Properties
open import Cubical.Data.Maybe
open import Cubical.Data.Bool.Base
open import Cubical.Data.Sigma
open import Cubical.Data.List
open import Cubical.Data.Unit
open import Cubical.Data.Unit.Properties using (isSetUnit)
open import Cubical.Data.Empty renaming (rec to ⊥rec)
open import Game

module Store (K V : Type)
  (_≟_  : Discrete K)        -- 键可判定相等：「两个键是不是同一个」要能算
  (_≟V_ : Discrete V)        -- 值可判定相等：Rebuilder 要比值；顺便给出 isSet
  where

isSetK : isSet K
isSetK = Discrete→isSet _≟_

isSetV : isSet V
isSetV = Discrete→isSet _≟V_

------------------------------------------------------------------------
-- §1 正侧：实例与写
--   一个 schema 上的实例 = 每个键上 0 或 1 个值。没有可变的槽：
--   槽是键，数据是某个实例在键上的取值，变是实例之间的箭头（upd）。
------------------------------------------------------------------------
Board : Type
Board = K → Maybe V                        -- nothing = 键还不在（Σ 缺席当开关）

-- 写一个键：旧查找表外面裹一层补丁，得到一张新表（à la Carte 的 putValue）
upd : K → Maybe V → Board → Board
upd k mv s k′ = decRec (λ _ → mv) (λ _ → s k′) (k ≟ k′)

-- 三条算术：读刚写的键、读别的键、不同键的两次写可换
upd-here : ∀ k mv s → upd k mv s k ≡ mv
upd-here k mv s with k ≟ k
... | yes _  = refl
... | no  ¬p = ⊥rec (¬p refl)

upd-there : ∀ k mv s k′ → ¬ (k ≡ k′) → upd k mv s k′ ≡ s k′
upd-there k mv s k′ ¬p with k ≟ k′
... | yes p = ⊥rec (¬p p)
... | no  _ = refl

upd-comm : ∀ k k′ a b s → ¬ (k ≡ k′)
         → upd k a (upd k′ b s) ≡ upd k′ b (upd k a s)
upd-comm k k′ a b s k≢k′ = funExt pointwise
  where
    pointwise : ∀ j → upd k a (upd k′ b s) j ≡ upd k′ b (upd k a s) j
    pointwise j with k ≟ j | k′ ≟ j
    ... | yes p | yes p′ = ⊥rec (k≢k′ (p ∙ sym p′))
    ... | yes _ | no  _  = refl
    ... | no  _ | yes _  = refl
    ... | no  _ | no  _  = refl

-- 同一个键的两次写：后写赢，前一次被盖掉——这就是同键方块为什么是空心的
upd-same : ∀ k a b s → upd k a (upd k b s) ≡ upd k a s
upd-same k a b s = funExt λ j → lemma j
  where
    lemma : ∀ j → upd k a (upd k b s) j ≡ upd k a s j
    lemma j with k ≟ j
    ... | yes _ = refl
    ... | no  _ = refl

------------------------------------------------------------------------
-- §2 负侧：观察 = 快照查询；一个程序 = 一次 cut
--   读不造版本：许多查询可以对同一个实例同时成立（读并发无冲突）。
--   查询是函数，所以「两次读 = 一次读」「不读就丢掉」免费（文档第四轮的 ? 片段）。
------------------------------------------------------------------------
Query : Type → Type
Query A = Board → A

cut : {B A : Type} → B → (B → A) → A        -- 文档写作 ⟨ s ‖ q ⟩；对任何 schema 的实例都一样
cut s q = q s

------------------------------------------------------------------------
-- §3 世界的签名与余模型（填 Harness 的参数 ②）
--   get k   是一次 cut：回应 Maybe V，实例不动
--   set k v 是一次推前：回应 tt，换一个新实例
------------------------------------------------------------------------
data WOp : Type where
  get : K → WOp
  set : K → V → WOp

WRes : WOp → Type
WRes (get k)   = Maybe V
WRes (set k v) = Unit

WSig : Sig
WSig = record { Op = WOp ; Res = WRes }

world : Board → (o : WOp) → WRes o × Board
world s (get k)   = s k , s
world s (set k v) = tt , upd k (just v) s

isSetBoard : isSet Board
isSetBoard = isSet→ (isOfHLevelMaybe 0 isSetV)

isSetWRes : ∀ o → isSet (WRes o)
isSetWRes (get k)   = isOfHLevelMaybe 0 isSetV
isSetWRes (set k v) = isSetUnit

-- 读不改实例；写了别的键，读到的还是原来的值（回应层面的独立性）
get-pure : ∀ s k → snd (world s (get k)) ≡ s
get-pure s k = refl

read-indep : ∀ s k k′ v → ¬ (k ≡ k′)
           → fst (world (snd (world s (set k′ v))) (get k)) ≡ fst (world s (get k))
read-indep s k k′ v k≢k′ = upd-there k′ (just v) s k (λ q → k≢k′ (sym q))

------------------------------------------------------------------------
-- §4 方块：两条事务先后可换
--   Filled 是「这个方块填满了」这个**类型**（文档：泛性质写成类型，不写成答案）。
--   fill-indep 是机器填的默认元素：两两不写同一个键。
--   同键的证书（两次 +1 可换、带条件的可换）由提供者 / LLM 写，Agda 查；
--   没有证书的方块是空心的：排队，或者选一种合并填上（decisions 2）。
------------------------------------------------------------------------
Tx : Type                                   -- 一条事务 = 一列步（只看它对实例做什么）
Tx = List WOp

step : WOp → Board → Board
step o s = snd (world s o)

runTx : Tx → Board → Board
runTx []       s = s
runTx (o ∷ os) s = runTx os (step o s)

Filled : Tx → Tx → Type
Filled t₁ t₂ = ∀ s → runTx (t₁ ++ t₂) s ≡ runTx (t₂ ++ t₁) s

-- 两步独立：读和谁都换；写和写要键不同
Indep : WOp → WOp → Type
Indep (set k _) (set k′ _) = ¬ (k ≡ k′)
Indep _         _          = Unit

-- 一步的小方块
step-comm : ∀ a b → Indep a b → ∀ s → step b (step a s) ≡ step a (step b s)
step-comm (get k)   (get k′)    _    s = refl
step-comm (get k)   (set k′ v′) _    s = refl
step-comm (set k v) (get k′)    _    s = refl
step-comm (set k v) (set k′ v′) k≢k′ s =
  upd-comm k′ k (just v′) (just v) s (λ p → k≢k′ (sym p))

-- 一步对一列、一列对一列：两两独立
IndepAll : WOp → Tx → Type
IndepAll a []       = Unit
IndepAll a (b ∷ bs) = Indep a b × IndepAll a bs

IndepTx : Tx → Tx → Type
IndepTx []       t = Unit
IndepTx (a ∷ as) t = IndepAll a t × IndepTx as t

runTx-++ : ∀ t₁ t₂ s → runTx (t₁ ++ t₂) s ≡ runTx t₂ (runTx t₁ s)
runTx-++ []       t₂ s = refl
runTx-++ (a ∷ as) t₂ s = runTx-++ as t₂ (step a s)

-- 一步穿过一列独立的步
step-tx : ∀ a t → IndepAll a t → ∀ s → runTx t (step a s) ≡ step a (runTx t s)
step-tx a []       _          s = refl
step-tx a (b ∷ bs) (ab , abs) s =
  cong (runTx bs) (step-comm a b ab s) ∙ step-tx a bs abs (step b s)

-- 小方块拼成大方块（Mazurkiewicz 迹：相邻交换生成全部交错）
tx-comm : ∀ t₁ t₂ → IndepTx t₁ t₂ → ∀ s → runTx t₂ (runTx t₁ s) ≡ runTx t₁ (runTx t₂ s)
tx-comm []       t₂ _          s = refl
tx-comm (a ∷ as) t₂ (ia , ias) s =
  tx-comm as t₂ ias (step a s) ∙ cong (runTx as) (step-tx a t₂ ia s)

fill-indep : ∀ t₁ t₂ → IndepTx t₁ t₂ → Filled t₁ t₂
fill-indep t₁ t₂ ind s =
  runTx-++ t₁ t₂ s ∙ tx-comm t₁ t₂ ind s ∙ sym (runTx-++ t₂ t₁ s)

------------------------------------------------------------------------
-- §5 底箭头之一：子 schema（realm）与选定提升
--   底上一根箭头：子 schema K∣R ↪ K。上面的运输是一个 lens（delta lens）：
--   view 把实例限制到子 schema（观察沿箭头拉回），update 把子实例写回父实例
--   （数据沿箭头推前）。它不是泛的，是选定的；合法 = 三条律，机器证。
------------------------------------------------------------------------
record Lens (A B : Type) : Type where
  field
    view   : A → B                         -- f*：拉回。B 上问的问题，翻译成 A 上的
    update : A → B → A                     -- f_!：推前。B 上的新版本写回到 A 的版本上
    GetPut : ∀ a → update a (view a) ≡ a             -- 没改就原样（撤销 = 对着旧版本写回）
    PutGet : ∀ a b → view (update a b) ≡ b           -- 写回之后能看到
    PutPut : ∀ a b b′ → update (update a b) b′ ≡ update a b′   -- 复合提升到复合
open Lens public

module Realm (R : K → Type) (decR : ∀ k → Dec (R k)) (propR : ∀ k → isProp (R k)) where

  K∣R : Type                               -- 子 schema 的键
  K∣R = Σ[ k ∈ K ] R k

  Board∣R : Type                           -- 子 schema 上的实例
  Board∣R = K∣R → Maybe V

  restrict : Board → Board∣R
  restrict s (k , _) = s k

  merge : Board → Board∣R → Board           -- R 内取子实例，R 外取父实例
  merge s t k = decRec (λ r → t (k , r)) (λ _ → s k) (decR k)

  realm : Lens Board Board∣R
  view   realm = restrict
  update realm = merge
  GetPut realm s = funExt λ k → lemma k
    where
      lemma : ∀ k → merge s (restrict s) k ≡ s k
      lemma k with decR k
      ... | yes _ = refl
      ... | no  _ = refl
  PutGet realm s t = funExt λ { (k , r) → lemma k r }
    where
      lemma : ∀ k r → merge s t k ≡ t (k , r)
      lemma k r with decR k
      ... | yes r′ = cong (λ x → t (k , x)) (propR k r′ r)
      ... | no  ¬r = ⊥rec (¬r r)
  PutPut realm s t t′ = funExt λ k → lemma k
    where
      lemma : ∀ k → merge (merge s t) t′ k ≡ merge s t′ k
      lemma k with decR k
      ... | yes _ = refl
      ... | no  _ = refl

  -- 限制：孩子碰不到 R 外的键——由运输本身保证，不是谓词、不是类型
  confine : ∀ s t k → ¬ R k → merge s t k ≡ s k
  confine s t k ¬r with decR k
  ... | yes r = ⊥rec (¬r r)
  ... | no  _ = refl

  -- 观察沿箭头拉回：子 schema 上的查询，翻译成父 schema 上的（免费的那种：接在 view 后面）
  pull : {A : Type} → (Board∣R → A) → Query A
  pull q s = q (restrict s)

  -- 握手律 ⟨ f_! s ‖ q ⟩ ≡ ⟨ s ‖ f* q ⟩，在这个免费版本里是定义本身
  handshake : {A : Type} (s : Board) (q : Board∣R → A) → cut (restrict s) q ≡ cut s (pull q)
  handshake s q = refl

------------------------------------------------------------------------
-- §6 底箭头之二：schema 的等价，沿路径搬运（想法 9）
--   两个 schema 等价（改名、换编码），实例类型之间就有一条路径（ua），
--   沿它 transport 就是泛提升——不用选，Agda 自己算；你的后端能把它跑出来。
--   定理 carry-is：算出来恰是按等价重索引。
------------------------------------------------------------------------
module Rename (K′ : Type) (e : K ≃ K′) where

  Board′ : Type
  Board′ = K′ → Maybe V

  path : Board ≡ Board′
  path i = ua e i → Maybe V

  carry : Board → Board′
  carry = transport path

  carry-is : ∀ s k′ → carry s k′ ≡ s (invEq e k′)
  carry-is s k′ =
      transportRefl (s (transport (sym (ua e)) k′))
    ∙ cong s (cong (λ p → transport p k′) (sym (uaInvEquiv e)) ∙ uaβ (invEquiv e) k′)

------------------------------------------------------------------------
-- §7 给 Harness 的运输（参数 ④）：同一个 Board 类型上的 restrict / merge
--   运输是数据：whole（孩子拿整张表）、realm R（孩子只看见 R，R 外是 nothing；只写回 R）
--   它是 §5 那个 lens 换个皮：子实例嵌回同一个 Board 类型里。律照样成立。
------------------------------------------------------------------------
data Lifting : Type where
  whole : Lifting
  realm : (K → Bool) → Lifting

restrictL : Lifting → Board → Board
restrictL whole     s   = s
restrictL (realm R) s k = if R k then s k else nothing

mergeL : Lifting → Board → Board → Board
mergeL whole     s t   = t
mergeL (realm R) s t k = if R k then t k else s k

-- 没改就原样（GetPut）；复合提升到复合（PutPut）；写回之后能看到（PutGet，在 R 上）
GetPutL : ∀ l s → mergeL l s (restrictL l s) ≡ s
GetPutL whole     s = refl
GetPutL (realm R) s = funExt λ k → lemma k
  where
    lemma : ∀ k → mergeL (realm R) s (restrictL (realm R) s) k ≡ s k
    lemma k with R k
    ... | true  = refl
    ... | false = refl

PutPutL : ∀ l s t t′ → mergeL l (mergeL l s t) t′ ≡ mergeL l s t′
PutPutL whole     s t t′ = refl
PutPutL (realm R) s t t′ = funExt λ k → lemma k
  where
    lemma : ∀ k → mergeL (realm R) (mergeL (realm R) s t) t′ k ≡ mergeL (realm R) s t′ k
    lemma k with R k
    ... | true  = refl
    ... | false = refl

PutGetL : ∀ l s t → restrictL l (mergeL l s t) ≡ restrictL l t
PutGetL whole     s t = refl
PutGetL (realm R) s t = funExt λ k → lemma k
  where
    lemma : ∀ k → restrictL (realm R) (mergeL (realm R) s t) k ≡ restrictL (realm R) t k
    lemma k with R k
    ... | true  = refl
    ... | false = refl

-- 限制：R 外的键，孩子看不见（nothing）也改不动（父的值原样）
confineL : ∀ R s t k → R k ≡ false → (restrictL (realm R) s k ≡ nothing) × (mergeL (realm R) s t k ≡ s k)
confineL R s t k e = subst (λ b → (if b then s k else nothing) ≡ nothing) (sym e) refl
                   , subst (λ b → (if b then t k else s k) ≡ s k) (sym e) refl
