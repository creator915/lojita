{-# OPTIONS --safe --cubical #-}
------------------------------------------------------------------------
-- ToyStore.agda —— 让整套系统在键值数据库上跑一局，再把槽里的东西逐个换掉
--   schema：键 = {x, y}，值 = ℕ。根读 x、给 x 加数、把活交给叶子；叶子读 x 写 y。
--   §7  真对手 + whole 运输 + 默认执行者：棋谱、终局全由 refl 算出
--   §8  方块：填满 / 空心           §9  子 schema 的 lens        §10 沿 ua 搬运
--   §11 换运输：叶子只看见 y         §12 换对手：录音回放（Rebuilder）、录音失效
------------------------------------------------------------------------
module ToyStore where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Relation.Nullary
open import Cubical.Data.Nat
open import Cubical.Data.Nat.Properties using (discreteℕ ; isSetℕ ; snotz ; injSuc)
open import Cubical.Data.Bool.Base
open import Cubical.Data.Maybe
open import Cubical.Data.Maybe.Properties using (just-inj)
open import Cubical.Data.Sigma
open import Cubical.Data.Unit
open import Cubical.Data.Empty
open import Cubical.Data.List
open import Game
open import PathCat using (Category ; module Build)

------------------------------------------------------------------------
-- 1 schema：两个键（固定词汇）
------------------------------------------------------------------------
data Key : Type where
  kx ky : Key

isX : Key → Type
isX kx = Unit
isX ky = ⊥

_≟K_ : Discrete Key
kx ≟K kx = yes refl
ky ≟K ky = yes refl
kx ≟K ky = no λ p → subst isX p tt
ky ≟K kx = no λ p → subst isX (sym p) tt

kx≢ky : ¬ (kx ≡ ky)
kx≢ky p = subst isX p tt

------------------------------------------------------------------------
-- 2 装上数据库
------------------------------------------------------------------------
import Store
module DB = Store Key ℕ _≟K_ discreteℕ
open DB

------------------------------------------------------------------------
-- 3 预言机：脚本 LLM。问它（Q = Unit），按脚本吐一条命令（A = Cmd）
------------------------------------------------------------------------
data Cmd : Type where
  addX!     : ℕ → Cmd
  delegate! : Cmd
  stop!     : Cmd

OState : Type
OState = List Cmd

oracleF : OState → (o : Unit) → Unit → Cmd × OState
oracleF []       _ _ = stop! , []
oracleF (c ∷ cs) _ _ = c , cs

------------------------------------------------------------------------
-- 4 装上 Harness：① 预言机 ② 世界 = Store ③ Spec/Report ④ 运输 = Store 的 whole / realm
------------------------------------------------------------------------
import Harness
module H = Harness
  Unit (λ _ → Unit) (λ _ → Cmd) OState oracleF
  WSig Board isSetBoard isSetWRes world
  ℕ ℕ
  Lifting restrictL mergeL
open H

------------------------------------------------------------------------
-- 5 工具 = 对象层的程序（一列事务）
------------------------------------------------------------------------
rd : Key → Free WSig (Maybe ℕ)
rd k = move (get k) done

wr : Key → ℕ → Free WSig Unit
wr k v = move (set k v) done

val : Maybe ℕ → ℕ
val nothing  = 0
val (just n) = n

data RTool : Type where
  incX : RTool

RCall RResult : RTool → Type
RCall   incX = ℕ
RResult incX = ℕ

rimpl : (t : RTool) → RCall t → Free WSig (RResult t)
rimpl incX n = rd kx >>= λ mx → let nx = val mx + n in wr kx nx >>= λ _ → done nx

Rroot : Rules
Rroot = record { Tool = RTool ; Call = RCall ; Result = RResult
               ; isSetResult = λ { incX → isSetℕ } ; impl = rimpl }

data LTool : Type where
  copyXY : LTool

LCall LResult : LTool → Type
LCall   copyXY = Unit
LResult copyXY = ℕ

limpl : (t : LTool) → LCall t → Free WSig (LResult t)
limpl copyXY _ = rd kx >>= λ mx → let n = val mx in wr ky n >>= λ _ → done n

Rleaf : Rules
Rleaf = record { Tool = LTool ; Call = LCall ; Result = LResult
               ; isSetResult = λ { copyXY → isSetℕ } ; impl = limpl }

------------------------------------------------------------------------
-- 6 配置树（边上带运输）与策略树
------------------------------------------------------------------------
leaf : Config
leaf = node Rleaf ⊥ (λ ()) (λ ())

root : Config                                  -- 叶子拿整张表
root = node Rroot Unit (λ _ → leaf) (λ _ → whole)

rcheck : Cmd → Maybe (Act Rroot Unit)
rcheck (addX! n) = just (run incX n)
rcheck delegate! = just (sub tt 0)
rcheck stop!     = nothing

-- 根程序：预算内反复「问 → check → 走」（同一段程序也给下面换了运输的 root′ 用）
rootProg : (x : Config) → (Cmd → Maybe (Op (Sig-of x))) → ℕ → ℕ → Free (Sig-of x) ℕ
rootProg x chk zero sp = done 0
rootProg (node r Kids kid lf) chk (suc f) sp = move (ask tt tt) λ c → next (chk c)
  where
    next : Maybe (Act r Kids) → Free (Sig-of (node r Kids kid lf)) ℕ
    next nothing  = done 0
    next (just m) = move m λ _ → rootProg (node r Kids kid lf) chk f sp

leafProg : ℕ → Free (Sig-of leaf) ℕ
leafProg sp = move (run copyXY tt) λ n → done n

stratLeaf : Strat leaf
stratLeaf = record { prog = leafProg ; kids = λ () }

stratRoot : Strat root
stratRoot = record { prog = rootProg root rcheck 8 ; kids = λ _ → stratLeaf }

------------------------------------------------------------------------
-- 7 跑一局：上下文的其余部分 X = Unit（资源账的位子，先空着），执行者 = 默认 play
------------------------------------------------------------------------
module D = Dynamics Unit (λ x _ → x) (λ x _ → x) playExec
open D

script : OState
script = addX! 2 ∷ delegate! ∷ addX! 3 ∷ stop! ∷ []

b0 : Board
b0 = λ _ → nothing

w0 : W
w0 = script , b0 , tt

result : Position root b0
result = finish root stratRoot (prog stratRoot 0) w0

finalBoard : Board
finalBoard = fst result

theTrace : Trace (Sig-of root)
theTrace = fst (snd result)

final-x : finalBoard kx ≡ just 5
final-x = refl

final-y : finalBoard ky ≡ just 2
final-y = refl

expected : Trace (Sig-of root)
expected =
    (ask tt tt  , addX! 2)
  ∷ (run incX 2 , 2)
  ∷ (ask tt tt  , delegate!)
  ∷ (sub tt 0   , (2 , (run copyXY tt , 2) ∷ []))
  ∷ (ask tt tt  , addX! 3)
  ∷ (run incX 3 , 5)
  ∷ (ask tt tt  , stop!)
  ∷ []

trace-is : theTrace ≡ expected
trace-is = refl

accepted : Product (λ b → b kx ≡ just 5)
accepted = finalBoard , final-x

-- 代理层的一步 run 在对象层是一条事务箭头：(get kx , nothing) (set kx 2 , tt)
inc-tx : Category.Hom Trans b0 (snd (exec Rroot incX 2 b0))
inc-tx = transOf Rroot incX 2 b0

inc-tx-is : fst inc-tx ≡ (get kx , nothing) ∷ (set kx 2 , tt) ∷ []
inc-tx-is = refl

------------------------------------------------------------------------
-- 8 方块：写 x 与写 y 填满（机器出证书）；两次写 x 空心
------------------------------------------------------------------------
filled : Filled (set kx 5 ∷ []) (set ky 2 ∷ [])
filled = fill-indep _ _ ((kx≢ky , tt) , tt)

hollow : ¬ Filled (set kx 1 ∷ []) (set kx 2 ∷ [])
hollow f = snotz (injSuc (just-inj 2 1 (cong (λ s → s kx) (f b0))))

------------------------------------------------------------------------
-- 9 子 schema（只含 y）的 lens：写回之后 y 换了、x 原样；GetPut 在终局上的实例
------------------------------------------------------------------------
module RY = Realm (λ k → k ≡ ky) (λ k → k ≟K ky) (λ k → isSetK k ky)

y-only : RY.Board∣R
y-only _ = just 7

merged-y : RY.merge finalBoard y-only ky ≡ just 7
merged-y = refl

merged-x : RY.merge finalBoard y-only kx ≡ just 5
merged-x = refl

roundtrip : RY.merge finalBoard (RY.restrict finalBoard) ≡ finalBoard
roundtrip = GetPut RY.realm finalBoard

------------------------------------------------------------------------
-- 10 改名：schema 等价 ⇒ 实例沿路径搬运（ua），算出来就是重索引
------------------------------------------------------------------------
data Key′ : Type where
  kx′ ky′ : Key′

to : Key → Key′
to kx = kx′
to ky = ky′

from : Key′ → Key
from kx′ = kx
from ky′ = ky

e : Key ≃ Key′
e = isoToEquiv (iso to from (λ { kx′ → refl ; ky′ → refl }) (λ { kx → refl ; ky → refl }))

module RN = Rename Key′ e

moved : RN.Board′
moved = RN.carry finalBoard

moved-x : moved kx′ ≡ just 5
moved-x = refl

moved-y : moved ky′ ≡ just 2
moved-y = refl

------------------------------------------------------------------------
-- 11 换运输：同一个叶子、同一段程序，边上改成 realm isY —— 叶子看不见 x
--   copyXY 读 x 得 nothing（按 0），写 y = 0；回来时 x 原样。sound 照样成立
------------------------------------------------------------------------
isY : Key → Bool
isY kx = false
isY ky = true

root′ : Config
root′ = node Rroot Unit (λ _ → leaf) (λ _ → realm isY)

stratRoot′ : Strat root′
stratRoot′ = record { prog = rootProg root′ rcheck 8 ; kids = λ _ → stratLeaf }

result′ : Position root′ b0
result′ = finish root′ stratRoot′ (prog stratRoot′ 0) w0

final′-x : fst result′ kx ≡ just 5
final′-x = refl

final′-y : fst result′ ky ≡ just 0          -- 叶子只看见 y，所以拷到的是 0
final′-y = refl

------------------------------------------------------------------------
-- 12 换对手：录音对手（Rebuilder）。先拼出可判定相等，再放录音
------------------------------------------------------------------------
import Replay
module RP = Replay
  Unit (λ _ → Unit) (λ _ → Cmd) OState oracleF
  WSig Board isSetBoard isSetWRes world
  ℕ ℕ
  Lifting restrictL mergeL
open RP using (DecCfg ; wrap ; dynLens ; wrap-honest)
module DA = RP.DecAct (λ _ _ → yes refl) (λ _ _ _ → yes refl) discreteℕ

decLeaf : DecCfg leaf
decLeaf = record
  { decOp  = DA.decAct Rleaf ⊥ (λ { copyXY copyXY → yes refl }) (λ { copyXY _ _ → yes refl }) (λ ())
  ; decRes = λ { copyXY → discreteℕ }
  ; kids   = λ () }

decRoot : DecCfg root
decRoot = record
  { decOp  = DA.decAct Rroot Unit (λ { incX incX → yes refl }) (λ { incX → discreteℕ }) (λ _ _ → yes refl)
  ; decRes = λ { incX → discreteℕ }
  ; kids   = λ _ → decLeaf }

-- 录音对手 = wrap 真对手；它诚实，所以是 soundHonest 的合法对手
recorder : Comodel (Sig-of root) (W × Trace (Sig-of root))
recorder = wrap root decRoot (opp root stratRoot) (dynLens Unit)

recorder-honest : Honest root recorder (λ wr → board (fst wr))
recorder-honest = wrap-honest root decRoot (opp root stratRoot) (dynLens Unit) (honest root stratRoot)

-- 行为尺：同一程序、同一起点，对着自己的录音回放 —— 棋谱逐字相同，预言机一次都没被问
replayed : ℕ × (W × Trace (Sig-of root)) × Trace (Sig-of root)
replayed = Play.play recorder (prog stratRoot 0) (w0 , theTrace)

replay-trace : snd (snd replayed) ≡ theTrace
replay-trace = refl

replay-oracle-untouched : fst (fst (fst (snd replayed))) ≡ script     -- 脚本一条没消费
replay-oracle-untouched = refl

replay-board : board (fst (fst (snd replayed))) kx ≡ just 5
replay-board = refl

-- 录音失效：起点变成 x = 10。第一条 ask 还能放；第一条 run 算出 12 ≠ 录音里的 2，
-- 录音作废，之后全问真预言机（脚本从头消费）。终局 x = 17：2 + 2 + 3 + 10
b10 : Board
b10 = upd kx (just 10) b0

diverged : ℕ × (W × Trace (Sig-of root)) × Trace (Sig-of root)
diverged = Play.play recorder (prog stratRoot 0) ((script , b10 , tt) , theTrace)

diverged-x : board (fst (fst (snd diverged))) kx ≡ just 17
diverged-x = refl

diverged-steps : length (snd (snd diverged)) ≡ 9                       -- 录音的 7 条 + 重问的 2 条
diverged-steps = refl

-- 录音对手跑出来的棋谱同样合法（结构只认诚实）
replay-legal : Build.Legal (Mach root) b0 (snd (snd replayed)) (board (fst (fst (snd replayed))))
replay-legal = soundHonest root recorder (λ wr → board (fst wr)) recorder-honest (prog stratRoot 0) (w0 , theTrace)
