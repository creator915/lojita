{-# OPTIONS --safe --cubical #-}
------------------------------------------------------------------------
-- Later.agda —— 延迟模态 ▷ 与拍
--   一拍 = 走一步。这一步可能换环境（装进一条声明），所以"下一拍"不是一个时刻，
--   是一个环境：走了 o、收到 r 之后，程序在 next o r 里继续。▷ 说的就是这个"之后"。
--   索引 Ix = 环境的类型（Code.agda 用 Env）。Game.agda 的 Sig / Free / Comodel / Play
--   是 Ix = Unit（环境从不变）的特例。
--   没有 guarded 不动点：程序是有限树，停机由形状保证，和 Game.agda 一样。
------------------------------------------------------------------------
module Later where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma
open import PathCat using (Category)

private variable
  Ix : Type
  i j k l : Ix

------------------------------------------------------------------------
-- §1 路：每个点上一族边，边有终点；一条路 = 一串首尾相接的边
--   程序（声明序列）和棋谱（一列记录）都是路，所以只造一次（同 PathCat 的做法）
------------------------------------------------------------------------
module PathOf {Ix : Type} (E : Ix → Type) (tgt : {i : Ix} → E i → Ix) where

  data Walk : Ix → Ix → Type where
    []  : {i : Ix} → Walk i i
    _∷_ : {i j : Ix} (e : E i) → Walk (tgt e) j → Walk i j
  infixr 5 _∷_

  _++_ : {i j k : Ix} → Walk i j → Walk j k → Walk i k
  []      ++ q = q
  (e ∷ p) ++ q = e ∷ (p ++ q)
  infixr 5 _++_

  ++-unit-r : {i j : Ix} (p : Walk i j) → p ++ [] ≡ p
  ++-unit-r []      = refl
  ++-unit-r (e ∷ p) = cong (e ∷_) (++-unit-r p)

  ++-assoc : {i j k l : Ix} (p : Walk i j) (q : Walk j k) (r : Walk k l)
           → (p ++ q) ++ r ≡ p ++ (q ++ r)
  ++-assoc []      q r = refl
  ++-assoc (e ∷ p) q r = cong (e ∷_) (++-assoc p q r)

  -- 范畴：对象 = 点，箭头 = 路。左单位律是定义本身，其余两条是上面的引理
  Cat : Category
  Cat = record { Ob = Ix ; Hom = Walk ; id = [] ; _⋆_ = _++_
               ; ⋆IdL = λ f → refl ; ⋆IdR = ++-unit-r ; ⋆Assoc = ++-assoc }

------------------------------------------------------------------------
-- §2 拍签名：在每个环境能走的步、它的回应、走完到哪
------------------------------------------------------------------------
record TSig (Ix : Type) : Type₁ where
  field
    Op   : Ix → Type                          -- 在 i 能走的步
    Res  : {i : Ix} → Op i → Type             -- 走了 o 之后能收到的回应
    next : {i : Ix} (o : Op i) → Res o → Ix    -- 收到 r 之后在哪个环境（装成了 / 没装成）
open TSig public

-- 一步的记录 = (走了什么 , 收到什么)
Step : (S : TSig Ix) → Ix → Type
Step S i = Σ[ o ∈ Op S i ] Res S o

-- ▷：一步 o 之后。X 是"每个环境上一个类型"；
--   ▷ S o X = 对每种回应 r，X 在下一拍的环境 next o r 里成立
▷ : (S : TSig Ix) (o : Op S i) (X : Ix → Type) → Type
▷ S o X = (r : Res S o) → X (next S o r)

------------------------------------------------------------------------
-- §3 程序：这一拍是数据（o 是一个值），下一拍是控制（▷ 里的续体）
--   续体的类型写在下一拍的环境上，所以"新名字下一拍才能用"是类型说的，不是约定
------------------------------------------------------------------------
data Run (S : TSig Ix) (A : Ix → Type) : Ix → Type where
  done : A i → Run S A i
  move : (o : Op S i) → ▷ S o (Run S A) → Run S A i

_>>=_ : {S : TSig Ix} {A B : Ix → Type}
      → Run S A i → ({j : Ix} → A j → Run S B j) → Run S B i
done a   >>= f = f a
move o k >>= f = move o (λ r → k r >>= f)
infixl 1 _>>=_

------------------------------------------------------------------------
-- §4 棋谱：从 i 到 j 的路，边 = 一步的记录，终点由 next 算
--   "棋谱合法"不用另证：类型里已经带着起点和终点（状态 = 棋谱的 fold）
------------------------------------------------------------------------
module Traces {Ix : Type} (S : TSig Ix) where
  open PathOf (Step S) (λ s → next S (fst s) (snd s)) public
    renaming (Walk to Trace)

------------------------------------------------------------------------
-- §5 余模型：对手的状态也按环境分（后端的 TCState 就是这样一个 W）；跑一局
------------------------------------------------------------------------
record Comodel (S : TSig Ix) (W : Ix → Type) : Type where
  field
    resp : W i → (o : Op S i) → Σ[ r ∈ Res S o ] W (next S o r)
open Comodel public

module Play {Ix : Type} {S : TSig Ix} {W : Ix → Type} (C : Comodel S W) where
  open Traces S

  -- 结果 = (终点环境 , 交出的东西 , 对手的新状态 , 棋谱)
  play : {A : Ix → Type} {i : Ix} → Run S A i → W i → Σ[ j ∈ Ix ] (A j × W j × Trace i j)
  play (done a)   w = _ , a , w , []
  play (move o k) w =
    let r    = fst (resp C w o)                -- 对手的回应
        w′   = snd (resp C w o)                -- 对手的新状态（已在下一拍的环境上）
        rest = play (k r) w′                   -- 接着走
    in fst rest , fst (snd rest) , fst (snd (snd rest)) , ((o , r) ∷ snd (snd (snd rest)))
