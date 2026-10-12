{-# OPTIONS --safe --cubical #-}
------------------------------------------------------------------------
-- Game.agda —— 一局棋的三件套
--   规则（签名 Sig）   程序（自由模型 Free = 策略）   对手（余模型 Comodel）
--   棋谱的类型由签名导出；"跑一局" = 策略对上对手。
-- 没有全局公理：所有未知量都是记录字段或模块参数。
------------------------------------------------------------------------
module Game where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma
open import Cubical.Data.List

-- 签名 = 规则书的内容
--   Op      能走的步（已含参数：问什么、调什么）
--   Res o   走了 o 之后能收到的回应
record Sig : Type₁ where
  field
    Op  : Type
    Res : Op → Type
open Sig public

-- 程序 = 自由模型里的项 = 策略
--   done a    交出结果 a
--   move o k  走一步 o；k 说明收到每种回应之后接着怎么走
-- 它是有限的树：每条路都走到 done。停机由形状保证；续命 = 再开一局。
data Free (S : Sig) (A : Type) : Type where
  done : A → Free S A
  move : (o : Op S) → (Res S o → Free S A) → Free S A

-- 程序接程序（单子的 bind；三条律留给 S0）
_>>=_ : {S : Sig} {A B : Type} → Free S A → (A → Free S B) → Free S B
done a   >>= f = f a
move o k >>= f = move o (λ r → k r >>= f)

-- 一步的记录 = (走了什么 , 收到什么)；棋谱 = 一列记录
-- 类型完全由签名决定：签名定了，日志的文法就定了
Step : Sig → Type
Step S = Σ[ o ∈ Op S ] Res S o

Trace : Sig → Type
Trace S = List (Step S)

-- 对手 = 余模型。W = 对手的内部状态（LLM 的记忆、世界的数据库……），写在类型里
--   resp w o  对第 o 步作答，并给出自己的新状态
record Comodel (S : Sig) (W : Type) : Type₁ where
  field
    resp : W → (o : Op S) → Res S o × W
open Comodel public

-- 跑一局：策略对上对手
--   结果 = (策略交出的东西 , 对手的新状态 , 棋谱)
module Play {S : Sig} {W : Type} (C : Comodel S W) where
  play : {A : Type} → Free S A → W → A × W × Trace S
  play (done a)   w = a , w , []
  play (move o k) w =
    let r    = fst (resp C w o)          -- 对手的回应
        w′   = snd (resp C w o)          -- 对手的新状态
        rest = play (k r) w′             -- 接着走
    in fst rest , fst (snd rest) , ((o , r) ∷ snd (snd rest))
