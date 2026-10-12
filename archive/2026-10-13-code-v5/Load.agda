{-# OPTIONS --safe --cubical #-}
------------------------------------------------------------------------
-- Load.agda —— 反射工具：代码 → 环境
--   装一条声明是编排层的一步。这一拍 d 是数据；后端（Agda 自己的类型检查器）判了 ok，
--   下一拍的环境就多了它，续体里才能 call 新名字——▷ 管的是环境的版本，不是一个值什么时候到。
--   后端是 CodeSig 的余模型，住在 Haskell 里（agda-cubical-run 的 --cubical-drive）：
--   归约到 move (load d) k 时真的去查、扩展签名，把判决喂给 k；归约到 move (call t a) k 时真的去算。
--   Agda 这一侧一个 postulate 都没有：后端的样子只在 Comodel 的类型里。
------------------------------------------------------------------------
open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat
open import Cubical.Data.Sigma
open import Cubical.Data.Sum using (_⊎_ ; inl ; inr)
open import Cubical.Data.List
open import Cubical.Data.SumFin.Base using (Fin)
open import Agda.Builtin.String using (String)
open import Later

module Load (libD libC : ℕ) (libPars : Fin libD → ℕ) where

open import Code libD libC libPars

------------------------------------------------------------------------
-- §1 签名：两种步
------------------------------------------------------------------------
data Verdict : Type where                 -- 后端的判决
  ok   : ℕ → Verdict                      --   通过；带新环境的指纹（后端算的，Rebuilder 比它）
  fail : String → Verdict                 --   没通过；带报错原文（喂回给 LLM）

data COp (Γ : Env) : Type where
  load : Decl Γ → COp Γ                              -- 装一条声明：这一拍它是数据
  call : (t : Name tn Γ) → El (callOf Γ t) → COp Γ   -- 调一个工具：不在 Γ 里的名字写不出来

CRes : {Γ : Env} → COp Γ → Type
CRes     (load d)   = Verdict
CRes {Γ} (call t a) = El (resOf Γ t)

cnext : {Γ : Env} (o : COp Γ) → CRes o → Env
cnext {Γ} (load d)   (ok _)   = Γ ▸ d               -- 通过：下一拍的环境多一条
cnext {Γ} (load d)   (fail _) = Γ                   -- 没通过：环境不变
cnext {Γ} (call t a) _        = Γ                   -- 调用不动环境

CodeSig : TSig Env
CodeSig = record { Op = COp ; Res = CRes ; next = cnext }

open Traces CodeSig public                -- Trace Γ Γ′、[]、_∷_、_++_、Cat

------------------------------------------------------------------------
-- §2 解释器子句（纯 Agda）：把一段程序逐条装进去，装完接着跑；哪条没过就停
------------------------------------------------------------------------
loadThen : {A : Env → Type} {Γ Γ′ : Env}
         → Code Γ Γ′ → Run CodeSig A Γ′ → ({Γ″ : Env} → A Γ″) → Run CodeSig A Γ
loadThen ∅       k stop = k
loadThen (d ▹ P) k stop = move (load d) λ { (ok _) → loadThen P k stop ; (fail _) → done stop }

-- 棋谱里通过了的那些声明就是程序；终点环境由它们 fold 出来（状态 = 日志的 fold）
accepted : {Γ Γ′ : Env} → Trace Γ Γ′ → Code Γ Γ′
accepted []                        = ∅
accepted ((load d   , ok _)   ∷ t) = d ▹ accepted t
accepted ((load d   , fail _) ∷ t) = accepted t
accepted ((call t a , r)      ∷ s) = accepted s

------------------------------------------------------------------------
-- §3 后端状态的模型：每个工具一个实现。真后端的状态是 TCState，这里只给形状
--   装一条声明后表怎么长：老的照旧，新的由 newImpl 给——真后端按声明的体算，玩具里它是参数
------------------------------------------------------------------------
Impls : Env → Type
Impls Γ = (t : Name tn Γ) → El (callOf Γ t) → El (resOf Γ t)

NewImpl : Type
NewImpl = {Γ : Env} (d : Decl Γ) (j : Fin (newCount tn d)) → El (fst (ifaceNew d j)) → El (snd (ifaceNew d j))

extendImpls : NewImpl → (Γ : Env) (d : Decl Γ) → Impls Γ → Impls (Γ ▸ d)
extendImpls newImpl Γ d w t = go (split (count tn Γ) t)
  where
    go : (s : Name tn Γ ⊎ Fin (newCount tn d)) → El (fst (ifaceAt Γ d s)) → El (snd (ifaceAt Γ d s))
    go (inl j) = w j
    go (inr j) = newImpl d j

------------------------------------------------------------------------
-- §4 脚本后端（玩具 / 录音）：对每条 load 按脚本判决，脚本用完一律通过；call 查实现表
--   它是 CodeSig 的一个余模型，和真后端住同一个槽；真后端不在模型内，接通见 docs/code-type.md
------------------------------------------------------------------------
module Scripted (newImpl : NewImpl) where

  W : Env → Type
  W Γ = Impls Γ × List Verdict

  respLoad : {Γ : Env} → Impls Γ → List Verdict → Verdict → (d : Decl Γ)
           → Σ[ r ∈ Verdict ] W (cnext (load d) r)
  respLoad w vs (ok h)   d = ok h   , (extendImpls newImpl _ d w , vs)
  respLoad w vs (fail s) d = fail s , (w , vs)

  respS : {Γ : Env} → W Γ → (o : COp Γ) → Σ[ r ∈ CRes o ] W (cnext o r)
  respS (w , [])       (load d)   = respLoad w [] (ok 0) d
  respS (w , v ∷ vs)   (load d)   = respLoad w vs v d
  respS (w , vs)       (call t a) = w t a , (w , vs)

  backend : Comodel CodeSig W
  backend = record { resp = respS }

------------------------------------------------------------------------
-- §5 给代理层（Harness.agda）的桥：装进来的工具以预言机的身份进入代理层，由后端作答
--   Harness 的四个预言机参数由此给出，Harness.agda 一字不改
------------------------------------------------------------------------
module AsOracle (Γ : Env) where
  Oracle : Type
  Oracle = Name tn Γ
  Q A : Oracle → Type
  Q t = El (callOf Γ t)
  A t = El (resOf Γ t)
