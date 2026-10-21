{-# OPTIONS --safe --cubical #-}
------------------------------------------------------------------------
-- Solve.agda —— 第一个任务：规格 = 一句话 + 一条测试；LLM 写，Agda 查，几轮之内过
--   一轮 = ask（配额扣一）→ enter 子实例 → parse → check 模块 → parse → check 测试模块 → leave
--   子实例是沙盒：leave 之后后端回到进入前的状态，模块名又是新的，下一轮可以重交同名模块
--   没过的轮次：Agda 的报错原文和那一轮交的代码一起拼进下一轮的提示词
--   配额 = 轮数上限：ask 要配额 ≥ 1，"最多问 n 次"是类型说的，不是约定
--   跑法：./task1.sh（真 DeepSeek）、./task1-dry.sh（信箱里预先放好的三份答卷）
------------------------------------------------------------------------
module Solve where

open import Cubical.Foundations.Prelude using (Type)
open import Cubical.Data.List.Base using (List; []; _∷_; _++_)
open import Cubical.Data.Nat.Base using (ℕ; zero; suc)
open import Cubical.Data.Bool.Base using (Bool; true; false; _or_)
open import Cubical.Data.Sigma
open import Cubical.Data.Maybe.Base using (Maybe; nothing; just)
open import Cubical.Data.Unit.Base using (tt)
open import Agda.Builtin.String using (String)
open import Syntax using (Module)
open import Env
open import Later using (Run; done; move)
open import ToyEnv using (natM; safeCubical)

open import Str using (_++ₛ_; stripFences)

------------------------------------------------------------------------
-- §2 规格、一轮的记录、结局
------------------------------------------------------------------------
record Spec : Type where
  constructor spec
  field
    modName : String        -- LLM 要写的模块名（测试模块 import 它）
    task    : String        -- 一句话
    test    : String        -- 一条测试：测试模块里 import 之后的声明

record Round : Type where
  constructor round
  field
    text    : String        -- 这一轮 LLM 交的（去围栏后）
    verdict : String        -- 驳回的原文；过了是 "ok"

data Outcome : Type where
  passed : List Round → Outcome    -- 最后一轮过了；轮数 = 表长
  gaveUp : List Round → Outcome    -- 配额用完

------------------------------------------------------------------------
-- §3 环境：根看得见 Nat 与 Prelude（Prelude 只给测试模块用）；每轮在一个同视野、零配额的子实例里
------------------------------------------------------------------------
preludeM : ModName
preludeM = "Cubical" ∷ "Foundations" ∷ "Prelude" ∷ []

E₀ : Env
E₀ = base (λ n → (n =ₘ natM) or (n =ₘ preludeM)) safeCubical

ix₀ : ℕ → Ix                          -- 配额 n = 最多问 n 次
ix₀ n = (E₀ , n) , []

hRound : Header E₀
hRound = header (natM ∷ preludeM ∷ []) safeCubical tt tt

Eᵣ : Env
Eᵣ = child E₀ hRound

------------------------------------------------------------------------
-- §4 测试模块与提示词
------------------------------------------------------------------------
testModule : Spec → String
testModule sp =
  "{-# OPTIONS --safe --cubical #-}\nmodule Test where\nopen import Cubical.Foundations.Prelude\nopen import Cubical.Data.Nat\nopen import "
  ++ₛ Spec.modName sp ++ₛ "\n\n" ++ₛ Spec.test sp

rules : Spec → String
rules sp =
  "你是 Agda 程序员。写一个完整的 Agda 模块完成下面的任务。只输出模块的代码本身：不要 markdown 围栏，不要解释，不要代码以外的任何文字。\n\n"
  ++ₛ "模块会被 Agda 2.9 以 --safe --cubical 检查。硬性要求，违反任何一条都会被驳回：\n"
  ++ₛ "1. 第一行是 {-# OPTIONS --safe --cubical #-}，第二行是 module " ++ₛ Spec.modName sp ++ₛ " where\n"
  ++ₛ "2. 导入只允许这一行：open import Cubical.Data.Nat\n"
  ++ₛ "   它提供 ℕ、zero、suc、_+_、_·_（乘法）、_∸_（截断减法）。不要导入任何别的模块：没有 Data.Nat，没有 Agda.Builtin.Nat，没有 Relation.Binary.PropositionalEquality，没有 Cubical.Foundations.Prelude。\n"
  ++ₛ "3. --safe 之下禁止：postulate、{-# TERMINATING #-}、{-# NON_TERMINATING #-}、{-# NON_COVERING #-}、primTrustMe、任何 unsafe 的东西。递归必须是结构递归（对 zero / suc n 分情况），模式匹配必须覆盖全部情况。\n"
  ++ₛ "4. 这是 Cubical Agda：自然数写 ℕ 不写 Nat；乘法是 _·_ 不是 _*_；减法是 _∸_ 不是 _-_；不要加别的 OPTIONS。\n"
  ++ₛ "5. 模块里只放任务要求的定义。_≡_ 不在作用域里，所以不要在模块里写等式、测试或证明；测试由另一个模块做。\n\n"
  ++ₛ "任务：" ++ₛ Spec.task sp ++ₛ "\n\n"
  ++ₛ "写好的模块会被下面这个测试模块导入并检查，必须通过（函数名要和测试里的一致）：\n"
  ++ₛ testModule sp

prompt : Spec → Maybe Round → String
prompt sp nothing              = rules sp
prompt sp (just (round c err)) =
  rules sp
  ++ₛ "\n\n上一轮你交的代码被驳回了。你交的代码：\n" ++ₛ c
  ++ₛ "\nAgda 的报错原文（里面的行号是语法树节点编号，不是源码行号，不要管它）：\n" ++ₛ err
  ++ₛ "\n\n请修正后重新输出完整的模块，仍然只输出代码。"

------------------------------------------------------------------------
-- §5 主循环
------------------------------------------------------------------------
A : Ix → Type
A _ = Outcome

module Loop (sp : Spec) where

  hLLM : Maybe (Header Eᵣ)                     -- LLM 的模块：只许 import Nat
  hLLM = mkHeader Eᵣ (natM ∷ []) safeCubical

  hTest : (E : Env) → Maybe (Header E)         -- 测试模块：Prelude、Nat、LLM 的模块
  hTest E = mkHeader E (preludeM ∷ natM ∷ (Spec.modName sp ∷ []) ∷ []) safeCubical

  go      : (n : ℕ) → List Round → Maybe Round → Run AgdaSig A (ix₀ n)
  attempt : (n : ℕ) → List Round → String → Run AgdaSig A ((Eᵣ , 0) , ((E₀ , n) ∷ []))

  -- 还能问 suc n 次：问一次，进子实例，把答卷交给 attempt
  go zero    hist fb = done (gaveUp hist)
  go (suc n) hist fb =
    move (ask (prompt sp fb)) λ a →
    move (enter hRound 0) λ _ →
    attempt n hist (stripFences a)

  attempt n hist src = move (log ("交的代码：\n" ++ₛ src)) λ _ → move (parse src) step1
    where
    rest : List Frame
    rest = (E₀ , n) ∷ []

    -- 离开子实例，交判决：过了就结束；没过就记一笔，下一轮带着报错再问
    back : {E : Env} → Maybe String → Run AgdaSig A ((E , 0) , rest)
    back nothing    = move (log "过了") λ _ → move leave λ _ → done (passed (hist ++ (round src "ok" ∷ [])))
    back (just err) = move (log ("驳回：" ++ₛ err)) λ _ → move leave λ _ → go n (hist ++ (round src err ∷ [])) (just (round src err))

    step4 : (c : Code Eᵣ) (i : Iface) (t : Code (Eᵣ ▸ (c , i))) (r : Verdict)
          → Run AgdaSig A (next {(Eᵣ ▸ (c , i) , 0) , rest} (check t) r)
    step4 c i t (fail _ msg) = back (just ("模块本身过了，但测试模块没过：\n" ++ₛ msg))
    step4 c i t (ok _)       = back nothing

    step3 : (c : Code Eᵣ) (i : Iface) → Maybe Module → Run AgdaSig A ((Eᵣ ▸ (c , i) , 0) , rest)
    step3 c i nothing  = back (just "harness 的问题：测试模块 parse 失败")
    step3 c i (just t) with hTest (Eᵣ ▸ (c , i))
    ... | nothing = back (just "harness 的问题：测试模块的头被驳回")
    ... | just h with mkCode (Eᵣ ▸ (c , i)) h t
    ...   | nothing = back (just "harness 的问题：测试模块被驳回")
    ...   | just tc = move (check tc) (step4 c i tc)

    step2 : (c : Code Eᵣ) (r : Verdict) → Run AgdaSig A (next {(Eᵣ , 0) , rest} (check c) r)
    step2 c (fail _ msg) = back (just msg)
    step2 c (ok i)       = move (parse (testModule sp)) (step3 c i)

    step1 : Maybe Module → Run AgdaSig A ((Eᵣ , 0) , rest)
    step1 nothing  = back (just "parse 失败：交的不是一个完整的 Agda 模块（代码以外还有别的文字？）")
    step1 (just m) with modNameOf m =ₘ (Spec.modName sp ∷ []) | hLLM
    ... | false | _       = back (just ("模块名必须是 " ++ₛ Spec.modName sp))
    ... | true  | nothing = back (just "harness 的问题：头被驳回")
    ... | true  | just h with mkCode Eᵣ h m
    ...   | nothing = back (just "OPTIONS 只能是 --safe --cubical，不能多也不能少")
    ...   | just c  = move (check c) (step2 c)

------------------------------------------------------------------------
-- §6 第一个任务：twice，最多五轮
------------------------------------------------------------------------
twiceSpec : Spec
twiceSpec = spec "Twice" "写 twice : ℕ → ℕ，把输入加倍。" "test : twice 3 ≡ 6\ntest = refl\n"

task1 : Run AgdaSig A (ix₀ 5)
task1 = Loop.go twiceSpec 5 [] nothing
