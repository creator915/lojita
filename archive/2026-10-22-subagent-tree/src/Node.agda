{-# OPTIONS --safe --cubical #-}
------------------------------------------------------------------------
-- Node.agda —— 文件 agent 的程序（docs/harness/04-node.md）
--   node d q p X 是挂在前缀 p 上的文件 agent：只用 NodeSig 里的步，每一轮 ask 一次、分类答卷、搬运、沙箱里 check，
--   解答就粘合，分解就逐个开孩子，反驳就交反驳；结局写进 p/result 再交给续体。
--   §1 类型  §2 NodeSig（工具注册表）与 embed  §3 键与证明  §4 答卷分类  §5 三个帧  §6 提示词  §7 主循环
--   模块参数 = E₀：包名单、E₀ 的 flag（含 --safe，粘合用）、E₀⁻ 的 flag（节点 / 沙箱 / 孩子用），
--   加三条算出来的证明（字面量名单下都是 tt）：名单里的模块在 E₀ 里可见、E₀⁻ ≼ E₀⁻、E₀ ≼ E₀⁻。
--   索引的写法：节点帧永远是 ((E⁻ , q , p) , rest)。配额 q 是索引、不做递归；递归在 fuel（结构递减）、树深 d、孩子表上；
--   每次 ask 前用 fromDec 查 1 ≤ᵇ q。孩子回来经续体 Cont（CPS）：孩子的终点配额不定，续体对任何 q′ 都写得出 leave。
------------------------------------------------------------------------
open import Cubical.Foundations.Prelude using (Type; _≡_; refl; sym; subst)
open import Cubical.Data.List.Base using (List; []; _∷_; _++_; map; length; rev)
open import Cubical.Data.Bool.Base using (Bool; true; false; _and_; _or_; not; if_then_else_; Bool→Type)
open import Cubical.Data.Nat.Base using (ℕ; zero; suc; predℕ)
open import Agda.Builtin.Nat using (_-_)
open import Cubical.Data.Sigma using (_×_; _,_; fst; snd)
open import Cubical.Data.Maybe.Base using (Maybe; nothing; just)
open import Cubical.Data.Unit.Base using (Unit; tt)
open import Agda.Builtin.String using (String; primStringAppend; primShowNat; primStringToList; primStringFromList)
open import Agda.Builtin.Char using (Char; primCharEquality; primIsAlpha; primIsDigit)
open import Env
open import Path using (Path; isPrefix; prefix-++; prefix-refl; _≤ᵇ_; half; half-≤; join)
open import Later using (TSig; Run; done; move)

module Node (E₀mods : List ModName) (E₀flags E₀⁻flags : Flags)
            (mods-ok : Bool→Type (allᵇ (_∈ₘ E₀mods) E₀mods))
            (sand-ok : Bool→Type (E₀⁻flags ≼ E₀⁻flags))
            (glue-ok : Bool→Type (E₀flags ≼ E₀⁻flags)) where

infixr 5 _++ₛ_
_++ₛ_ : String → String → String
_++ₛ_ = primStringAppend

show : ℕ → String
show = primShowNat

------------------------------------------------------------------------
-- §0 环境：节点帧、沙箱帧、孩子帧的环境都是 E⁻（E₀ 名单、E₀⁻）；粘合帧的头多 --safe
------------------------------------------------------------------------
E⁻ : Env
E⁻ = base (_∈ₘ E₀mods) E₀⁻flags

hSand : Header E⁻        -- 沙箱帧、孩子帧的头：E₀ 名单、E₀⁻。child E⁻ hSand 算出来还是 E⁻
hSand = header E₀mods E₀⁻flags mods-ok sand-ok

hGlue : Header E⁻        -- 粘合帧的头：E₀ 名单、E₀（多 --safe）
hGlue = header E₀mods E₀flags mods-ok glue-ok

------------------------------------------------------------------------
-- §1 类型
------------------------------------------------------------------------
data Result : Type where
  solved    : List Path → Result         -- 子树全部模块的键，依赖序；全部在 E₀（--safe）下过
  refuted   : Path → Result              -- 反驳模块的键
  exhausted : Result                     -- 配额用完；不是判决

data Note : Type where                   -- NodeSig 的 set 只能写这四种键
  memo    : ℕ → Note                     -- p/memo/<n>
  verdict : ℕ → Note                     -- p/verdict/<n>
  result  : Note                         -- p/result
  dropped : String → Note                -- p/kids/<K>/dropped

data Why : Type where                    -- 为什么改设计
  kidRefuted   : String → Path → Why
  kidExhausted : String → Why
  glueFailed   : String → Why

data Kind : Type where                   -- 答卷的分类
  solution  : String → Kind              -- 文件 = {X.agda, XTest.agda}；带主文件名（没有 "-- file:" 标记时是 _.agda）
  design    : String → List String → Kind  -- 主文件名、孩子名表：每个 K 配 K.agda、KTest.agda
  refute    : Kind                       -- 文件含 XRefute.agda
  malformed : String → Kind              -- 别的：缺 X.agda、孩子缺一半、名字不合法

data Verdict′ : Type where               -- 一组 check 的结论
  pass   : Verdict′
  failed : String → Verdict′

------------------------------------------------------------------------
-- §2 NodeSig：工具注册表。没有的：sh、eval、render、goals / give / split、裸的 set、parse / check
------------------------------------------------------------------------
data NodeOp : Ix → Type where
  ask       : {ix : Ix} → Query → {_ : Bool→Type (1 ≤ᵇ quotaOf ix)} → NodeOp ix
  get       : {ix : Ix} → Path → NodeOp ix
  setN      : {ix : Ix} → Note → String → NodeOp ix                       -- 键由 Note 算出，证明由 prefix-++ 给
  transport : {ix : Ix} (m : Move) (t s d : Path) {_ : Bool→Type (isPrefix (realmOf ix) t)} → NodeOp ix
  audit     : {ix : Ix} → Path → NodeOp ix
  checkAt   : {ix : Ix} → Header (envOf ix) → Path → NodeOp ix             -- 让检查器读 Store 里的模块；agent 自己不读
  enter     : {ix : Ix} (h : Header (envOf ix)) (q : ℕ) (p : Path)
              {_ : Bool→Type (q ≤ᵇ quotaOf ix)} {_ : Bool→Type (isPrefix (realmOf ix) p)} → NodeOp ix
  leave     : {ix : Ix} → {_ : Bool→Type (hasParent ix)} → NodeOp ix
  log       : {ix : Ix} → String → NodeOp ix

------------------------------------------------------------------------
-- §3 键与证明：每个"在 p 下"的键一条，形状都一样
------------------------------------------------------------------------
specStub specTest : Path → Path
specStub p = p ++ "spec" ∷ "stub" ∷ []
specTest p = p ++ "spec" ∷ "test" ∷ []

codeOf : Path → String → Path                      -- p/code/<f>
codeOf p f = p ++ "code" ∷ f ∷ []

draftOf : Path → String → String → Path            -- p/draft/<step>/<f>
draftOf p step f = p ++ "draft" ∷ step ∷ f ∷ []

kidOf : Path → String → Path                       -- p/kids/<K>
kidOf p K = p ++ "kids" ∷ K ∷ []

kidStub kidTest : Path → String → Path             -- 孩子的 spec 两段，写成 p ++ … 以便 prefix-++ 直接用
kidStub p K = p ++ "kids" ∷ K ∷ "spec" ∷ "stub" ∷ []
kidTest p K = p ++ "kids" ∷ K ∷ "spec" ∷ "test" ∷ []

noteKey : Path → Note → Path
noteKey p (memo n)    = p ++ "memo" ∷ show n ∷ []
noteKey p (verdict n) = p ++ "verdict" ∷ show n ∷ []
noteKey p result      = p ++ "result" ∷ []
noteKey p (dropped K) = p ++ "kids" ∷ K ∷ "dropped" ∷ []

ok-++ : ∀ p s → Bool→Type (isPrefix p (p ++ s))
ok-++ p s = subst Bool→Type (sym (prefix-++ p s)) tt

ok-refl : ∀ p → Bool→Type (isPrefix p p)
ok-refl p = subst Bool→Type (sym (prefix-refl p)) tt

ok-half : ∀ q → Bool→Type (half q ≤ᵇ q)
ok-half q = subst Bool→Type (sym (half-≤ q)) tt

noteOk : (p : Path) (n : Note) → Bool→Type (isPrefix p (noteKey p n))
noteOk p (memo n)    = ok-++ p _
noteOk p (verdict n) = ok-++ p _
noteOk p result      = ok-++ p _
noteOk p (dropped K) = ok-++ p _

-- 逐个构造子对过去；setN 翻成 set，带上算出来的键和证明
embed : {ix : Ix} → NodeOp ix → Op ix
embed (ask q {pf})              = ask q {pf}
embed (get k)                   = get k
embed {ix} (setN n v)           = set (noteKey (realmOf ix) n) v {noteOk (realmOf ix) n}
embed (transport m t s d {pf})  = transport m t s d {pf}
embed (audit k)                 = audit k
embed (checkAt h k)             = checkAt h k
embed (enter h q p {pf₁} {pf₂}) = enter h q p {pf₁} {pf₂}
embed (leave {_} {pf})          = leave {_} {pf}
embed (log s)                   = log s

NodeSig : TSig Ix
NodeSig = record { Op = NodeOp ; Res = λ o → Res (embed o) ; next = λ o r → next (embed o) r }

embedRun : {A : Ix → Type} {ix : Ix} → Run NodeSig A ix → Run AgdaSig A ix
embedRun (done a)   = done a
embedRun (move o k) = move (embed o) λ r → embedRun (k r)

------------------------------------------------------------------------
-- §4 答卷分类：有 XRefute.agda → refute；没有 X.agda 也没有 _.agda → malformed；
--   其余文件按名字配对成孩子（K.agda 与 KTest.agda 成对、K 只含字母数字），配不成对 → malformed；没有孩子 → solution；有 → design
------------------------------------------------------------------------
isPrefixC : List Char → List Char → Bool
isPrefixC []       _        = true
isPrefixC (_ ∷ _)  []       = false
isPrefixC (c ∷ cs) (d ∷ ds) = primCharEquality c d and isPrefixC cs ds

dropN : {A : Type} → ℕ → List A → List A
dropN zero    xs       = xs
dropN (suc n) []       = []
dropN (suc n) (_ ∷ xs) = dropN n xs

-- stripSuffix ".agda" "K.agda" = just "K"
stripSuffix : String → String → Maybe String
stripSuffix suf s with isPrefixC (rev (primStringToList suf)) (rev (primStringToList s))
... | false = nothing
... | true  = just (primStringFromList (rev (dropN (length (primStringToList suf)) (rev (primStringToList s)))))

legalName : String → Bool                          -- 非空，只含字母数字（I6 的 [A-Za-z0-9]+）
legalName s = go (primStringToList s)
  where
  all′ : List Char → Bool
  all′ []       = true
  all′ (c ∷ cs) = (primIsAlpha c or primIsDigit c) and all′ cs
  go : List Char → Bool
  go [] = false
  go cs = all′ cs

mainFile : String → List String → Maybe String      -- X.agda，或没有标记时的 _.agda
mainFile X names = if (X ++ₛ ".agda") ∈ₛ names then just (X ++ₛ ".agda")
                   else if "_.agda" ∈ₛ names then just "_.agda" else nothing

others : String → List String → List String        -- 去掉 X.agda、_.agda、XTest.agda
others X []       = []
others X (f ∷ fs) = if (f =ₛ (X ++ₛ ".agda")) or (f =ₛ "_.agda") or (f =ₛ (X ++ₛ "Test.agda")) then others X fs else f ∷ others X fs

-- 配对：KTest.agda 要有 K.agda；K.agda 要有 KTest.agda，并把 K 记下
pairKids : List String → List String → List String → Maybe (List String)
pairKids names []       acc = just acc
pairKids names (f ∷ fs) acc with stripSuffix "Test.agda" f
... | just K  = if ((K ++ₛ ".agda") ∈ₛ names) and legalName K then pairKids names fs acc else nothing
... | nothing with stripSuffix ".agda" f
...   | just K  = if ((K ++ₛ "Test.agda") ∈ₛ names) and legalName K then pairKids names fs (acc ++ K ∷ []) else nothing
...   | nothing = nothing

classify : String → List String → Kind
classify X names with (X ++ₛ "Refute.agda") ∈ₛ names | mainFile X names
... | true  | _            = refute
... | false | nothing      = malformed ("no " ++ₛ X ++ₛ ".agda")
... | false | just main with pairKids names (others X names) []
...   | nothing = malformed "kids do not pair up (K.agda with KTest.agda, K alphanumeric)"
...   | just [] = solution main
...   | just ks = design main ks

stepOf : List String → String                      -- ask 的回应：第一个元素是步号
stepOf (s ∷ _) = s
stepOf []      = "0"

filesOf : List String → List String                -- 其余是文件名
filesOf (_ ∷ fs) = fs
filesOf []       = []

------------------------------------------------------------------------
-- §5 三个帧：沙箱（E₀⁻）、粘合（E₀），都在同一前缀、零配额；进去逐个 checkAt，出来忘掉
--   checkAll 的索引：栈顶环境 E′ 是显式参数，每过一个模块换成 E′ ▸ i；续体对任何终点环境成立
--   hMax = mkHeader E′ (E₀ 名单 ++ 本沙箱里已过的模块名) fl：证明算出来；后端核对实际 import ⊆ 它
------------------------------------------------------------------------
showMod : ModName → String
showMod []      = ""
showMod (s ∷ m) = s ++ₛ rest m
  where
  rest : ModName → String
  rest []      = ""
  rest (t ∷ m) = "." ++ₛ t ++ₛ rest m

showMods : List ModName → String
showMods []       = ""
showMods (m ∷ []) = showMod m
showMods (m ∷ ms) = showMod m ++ₛ ", " ++ₛ showMods ms

checkAll : {R : Ix → Type} {rest : List Frame} {p : Path} (E′ : Env) (fl : Flags) (seen : List ModName) (keys : List Path)
         → ((E″ : Env) → Verdict′ → Run NodeSig R ((E″ , 0 , p) , rest))
         → Run NodeSig R ((E′ , 0 , p) , rest)
checkAll E′ fl seen []       k = k E′ pass
checkAll E′ fl seen (x ∷ xs) k with mkHeader E′ (E₀mods ++ seen) fl
... | nothing = k E′ (failed ("header: cannot import " ++ₛ showMods seen))
... | just h  = move (checkAt h x) λ where
    (fail _ msg) → k E′ (failed msg)
    (ok i)       → checkAll (E′ ▸ i) fl (Iface.name i ∷ seen) xs k

sandbox : {R : Ix → Type} {rest : List Frame} {q : ℕ} {p : Path} (h : Header E⁻) (keys : List Path)
        → (Verdict′ → Run NodeSig R ((E⁻ , q , p) , rest))
        → Run NodeSig R ((E⁻ , q , p) , rest)
sandbox {p = p} h keys k =
  move (enter h 0 p {tt} {ok-refl p}) λ _ →
  checkAll (child E⁻ h) (flags h) [] keys λ _ v →
  move leave λ _ →
  k v

------------------------------------------------------------------------
-- §6 提示词（Query）：lit 写死，row / last 由后端填
------------------------------------------------------------------------
prompt : Path → String → Query
prompt p X =
  lit ("【任务】你在填一个 Agda 包 " ++ₛ X ++ₛ "。下面是它的 stub 和测试的 stub；签名与具体定义不能改，洞是 postulate 块里的名字。") ∷
  lit "【stub】" ∷ row (specStub p) ∷
  lit "【测试】" ∷ row (specTest p) ∷
  lit ("【规则】只能 import：" ++ₛ showMods E₀mods ++ₛ "；不许 postulate / TERMINATING / primitive / macro / unquote；输出若干文件，每个以 \"-- file: 名字.agda\" 开头。") ∷
  lit ("【分包】" ++ₛ X ++ₛ ".agda 可以 import 一个新名字 K，但必须同时交 K.agda（stub：签名 + postulate）和 KTest.agda（stub）。") ∷
  lit ("【反驳】若规约矛盾，只交 " ++ₛ X ++ₛ "Refute.agda：import " ++ₛ X ++ₛ " 与 " ++ₛ X ++ₛ "Test，证 absurd : ⊥，不许 postulate。") ∷
  lit "【上次】" ∷ last 2 (p ++ "verdict" ∷ []) ∷ last 3 (p ++ "memo" ∷ []) ∷ []

showWhy : Why → String
showWhy (kidRefuted K k)  = "kid " ++ₛ K ++ₛ " refuted its spec: " ++ₛ join k
showWhy (kidExhausted K)  = "kid " ++ₛ K ++ₛ " ran out of quota"
showWhy (glueFailed msg)  = "glue (--safe) failed: " ++ₛ msg

promptRedesign : Path → String → Why → Query
promptRedesign p X why = prompt p X ++ (lit "【改设计】当前根正文：" ∷ row (codeOf p (X ++ₛ ".agda")) ∷ whyItems why)
  where
  whyItems : Why → List Item
  whyItems (kidRefuted K k) = lit ("孩子 " ++ₛ K ++ₛ " 反驳了它的规约，反驳原文：") ∷ row k ∷
                              lit ("改设计：改 " ++ₛ K ++ₛ " 的 spec，或换别的分法；spec 没变的孩子照用。") ∷ []
  whyItems (kidExhausted K) = lit ("孩子 " ++ₛ K ++ₛ " 配额用完没做出来。改设计：简化它的 spec，或换别的分法。") ∷ []
  whyItems (glueFailed msg) = lit ("粘合（--safe）没过：" ++ₛ msg) ∷ []

------------------------------------------------------------------------
-- §7 主循环
------------------------------------------------------------------------
showKeys : List Path → String
showKeys []       = ""
showKeys (k ∷ ks) = " " ++ₛ join k ++ₛ showKeys ks

showResult : Result → String                       -- p/result 行
showResult (solved ks) = "solved " ++ₛ show (length ks) ++ₛ showKeys ks
showResult (refuted k) = "refuted " ++ₛ join k
showResult exhausted   = "exhausted"

codes : Path → String → List Path                  -- 自己的两个模块
codes p X = codeOf p (X ++ₛ ".agda") ∷ codeOf p (X ++ₛ "Test.agda") ∷ []

refuteOf : Path → String → Path
refuteOf p X = codeOf p (X ++ₛ "Refute.agda")

kidKeys : Path → List String → List Path           -- 孩子们的 stub、test-stub，洞阶段要 check 的
kidKeys p []       = []
kidKeys p (K ∷ ks) = kidStub p K ∷ kidTest p K ∷ kidKeys p ks

Kids : Type                                        -- 回来了的孩子：名字、它的 solved 清单
Kids = List (String × List Path)

kidMods : Kids → List Path
kidMods []              = []
kidMods ((_ , ms) ∷ ks) = ms ++ kidMods ks

lookupKid : String → Kids → Maybe (List Path)
lookupKid K []              = nothing
lookupKid K ((K′ , ms) ∷ ks) = if K =ₛ K′ then just ms else lookupKid K ks

sameText : Maybe String → Maybe String → Bool
sameText (just a) (just b) = a =ₛ b
sameText _        _        = false

-- 孩子回来的续体：孩子的终点配额不定，所以对任何 q′ 都要能接
Cont : (R : Ix → Type) (p : Path) (rest : List Frame) → Type
Cont R p rest = (q : ℕ) → Result → Run NodeSig R ((E⁻ , q , p) , rest)

module Loop (R : Ix → Type) where
  Prog : (q : ℕ) (p : Path) (rest : List Frame) → Type
  Prog q p rest = Run NodeSig R ((E⁻ , q , p) , rest)

  -- 结局：写 p/result，交给续体（N4：result 先于 leave）
  finish : {rest : List Frame} (q : ℕ) (p : Path) → Result → Cont R p rest → Prog q p rest
  finish q p r k = move (setN result (showResult r)) λ _ → k q r

  -- 答卷里没有了的旧孩子：写 kids/K/dropped = 轮号
  dropGone : {rest : List Frame} {q : ℕ} {p : Path} (n : ℕ) (old keep : List String) → Prog q p rest → Prog q p rest
  dropGone n []        keep cont = cont
  dropGone n (K ∷ old) keep cont =
    if K ∈ₛ keep then dropGone n old keep cont
    else move (setN (dropped K) (show n)) λ _ → dropGone n old keep cont

  mutual
    -- 入口：写 memo/0 = quota，开始循环。d 是树深（还能开几层孩子）；fuel 从 q 起
    nodeK : {rest : List Frame} (d q : ℕ) (p : Path) (X : String) → Cont R p rest → Prog q p rest
    nodeK zero    q p X k = finish q p exhausted k
    nodeK (suc d) q p X k = move (setN (memo 0) ("quota=" ++ₛ show q)) λ _ → loop d q q 0 p X k

    -- 一轮：fuel 结构递减；配额 q 是索引，ask 前用 fromDec 查 1 ≤ᵇ q；n 是轮号（ask 的次数）
    loop : {rest : List Frame} (d q fuel n : ℕ) (p : Path) (X : String) → Cont R p rest → Prog q p rest
    loop d q zero    n p X k = finish q p exhausted k
    loop d q (suc f) n p X k = askStep d q f n p X k (fromDec (1 ≤ᵇ q))

    askStep : {rest : List Frame} (d q f n : ℕ) (p : Path) (X : String) → Cont R p rest
            → Maybe (Bool→Type (1 ≤ᵇ q)) → Prog q p rest
    askStep d q f n p X k nothing   = finish q p exhausted k
    askStep d q f n p X k (just pf) =
      move (ask (prompt p X) {pf}) λ names →
      dispatch d (predℕ q) f (suc n) p X (stepOf names) (classify X (filesOf names)) k

    dispatch : {rest : List Frame} (d q f n : ℕ) (p : Path) (X step : String) → Kind → Cont R p rest → Prog q p rest
    dispatch d q f n p X step (solution main)  k = solve d q f n p X step main k
    dispatch d q f n p X step (design main ks) k = writeKids d q f n p X step main ks ks k
    dispatch d q f n p X step refute           k = refuteStep d q f n p X step k
    dispatch d q f n p X step (malformed s)    k = bounce d q f n p X ("malformed: " ++ₛ s) k

    -- 没过：verdict/n 记报错原文，memo/n 记一笔，下一轮
    bounce : {rest : List Frame} (d q f n : ℕ) (p : Path) (X msg : String) → Cont R p rest → Prog q p rest
    bounce d q f n p X msg k =
      move (setN (verdict n) msg) λ _ →
      move (setN (memo n) ("round " ++ₛ show n ++ₛ " rejected")) λ _ →
      loop d q f n p X k

    -- 7.1 解答：fill 两个 → 沙箱 → 粘合 → solved
    solve : {rest : List Frame} (d q f n : ℕ) (p : Path) (X step main : String) → Cont R p rest → Prog q p rest
    solve d q f n p X step main k =
      move (transport fill (codeOf p (X ++ₛ ".agda")) (specStub p) (draftOf p step main) {ok-++ p _}) λ where
        (rejected s)     → bounce d q f n p X ("fill " ++ₛ X ++ₛ ".agda: " ++ₛ s) k
        (filled (suc _)) → bounce d q f n p X (X ++ₛ ".agda still has postulates") k
        (filled zero)    →
          move (transport fill (codeOf p (X ++ₛ "Test.agda")) (specTest p) (draftOf p step (X ++ₛ "Test.agda")) {ok-++ p _}) λ where
            (rejected s)     → bounce d q f n p X ("fill " ++ₛ X ++ₛ "Test.agda: " ++ₛ s) k
            (filled (suc _)) → bounce d q f n p X (X ++ₛ "Test.agda still has postulates") k
            (filled zero)    →
              sandbox hSand (codes p X) λ where
                (failed msg) → bounce d q f n p X msg k
                pass → sandbox hGlue (codes p X) λ where
                  (failed msg) → bounce d q f n p X ("glue: " ++ₛ msg) k
                  pass         → finish q p (solved (codes p X)) k

    -- 7.2 分解：每个孩子的两段 stub whole 进 kids/K/spec/，再根正文 whole、根测试 fill，洞阶段沙箱，然后逐个开孩子
    writeKids : {rest : List Frame} (d q f n : ℕ) (p : Path) (X step main : String) (todo all : List String) → Cont R p rest → Prog q p rest
    writeKids d q f n p X step main []         all k = writeRoot d q f n p X step main all [] all k
    writeKids d q f n p X step main (K ∷ todo) all k = whole2 d q f n p X step K (writeKids d q f n p X step main todo all k) k

    -- 搬孩子 K 的两段 stub，然后接着 cont
    whole2 : {rest : List Frame} (d q f n : ℕ) (p : Path) (X step K : String) → Prog q p rest → Cont R p rest → Prog q p rest
    whole2 d q f n p X step K cont k =
      move (transport whole (kidStub p K) [] (draftOf p step (K ++ₛ ".agda")) {ok-++ p _}) λ where
        (rejected s) → bounce d q f n p X ("spec " ++ₛ K ++ₛ ".agda: " ++ₛ s) k
        (filled _)   →
          move (transport whole (kidTest p K) [] (draftOf p step (K ++ₛ "Test.agda")) {ok-++ p _}) λ where
            (rejected s) → bounce d q f n p X ("spec " ++ₛ K ++ₛ "Test.agda: " ++ₛ s) k
            (filled _)   → cont

    -- 根正文 whole、根测试 fill（留洞数写进 verdict/n），洞阶段沙箱：孩子们的 stub、再根的两个
    writeRoot : {rest : List Frame} (d q f n : ℕ) (p : Path) (X step main : String) (all : List String) (kept : Kids) (redo : List String)
              → Cont R p rest → Prog q p rest
    writeRoot d q f n p X step main all kept redo k =
      move (transport whole (codeOf p (X ++ₛ ".agda")) [] (draftOf p step main) {ok-++ p _}) λ where
        (rejected s) → bounce d q f n p X ("whole " ++ₛ X ++ₛ ".agda: " ++ₛ s) k
        (filled _)   →
          move (transport fill (codeOf p (X ++ₛ "Test.agda")) (specTest p) (draftOf p step (X ++ₛ "Test.agda")) {ok-++ p _}) λ where
            (rejected s) → bounce d q f n p X ("fill " ++ₛ X ++ₛ "Test.agda: " ++ₛ s) k
            (filled h)   →
              move (setN (verdict n) ("deferred=" ++ₛ show h)) λ _ →
              sandbox hSand (kidKeys p all ++ codes p X) λ where
                (failed msg) → bounce d q f n p X msg k
                pass         → kids d q f n p X redo kept k

    -- 7.3 逐个开孩子（配额给一半）；都回来了就粘合
    kids : {rest : List Frame} (d q f n : ℕ) (p : Path) (X : String) (todo : List String) (got : Kids) → Cont R p rest → Prog q p rest
    kids d q f n p X [] got k =
      sandbox hGlue (kidMods got ++ codes p X) λ where
        pass         → finish q p (solved (kidMods got ++ codes p X)) k
        (failed msg) → redesign d q f n p X (glueFailed msg) got k
    kids d q f n p X (K ∷ todo) got k =
      move (enter hSand (half q) (kidOf p K) {ok-half q} {ok-++ p _}) λ _ →
      nodeK d (half q) (kidOf p K) K λ q′ r →
      move leave λ _ →
      afterKid d (q - half q) f n p X K todo got r k

    afterKid : {rest : List Frame} (d q f n : ℕ) (p : Path) (X K : String) (todo : List String) (got : Kids) → Result → Cont R p rest → Prog q p rest
    afterKid d q f n p X K todo got (solved ms) k = kids d q f n p X todo (got ++ (K , ms) ∷ []) k
    afterKid d q f n p X K todo got (refuted r) k = redesign d q f n p X (kidRefuted K r) got k
    afterKid d q f n p X K todo got exhausted   k = redesign d q f n p X (kidExhausted K) got k

    -- 7.4 改设计：memo 记原因，再问；答卷里每个孩子 keep / whole / drop
    redesign : {rest : List Frame} (d q fuel n : ℕ) (p : Path) (X : String) → Why → Kids → Cont R p rest → Prog q p rest
    redesign d q zero    n p X why got k = move (setN (memo n) (showWhy why)) λ _ → finish q p exhausted k
    redesign d q (suc f) n p X why got k = move (setN (memo n) (showWhy why)) λ _ → redesignAsk d q f n p X why got k (fromDec (1 ≤ᵇ q))

    redesignAsk : {rest : List Frame} (d q f n : ℕ) (p : Path) (X : String) → Why → Kids → Cont R p rest
                → Maybe (Bool→Type (1 ≤ᵇ q)) → Prog q p rest
    redesignAsk d q f n p X why got k nothing   = finish q p exhausted k
    redesignAsk d q f n p X why got k (just pf) =
      move (ask (promptRedesign p X why) {pf}) λ names →
      redesigned d (predℕ q) f (suc n) p X (stepOf names) (classify X (filesOf names)) got k

    redesigned : {rest : List Frame} (d q f n : ℕ) (p : Path) (X step : String) → Kind → Kids → Cont R p rest → Prog q p rest
    redesigned d q f n p X step (design main ks) got k = compareKids d q f n p X step main ks ks got [] [] k
    redesigned d q f n p X step (solution main)  got k = dropGone n (map fst got) [] (solve d q f n p X step main k)   -- 不再分包：旧孩子全部丢弃
    redesigned d q f n p X step refute           got k = refuteStep d q f n p X step k
    redesigned d q f n p X step (malformed s)    got k = bounce d q f n p X ("malformed: " ++ₛ s) k

    -- 逐个孩子比 spec：在 got 里且两段逐字相同 → keep（result 照用）；否则 whole 两段、进重做表
    compareKids : {rest : List Frame} (d q f n : ℕ) (p : Path) (X step main : String) (todo all : List String) (got kept : Kids) (redo : List String)
                → Cont R p rest → Prog q p rest
    compareKids d q f n p X step main []         all got kept redo k =
      dropGone n (map fst got) all (writeRoot d q f n p X step main all kept redo k)
    compareKids d q f n p X step main (K ∷ todo) all got kept redo k =
      compareKid d q f n p X step main K todo all got kept redo k (lookupKid K got)

    compareKid : {rest : List Frame} (d q f n : ℕ) (p : Path) (X step main K : String) (todo all : List String) (got kept : Kids) (redo : List String)
               → Cont R p rest → Maybe (List Path) → Prog q p rest
    compareKid d q f n p X step main K todo all got kept redo k nothing =
      whole2 d q f n p X step K (compareKids d q f n p X step main todo all got kept (redo ++ K ∷ []) k) k
    compareKid d q f n p X step main K todo all got kept redo k (just ms) =
      move (get (kidStub p K)) λ oldS → move (get (kidTest p K)) λ oldT →
      move (get (draftOf p step (K ++ₛ ".agda"))) λ newS → move (get (draftOf p step (K ++ₛ "Test.agda"))) λ newT →
      if sameText oldS newS and sameText oldT newT
        then compareKids d q f n p X step main todo all got (kept ++ (K , ms) ∷ []) redo k
        else whole2 d q f n p X step K (compareKids d q f n p X step main todo all got kept (redo ++ K ∷ []) k) k

    -- 7.5 反驳：whole 进 code/XRefute.agda → audit → 沙箱里 check stub、test-stub、反驳 → refuted
    refuteStep : {rest : List Frame} (d q f n : ℕ) (p : Path) (X step : String) → Cont R p rest → Prog q p rest
    refuteStep d q f n p X step k =
      move (transport whole (refuteOf p X) [] (draftOf p step (X ++ₛ "Refute.agda")) {ok-++ p _}) λ where
        (rejected s) → bounce d q f n p X ("refute: " ++ₛ s) k
        (filled _)   →
          move (audit (refuteOf p X)) λ where
            false → bounce d q f n p X "unsafe: the refutation uses postulate / primitive / macro / tactic / unquote / a pragma" k
            true  →
              sandbox hSand (specStub p ∷ specTest p ∷ refuteOf p X ∷ []) λ where
                (failed msg) → bounce d q f n p X msg k
                pass         → finish q p (refuted (refuteOf p X)) k

-- 文件 agent：挂在前缀 p 上、树深 d、配额 q、模块名 X；结局是返回值，也写在 p/result
node : {rest : List Frame} (d q : ℕ) (p : Path) (X : String) → Run NodeSig (λ _ → Result) ((E⁻ , q , p) , rest)
node d q p X = Loop.nodeK (λ _ → Result) d q p X (λ _ r → done r)
