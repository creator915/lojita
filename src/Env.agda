{-# OPTIONS --safe --cubical #-}
------------------------------------------------------------------------
-- Env.agda —— 环境、Code E、头、签名 AgdaSig
--   Env      环境 = 父给的库与模式 ▸ 过了检查的模块（接口由后端算，作数据带回）
--   Code E   一个模块加它的头（import 谁、开什么 flag）。头必须落在 E 的视野与模式里：
--            Env 用 Code E，Code E 用对 Env 递归的 visible / flagsOf —— 归纳–递归，只管模块边界；
--            声明内部的名字交给 Agda 的 scope checker，不在类型里重做
--   Ix       栈：每层一个 (环境 , 剩余配额 , realm 前缀)；enter 压栈、leave 弹栈。父开子只能给子集、更严的 flag、更少的配额、更窄的 realm
--   get/set  世界 = Store String String（Keys.agda 的 S）：后端 --cubical-handler=store:DIR 在硬盘上实现 S.world；
--            get 在 realm 外读到 nothing（restrictL），set 只能写 realm 里的键（越界是类型错，比 mergeL 的丢弃更严）
--   sh       动世界的那一步（方案里的 run；run 这个名字仓库里已被占用）：后端 --cubical-handler=sh:DIR 才作答
--   Op/Res/next   一拍能走的步、回应、下一拍在哪（▷ 来自 Later.agda：check 过了，下一拍才看得见新模块）
--   后端（agda 进程）是这个签名的余模型；Agda 这边一个 postulate 都没有。脚本余模型见 ToyEnv.agda
------------------------------------------------------------------------
module Env where

open import Cubical.Foundations.Prelude using (Type)
open import Cubical.Data.List.Base using (List; []; _∷_)
open import Cubical.Data.Bool.Base using (Bool; true; false; _and_; _or_; not; Bool→Type)
open import Cubical.Data.Nat.Base using (ℕ; zero; suc; predℕ)
open import Agda.Builtin.Nat using (_-_)
open import Cubical.Data.Sigma using (_×_; _,_; fst; snd)
open import Cubical.Data.Maybe.Base using (Maybe; nothing; just)
open import Cubical.Data.Unit.Base using (Unit; tt)
open import Agda.Builtin.String using (String; primStringEquality; primStringAppend; primStringToList)
open import Agda.Builtin.Char using (Char; primCharEquality)
open import Syntax
open import FlagTable
open import Later using (TSig)

------------------------------------------------------------------------
-- §1 零件：名字、模块名、flag
------------------------------------------------------------------------
ModName : Type
ModName = List String

_=ₛ_ : String → String → Bool
_=ₛ_ = primStringEquality

_=ₘ_ : ModName → ModName → Bool
[]       =ₘ []       = true
(x ∷ xs) =ₘ (y ∷ ys) = (x =ₛ y) and (xs =ₘ ys)
_        =ₘ _        = false

_∈ₘ_ : ModName → List ModName → Bool
n ∈ₘ []       = false
n ∈ₘ (m ∷ ms) = (n =ₘ m) or (n ∈ₘ ms)

_∈ₛ_ : String → List String → Bool
s ∈ₛ []       = false
s ∈ₛ (t ∷ ts) = (s =ₛ t) or (s ∈ₛ ts)

allᵇ : {A : Type} → (A → Bool) → List A → Bool
allᵇ p []       = true
allᵇ p (x ∷ xs) = p x and allᵇ p xs

_⊆ₛ_ : List String → List String → Bool
xs ⊆ₛ ys = allᵇ (_∈ₛ ys) xs

_≤ᵇ_ : ℕ → ℕ → Bool
zero  ≤ᵇ _     = true
suc _ ≤ᵇ zero  = false
suc m ≤ᵇ suc n = m ≤ᵇ n

-- 前缀：realm 的判定。prefixOf p k = k 以 p 开头；空前缀 "" 是整张表（Store 的 whole）
isPrefix : List Char → List Char → Bool
isPrefix []       _        = true
isPrefix (_ ∷ _)  []       = false
isPrefix (p ∷ ps) (c ∷ cs) = primCharEquality p c and isPrefix ps cs

prefixOf : String → String → Bool
prefixOf p k = isPrefix (primStringToList p) (primStringToList k)

-- 名字串：Name 的各段接起来，洞写成 "_"
partStr : NamePart → String
partStr Hole   = "_"
partStr (Id s) = s

partsStr : List NamePart → String
partsStr []       = ""
partsStr (p ∷ ps) = primStringAppend (partStr p) (partsStr ps)

nameStr : Name → String
nameStr (Name′ _ (p ∷¹ ps)) = primStringAppend (partStr p) (partsStr ps)
nameStr NoName              = "_"

qnameMod : QName → ModName
qnameMod (QName′ n) = nameStr n ∷ []
qnameMod (Qual n q) = nameStr n ∷ qnameMod q

-- 模块自己说的名字与 OPTIONS（只看文件顶上的 pragma，和 Agda 一样）
modNameOf : Module → ModName
modNameOf (Mod q _ _) = qnameMod q

optionsOf : Module → List String
optionsOf (Mod _ ps _) = go ps
  where
    _++ₛ_ : List String → List String → List String
    []       ++ₛ ys = ys
    (x ∷ xs) ++ₛ ys = x ∷ (xs ++ₛ ys)
    go : List Pragma → List String
    go []                     = []
    go (OptionsPragma ss ∷ ps) = ss ++ₛ go ps
    go (_ ∷ ps)               = go ps

-- flag：子 ≼ 父 —— infective 的子不能多开（父没开的子不能开），coinfective 的子不能关（父开了子必须开）
Flags : Type
Flags = List String

isInf isCoinf : String → Bool
isInf f with flagKind f
... | infective = true
... | _         = false
isCoinf f with flagKind f
... | coinfective = true
... | _           = false

_≼_ : Flags → Flags → Bool
child ≼ parent = allᵇ (λ f → not (isInf f) or (f ∈ₛ parent)) child
             and allᵇ (λ f → not (isCoinf f) or (f ∈ₛ child)) parent

------------------------------------------------------------------------
-- §2 接口、环境、头、Code E：归纳–递归
------------------------------------------------------------------------
-- 后端算出来、作为数据带回的接口：名字、导出表、用的 flag、模块指纹
-- 导出表的一行 = 数据库的一条：名字、类型（仍是语法）、定义里用到的名字（依赖）、这条声明的指纹
record Export : Type where
  constructor export
  field
    name : String
    type : Expr
    deps : List String
    hash : ℕ

record Iface : Type where
  constructor iface
  field
    name    : ModName
    exports : List Export
    options : Flags
    hash    : ℕ

data Env : Type
visible : Env → ModName → Bool          -- 语境：能 import 谁
flagsOf : Env → Flags                   -- 余语境：这个实例在什么模式下检查
record Header (E : Env) : Type
record Code   (E : Env) : Type

-- 头 = 子模块的头两行：import 谁（必须看得见）、开什么 flag（必须 ≼ 环境的）
record Header E where
  constructor header
  field
    imports    : List ModName
    flags      : Flags
    imports-ok : Bool→Type (allᵇ (visible E) imports)
    flags-ok   : Bool→Type (flags ≼ flagsOf E)
open Header public

-- Code E = 头 + 模块：模块的名字是新的，模块自己写的 OPTIONS 不超出头里的 flag。
-- 模块体里真正 import 了谁由后端核对（实际 ⊆ 头），对不上就 fail。
record Code E where
  constructor code
  field
    hd      : Header E
    body    : Module
    fresh   : Bool→Type (not (visible E (modNameOf body)))
    opts-ok : Bool→Type (optionsOf body ⊆ₛ flags hd)
open Code public

data Env where
  base : (ModName → Bool) → Flags → Env   -- 父给的：哪些库模块可见、什么模式
  _▸_  : (E : Env) → Code E × Iface → Env  -- 过了检查的模块：下一拍才在这
infixl 5 _▸_

visible (base lib _)  n = lib n
visible (E ▸ (c , _)) n = visible E n or (modNameOf (body c) =ₘ n)

flagsOf (base _ fl) = fl
flagsOf (E ▸ _)     = flagsOf E

-- 子实例的环境：只看得见头里列的模块、只开头里的 flag
child : (E : Env) → Header E → Env
child E h = base (_∈ₘ imports h) (flags h)

------------------------------------------------------------------------
-- §3 栈与步：签名 AgdaSig
------------------------------------------------------------------------
Frame : Type
Frame = Env × ℕ × String        -- 环境 × 剩余配额（问 LLM 一次扣一）× realm 前缀（"" = 整张表）

Ix : Type
Ix = Frame × List Frame         -- 栈顶 × 其余

envOf : Ix → Env
envOf ((E , _ , _) , _) = E

quotaOf : Ix → ℕ
quotaOf ((_ , q , _) , _) = q

realmOf : Ix → String
realmOf ((_ , _ , r) , _) = r

hasParent : Ix → Bool              -- 不在根上
hasParent (_ , [])    = false
hasParent (_ , _ ∷ _) = true

data Verdict : Type where       -- check 的回应
  ok   : Iface → Verdict               -- 过了：接口
  fail : List ℕ → String → Verdict     -- 没过：树上的路径 + 报错原文

data Answer : Type where        -- eval 的回应
  value : Expr → Answer                -- 规范形（仍是语法）
  error : String → Answer

-- 编辑器那一组步的回应：洞 = Agda 自己的 ?
record Goal : Type where
  constructor goal
  field
    id   : ℕ                           -- Agda 的洞号（按出现顺序）
    path : List ℕ                      -- 洞在树上的路径
    type : Expr                        -- 目标类型（语法）

data Goals : Type where
  holes   : List Goal → Goals
  noCheck : String → Goals             -- 模块本身没过检查

data Edit : Type where
  edited   : Module → Edit             -- 改过的树（洞填上了 / 子句拆开了），下一拍 check 它
  rejected : String → Edit

data Op : Ix → Type where
  parse  : {ix : Ix} → String → Op ix                             -- 文本 → 树（parser）
  check  : {ix : Ix} → Code (envOf ix) → Op ix                    -- 检查一个模块（createInterface）
  eval   : {ix : Ix} → Header (envOf ix) → Expr → Op ix           -- 在头的视野里算一个表达式
  render : {ix : Ix} → Module → Op ix                             -- 树 → 规范文本
  enter  : {ix : Ix} (h : Header (envOf ix)) (q : ℕ) (p : String)                                -- 开子实例：配额 q，realm p
           {_ : Bool→Type (q ≤ᵇ quotaOf ix)} {_ : Bool→Type (prefixOf (realmOf ix) p)} → Op ix   --   只能比父少、比父窄
  leave  : {ix : Ix} → {_ : Bool→Type (hasParent ix)} → Op ix     -- 回到父实例（根上写不出来）
  ask    : {ix : Ix} → String → {_ : Bool→Type (1 ≤ᵇ quotaOf ix)} → Op ix   -- 问 LLM，扣一份配额
  get    : {ix : Ix} → String → Op ix                             -- 读一个键；realm 外读到 nothing
  set    : {ix : Ix} (k : String) → String → {_ : Bool→Type (prefixOf (realmOf ix) k)} → Op ix   -- 写一个键；只能写 realm 里的
  log    : {ix : Ix} → String → Op ix
  sh     : {ix : Ix} → String → Op ix                             -- 动世界：在实例所在的目录跑一条 shell 命令
  -- 编辑器：都在头的视野里检查一遍带洞的模块，不改环境
  goals  : {ix : Ix} → Header (envOf ix) → Module → Op ix                   -- 洞的表
  give   : {ix : Ix} → Header (envOf ix) → Module → ℕ → Expr → Op ix        -- 往第 k 个洞里填
  split  : {ix : Ix} → Header (envOf ix) → Module → ℕ → String → Op ix      -- 在第 k 个洞按变量分情况

Res : {ix : Ix} → Op ix → Type
Res (parse _)    = Maybe Module
Res (check _)    = Verdict
Res (eval _ _)   = Answer
Res (render _)   = String
Res (enter _ _ _) = Unit
Res leave        = Unit
Res (ask _)      = String
Res (get _)      = Maybe String
Res (set _ _)    = Unit
Res (log _)      = Unit
Res (sh _)       = ℕ × String        -- 退出码 × 输出（stdout 与 stderr 合流；超时退出码 124）
Res (goals _ _)     = Goals
Res (give _ _ _ _)  = Edit
Res (split _ _ _ _) = Edit

next : {ix : Ix} (o : Op ix) → Res o → Ix
next {(E , q , r) , rest} (check c)    (ok i)     = (E ▸ (c , i) , q , r) , rest    -- ▷：下一拍才看得见
next {ix}               (check _)    (fail _ _) = ix
next {(E , q , r) , rest} (enter h q′ p) _        = (child E h , q′ , p) , ((E , q - q′ , r) ∷ rest)
next {F , G ∷ rest}     leave        _          = G , rest
next {F , []}           leave        _          = F , []        -- 到不了：hasParent 不成立
next {(E , q , r) , rest} (ask _)      _          = (E , predℕ q , r) , rest
next {ix}               (parse _)    _          = ix
next {ix}               (eval _ _)   _          = ix
next {ix}               (render _)   _          = ix
next {ix}               (get _)      _          = ix
next {ix}               (set _ _)    _          = ix
next {ix}               (log _)      _          = ix
next {ix}               (sh _)       _          = ix
next {ix}               (goals _ _)     _       = ix
next {ix}               (give _ _ _ _)  _       = ix
next {ix}               (split _ _ _ _) _       = ix

AgdaSig : TSig Ix
AgdaSig = record { Op = Op ; Res = Res ; next = next }

------------------------------------------------------------------------
-- §4 运行时造头、造 Code：模块是跑出来的数据时，证明要算出来
--   fromDec 把一个算出来的布尔变成"有没有证明"；有就 just tt
------------------------------------------------------------------------
fromDec : (b : Bool) → Maybe (Bool→Type b)
fromDec true  = just tt
fromDec false = nothing

mkHeader : (E : Env) → List ModName → Flags → Maybe (Header E)
mkHeader E is fl with fromDec (allᵇ (visible E) is) | fromDec (fl ≼ flagsOf E)
... | just p | just q = just (header is fl p q)
... | _      | _      = nothing

mkCode : (E : Env) → Header E → Module → Maybe (Code E)
mkCode E h m with fromDec (not (visible E (modNameOf m))) | fromDec (optionsOf m ⊆ₛ flags h)
... | just p | just q = just (code h m p q)
... | _      | _      = nothing
