{-# OPTIONS --safe --cubical #-}
------------------------------------------------------------------------
-- Code.agda —— 代码的类型：程序是箭头，环境是点
--   Env        环境 = 签名链：从库 Γ₀（= ε）出发，一次装进一条声明。它是数据：装了什么它就是什么
--   Decl Γ     在 Γ 上能写的一条声明。它能引用的名字 Name k Γ = Fin (count k Γ) 由 Γ 算出：
--              Env 用 Decl 定义，count 对 Env 递归，Decl 的构造子又用 count ——归纳–递归
--   Term Γ n   子句右边的项层（照 Agda 的 Term 画），n 个局部变量
--   Code Γ Γ′  程序 = 声明序列 = 从 Γ 到 Γ′ 的一条路；范畴 EnvCat：对象 = 环境，箭头 = 程序
--   U / El     工具的接口（一阶、可判定）：接口写在声明里是数据，体由后端查
-- Agda 里不查类型、不求值：那是后端的事（Load.agda：后端是签名的余模型）。
-- 库是三个参数：库里定义名、构造子名各有几个，和每个定义的参数个数。
------------------------------------------------------------------------
open import Cubical.Foundations.Prelude
open import Cubical.Relation.Nullary
open import Cubical.Data.Nat
open import Cubical.Data.Nat.Properties using (discreteℕ)
open import Cubical.Data.Bool.Base
open import Cubical.Data.Unit
open import Cubical.Data.Empty using (⊥)
open import Cubical.Data.Sigma
open import Cubical.Data.Sum using (_⊎_ ; inl ; inr) renaming (map to ⊎-map)
open import Cubical.Data.List
open import Cubical.Data.Maybe
open import Cubical.Data.SumFin.Base using (Fin ; fzero ; fsuc ; toℕ)
open import Agda.Builtin.String using (String)
open import Later using (module PathOf)

module Code (libD libC : ℕ) (libPars : Fin libD → ℕ) where

------------------------------------------------------------------------
-- §0 接口宇宙：工具的参数和结果只能是这些类型
--   一阶、可判定、能写进棋谱、能过进程边界。限制写在接口上，不写在体上。
------------------------------------------------------------------------
data U : Type where
  nat unit bool str : U
  list maybe        : U → U
  pair              : U → U → U

El : U → Type
El nat        = ℕ
El unit       = Unit
El bool       = Bool
El str        = String
El (list a)   = List (El a)
El (maybe a)  = Maybe (El a)
El (pair a b) = El a × El b

dflt : (u : U) → El u                      -- 每个接口类型一个默认值（玩具后端用）
dflt nat        = 0
dflt unit       = tt
dflt bool       = false
dflt str        = ""
dflt (list a)   = []
dflt (maybe a)  = nothing
dflt (pair a b) = dflt a , dflt b

------------------------------------------------------------------------
-- §1 零件
------------------------------------------------------------------------
data Kind : Type where                      -- 三种名字
  dn : Kind                                 --   定义：函数 / 数据类型 / 记录 / 字段 / 工具
  cn : Kind                                 --   构造子
  tn : Kind                                 --   工具（工具同时也是定义，两种名字指同一个东西）

data Vis : Type where                       -- 参数可见性：(x : A) / {x : A} / ⦃ x : A ⦄
  vis hid ins : Vis

data Lit : Type where                       -- 字面量
  natL : ℕ → Lit
  strL : String → Lit

libCount : Kind → ℕ                         -- 库里各种名字的个数
libCount dn = libD
libCount cn = libC
libCount tn = 0

-- 名字按数字写：# 2 是第 2 个（从 0 数）。m < n 由计算给出，越界是编译错误，不用写证明
ltᵇ : ℕ → ℕ → Bool
ltᵇ _       zero    = false
ltᵇ zero    (suc _) = true
ltᵇ (suc m) (suc n) = ltᵇ m n

#_ : {n : ℕ} (m : ℕ) {_ : Bool→Type (ltᵇ m n)} → Fin n
#_ {suc n} zero        = fzero
#_ {suc n} (suc m) {p} = fsuc (#_ {n} m {p})
#_ {zero}  m       {()}

-- 把 Fin (m + n) 拆成"前 m 个"和"后 n 个"：查一个名字是老的还是这条声明新引入的
split : (m : ℕ) {n : ℕ} → Fin (m + n) → Fin m ⊎ Fin n
split zero    i       = inr i
split (suc m) fzero    = inl fzero
split (suc m) (fsuc i) = ⊎-map fsuc (λ j → j) (split m i)

------------------------------------------------------------------------
-- §2 环境、声明、项：一个归纳–递归块
--   Env 的构造子 _▸_ 要 Decl Γ；Decl Γ 的构造子要 Name k Γ = Fin (count k Γ)；
--   count 对 Env 递归、newCount 对 Decl 递归。所以 Env / Decl / count 必须一起定义。
--   作用域由类型保证（引用不存在的名字写不出来），类型正确与否交给后端。
------------------------------------------------------------------------
data Env : Type
data Decl (Γ : Env) : Type
data Term (Γ : Env) (n : ℕ) : Type
data Pat  (Γ : Env) (n : ℕ) : Type
data Clause (Γ : Env) : Type

count    : Kind → Env → ℕ                           -- Γ 里每种名字有几个
newCount : Kind → {Γ : Env} → Decl Γ → ℕ           -- 一条声明引入几个

Name : Kind → Env → Type                            -- 名字 = 小于 count 的数（层号：库在前，越早越小）
Name k Γ = Fin (count k Γ)

pars    : (Γ : Env) → Name dn Γ → ℕ                 -- 数据类型 / 记录的参数个数（函数记 0）
parsAt  : (Γ : Env) (d : Decl Γ) → Name dn Γ ⊎ Fin (newCount dn d) → ℕ
parsNew : {Γ : Env} (d : Decl Γ) → Fin (newCount dn d) → ℕ

Terms : Env → ℕ → ℕ → Type                          -- k 个项，各带 n 个局部变量（构造子的类型）
Tel   : Env → ℕ → ℕ → Type                          -- 望远镜：k 个项，后一个比前一个多一个变量（记录的字段）

data Env where
  ε   : Env                                         -- 库（Γ₀）
  _▸_ : (Γ : Env) → Decl Γ → Env                    -- 装进一条
infixl 5 _▸_

data Decl Γ where
  sig     : Term Γ 0 → Decl Γ                                        -- f : A             引入 1 个 dn
  tool    : U → U → Decl Γ                                           -- f : El c → El r   引入 1 个 dn、1 个 tn
  fun     : Name dn Γ → List (Clause Γ) → Decl Γ                     -- f 的子句           不引入名字
  datasig : (p : ℕ) → Term Γ 0 → Decl Γ                              -- data D : (p 个参数) → … → Set   引入 1 个 dn
  datadef : (D : Name dn Γ) (k : ℕ) → Terms Γ (pars Γ D) k → Decl Γ  -- D 的 k 个构造子（参数在作用域里）引入 k 个 cn
  recsig  : (p : ℕ) → Term Γ 0 → Decl Γ                              -- record R : (p 个参数) → Set     引入 1 个 dn
  recdef  : (R : Name dn Γ) (k : ℕ) → Tel Γ (pars Γ R) k → Decl Γ    -- R 的 k 个字段       引入 k 个 dn、1 个 cn

data Term Γ n where
  var  : Fin n → List (Vis × Term Γ n) → Term Γ n    -- 局部变量（de Bruijn）加参数
  lam  : Vis → Term Γ (suc n) → Term Γ n             -- λ：体内 0 号变量是新绑定的
  lit  : Lit → Term Γ n
  def  : Name dn Γ → List (Vis × Term Γ n) → Term Γ n  -- 环境里的定义（函数 / 类型 / 记录 / 字段 / 工具）
  con  : Name cn Γ → List (Vis × Term Γ n) → Term Γ n  -- 构造子
  pi   : Vis → Term Γ n → Term Γ (suc n) → Term Γ n  -- (x : A) → B；B 里 0 号变量是 x
  sort : ℕ → Term Γ n                                -- Set n
  meta : ℕ → Term Γ n                                -- 洞：编辑器的对象（§5）；作用域就是它所在的 (Γ , n)

data Pat Γ n where                                   -- n = 这条子句的模式变量个数
  pvar    : Fin n → Pat Γ n
  pcon    : Name cn Γ → List (Vis × Pat Γ n) → Pat Γ n
  pdot    : Term Γ n → Pat Γ n
  plit    : Lit → Pat Γ n
  pproj   : Name dn Γ → Pat Γ n                      -- 余模式：取字段
  pabsurd : Fin n → Pat Γ n

data Clause Γ where
  clause : (k : ℕ) → List (Vis × Pat Γ k) → Term Γ k → Clause Γ   -- k 个模式变量，左边，右边
  absurd : (k : ℕ) → List (Vis × Pat Γ k) → Clause Γ

count k ε       = libCount k
count k (Γ ▸ d) = count k Γ + newCount k d

newCount dn (sig _)         = 1
newCount dn (tool _ _)      = 1
newCount dn (fun _ _)       = 0
newCount dn (datasig _ _)   = 1
newCount dn (datadef _ _ _) = 0
newCount dn (recsig _ _)    = 1
newCount dn (recdef _ k _)  = k
newCount cn (datadef _ k _) = k
newCount cn (recdef _ _ _)  = 1
newCount cn _               = 0
newCount tn (tool _ _)      = 1
newCount tn _               = 0

pars ε       i = libPars i
pars (Γ ▸ d) i = parsAt Γ d (split (count dn Γ) i)

parsAt Γ d (inl j) = pars Γ j                       -- 老名字：到 Γ 里查
parsAt Γ d (inr j) = parsNew d j                    -- 新名字：这条声明说了算

parsNew (datasig p _) _ = p
parsNew (recsig  p _) _ = p
parsNew _             _ = 0

Terms Γ n zero    = Unit
Terms Γ n (suc k) = Term Γ n × Terms Γ n k

Tel Γ n zero    = Unit
Tel Γ n (suc k) = Term Γ n × Tel Γ (suc n) k

------------------------------------------------------------------------
-- §3 工具的接口：对 Γ 递归查。call 的参数类型、结果类型由此算出（Load.agda）
------------------------------------------------------------------------
ifaceNew : {Γ : Env} (d : Decl Γ) → Fin (newCount tn d) → U × U
ifaceNew (tool c r) _ = c , r
ifaceNew _          _ = unit , unit                 -- 其它声明不引入工具名（Fin 0），到不了

iface   : (Γ : Env) → Name tn Γ → U × U
ifaceAt : (Γ : Env) (d : Decl Γ) → Name tn Γ ⊎ Fin (newCount tn d) → U × U
iface ε       ()
iface (Γ ▸ d) t = ifaceAt Γ d (split (count tn Γ) t)
ifaceAt Γ d (inl j) = iface Γ j
ifaceAt Γ d (inr j) = ifaceNew d j

callOf resOf : (Γ : Env) → Name tn Γ → U
callOf Γ t = fst (iface Γ t)
resOf  Γ t = snd (iface Γ t)

------------------------------------------------------------------------
-- §4 程序 = 路：Code Γ Γ′ 是从 Γ 到 Γ′ 的一串声明；EnvCat 是环境的范畴
--   对象 = 环境，箭头 = 程序，合成 = 拼接。范畴式代码编辑器编辑的是箭头。
------------------------------------------------------------------------
open PathOf Decl (λ {Γ} d → Γ ▸ d) public
  renaming (Walk to Code ; Cat to EnvCat ; [] to ∅ ; _∷_ to _▹_
           ; _++_ to _⋆_ ; ++-unit-r to ⋆-unit-r ; ++-assoc to ⋆-assoc)

-- 每个环境恰是一条从库出发的程序：环境 = 程序的 fold，程序 = 环境的日志
path : (Γ : Env) → Code ε Γ
path ε       = ∅
path (Γ ▸ d) = path Γ ⋆ (d ▹ ∅)

------------------------------------------------------------------------
-- §5 洞：编辑器的对象层
--   一个洞的作用域就是它所在的 (Γ , n)；填洞 = 给它一个 Term Γ n；表按洞号（ℕ）查。
--   程序层的洞不另造：sig 了还没 fun 的名字就是程序层的洞（Agda 自己的"先声明后定义"）。
------------------------------------------------------------------------
Holes : Env → Type
Holes Γ = ℕ → Maybe (Σ[ n ∈ ℕ ] Term Γ n)

fillHole : {Γ : Env} → Holes Γ → ℕ → (Σ[ n ∈ ℕ ] Term Γ n) → Holes Γ
fillHole θ m t m′ = decRec (λ _ → just t) (λ _ → θ m′) (discreteℕ m m′)

-- 把填了的洞代进去（Agda 的 instantiateFull）：作用域对得上才代，对不上洞留着
zonk  : {Γ : Env} {n : ℕ} → Holes Γ → Term Γ n → Term Γ n
zonks : {Γ : Env} {n : ℕ} → Holes Γ → List (Vis × Term Γ n) → List (Vis × Term Γ n)
zonk θ (var i as) = var i (zonks θ as)
zonk θ (lam v t)  = lam v (zonk θ t)
zonk θ (lit l)    = lit l
zonk θ (def f as) = def f (zonks θ as)
zonk θ (con c as) = con c (zonks θ as)
zonk θ (pi v a b) = pi v (zonk θ a) (zonk θ b)
zonk θ (sort s)   = sort s
zonk {Γ} {n} θ (meta m) = at (θ m)
  where
    at : Maybe (Σ[ n′ ∈ ℕ ] Term Γ n′) → Term Γ n
    at nothing         = meta m
    at (just (n′ , t)) = decRec (λ p → subst (Term Γ) p t) (λ _ → meta m) (discreteℕ n′ n)
zonks θ []             = []
zonks θ ((v , t) ∷ as) = (v , zonk θ t) ∷ zonks θ as

zonkP  : {Γ : Env} {n : ℕ} → Holes Γ → Pat Γ n → Pat Γ n
zonkPs : {Γ : Env} {n : ℕ} → Holes Γ → List (Vis × Pat Γ n) → List (Vis × Pat Γ n)
zonkP θ (pvar i)    = pvar i
zonkP θ (pcon c ps) = pcon c (zonkPs θ ps)
zonkP θ (pdot t)    = pdot (zonk θ t)
zonkP θ (plit l)    = plit l
zonkP θ (pproj f)   = pproj f
zonkP θ (pabsurd i) = pabsurd i
zonkPs θ []             = []
zonkPs θ ((v , p) ∷ ps) = (v , zonkP θ p) ∷ zonkPs θ ps

zonkC : {Γ : Env} → Holes Γ → Clause Γ → Clause Γ
zonkC θ (clause k ps t) = clause k (zonkPs θ ps) (zonk θ t)
zonkC θ (absurd k ps)   = absurd k (zonkPs θ ps)

zonkTs : {Γ : Env} {n : ℕ} → Holes Γ → (k : ℕ) → Terms Γ n k → Terms Γ n k
zonkTs θ zero    _        = tt
zonkTs θ (suc k) (t , ts) = zonk θ t , zonkTs θ k ts

zonkTel : {Γ : Env} {n : ℕ} → Holes Γ → (k : ℕ) → Tel Γ n k → Tel Γ n k
zonkTel θ zero    _        = tt
zonkTel θ (suc k) (t , ts) = zonk θ t , zonkTel θ k ts

zonkD : {Γ : Env} → Holes Γ → Decl Γ → Decl Γ
zonkD θ (sig A)          = sig (zonk θ A)
zonkD θ (tool c r)       = tool c r
zonkD θ (fun f cs)       = fun f (map (zonkC θ) cs)
zonkD θ (datasig p A)    = datasig p (zonk θ A)
zonkD θ (datadef D k cs) = datadef D k (zonkTs θ k cs)
zonkD θ (recsig p A)     = recsig p (zonk θ A)
zonkD θ (recdef R k fs)  = recdef R k (zonkTel θ k fs)
