# 03 Env.agda：窗口 Σ 的四处改动

一句话：`Env.agda` 是 Agda 侧的窗口，节点能做的一切都是它的一个构造子。这次改四处：键与 realm 改成路径、`ask` 换参数与回应、加 `transport`、加 `audit`。
`Env` / `Code` / `Header` / `enter` / `leave` / `check` / `get` / `set` 的形状与前置条件不动。两条引理放在新文件 `Path.agda`。

## 0 现在的样子（不动的部分，方便对照）

```
 Env      base lib flags ∣ E ▸ (Code E × Iface)        语境（能 import 谁）× 余语境（flag）
 Header E imports（⊆ visible E）、flags（≼ flagsOf E）  子模块的头两行；两条证明算出来
 Code E   hd、body、fresh、opts-ok                       一个模块加它的头
 Frame    Env × ℕ × realm                                环境 × 剩余配额 × realm
 Ix       Frame × List Frame                             栈顶 × 其余
 Op ix    parse check eval render enter leave ask get set log sh goals give split
 next     check ok → E ▸ …；enter 压栈；leave 弹栈；ask 配额 −1；其余不变
```

前置条件都是 `Bool→Type (…)`：`enter` 要 `q ≤ᵇ 配额` 和 `prefixOf realm p`，`set` 要 `prefixOf realm k`，`ask` 要 `1 ≤ᵇ 配额`，`leave` 要 `hasParent`。
算成 `true` 就是 `tt`，算成 `false` 就写不出来（反例 `tests/neg/` 七个）。

## 1 改动一：键与 realm 改成路径（新文件 `src/Path.agda`）

### 为什么

`node` 是递归程序，前缀 p 是变量。`prefixOf p (p ++ "memo/1")` 对着 `primStringAppend` 算不动，
而且 `primStringEquality x x ≡ true` 没有内建引理可证（Agda.Builtin.String.Properties 只有两条 injective）。
路径按段存成列表，前缀判定用 `Keys.discreteString`（可判定相等，能 `with` 分情况），引理就能证了；字面量键照旧自动算出 `tt`。

### 定义

```agda
module Path where
open import Keys using (discreteString)

Path : Type
Path = List String                                   -- 一段一个字符串；"a/x" 写成 "a" ∷ "x" ∷ []

isPrefix : Path → Path → Bool                        -- 逐段比；用可判定相等，不用 primStringEquality
isPrefix []       _        = true
isPrefix (_ ∷ _)  []       = false
isPrefix (p ∷ ps) (k ∷ ks) = decRec (λ _ → isPrefix ps ks) (λ _ → false) (discreteString p k)

prefix-++ : ∀ p s → isPrefix p (p ++ s) ≡ true       -- 对 p 归纳；每段 with discreteString x x，no 的分支用 ¬p refl 排除
≤ᵇ-refl   : ∀ q → q ≤ᵇ q ≡ true                      -- 对 q 归纳

half : ℕ → ℕ                                         -- 给孩子分配额用：half 0 = 0 ; half 1 = 0 ; half (2+n) = 1 + half n
half-≤ : ∀ q → half q ≤ᵇ q ≡ true
prefix-refl : ∀ p → isPrefix p p ≡ true              -- 同前缀开沙箱 / 粘合帧
discretePath : Discrete Path                         -- discreteList discreteString；LogTx 用 Store Path String
join : Path → String                                 -- "a" ∷ "x" ∷ [] ↦ "a/x"：脚本余模型存 S.Board 的键、result 行里的键
```

`_≤ᵇ_` 也搬进 `Path.agda`（`≤ᵇ-refl` 要用它）；`Env` 用 `open import Path public using (Path; isPrefix; _≤ᵇ_)` 原样再导出，别的文件照旧从 `Env` 拿。

### 用法

```
 字面量键      set ("a" ∷ "x" ∷ []) "1"                        前置条件自动算成 tt，和现在一样
 变量前缀      set (p ++ "memo" ∷ "1" ∷ []) v {pf}              pf = subst Bool→Type (sym (prefix-++ p _)) tt
 分配额        enter h (half q) (p ++ "kids" ∷ K ∷ []) {pf₁} {pf₂}   pf₁ 由 half-≤，pf₂ 由 prefix-++
```

`Env.agda` 里改的只是类型：`Frame = Env × ℕ × Path`，`realmOf : Ix → Path`，`enter … (p : Path)`，`get : Path → Op`，`set : (k : Path) → String → …`，前置条件里的 `prefixOf` 换成 `isPrefix`。
原来的 `prefixOf`、`isPrefix`（字符版）删掉。

### 后端对应

后端收到的 realm 与键是字符串列表：realm 每段后加 `/` 接起来（`["a"]` → `"a/"`，根 `[]` → `""`），键段间用 `/`（`["a","x"]` → `"a/x"`）。
日志里的键和 `fold.py`、`store.sh`、dump 都不变。

## 2 改动二：`ask` 的参数是 Query，回应是文件名表

```agda
data Item : Type where
  lit  : String → Item          -- 固定文字：规则、输出格式
  row  : Path → Item            -- 一行的值：规约文本、反驳文本
  last : ℕ → Path → Item        -- 某前缀下最近 n 行：verdict/、memo/

Query : Type
Query = List Item

ask : {ix : Ix} → Query → {_ : Bool→Type (1 ≤ᵇ quotaOf ix)} → Op ix
Res (ask _) = List String       -- 答卷里的文件名；文件本身在 <realm>draft/<step>/<名字>
next (ask _) _ = 配额 −1        -- 不变
```

后端做什么见 `05-backend.md` §2。程序这边：拿到名字表就分类，要哪个文件再 `get`，不持答卷。

## 3 改动三：`transport`，写 code 行的唯一方式

```agda
data Move : Type where
  fill  : Move                  -- stub 的签名 + 答卷的子句；只换 postulate 块里的名字
  whole : Move                  -- 整个换成答卷

data Filled : Type where
  filled   : ℕ → Filled         -- 写好了；数 = 仍是 postulate 的名字个数（whole 恒为 0）
  rejected : String → Filled    -- 没写；原因

transport : {ix : Ix} (m : Move) (t s d : Path) {_ : Bool→Type (isPrefix (realmOf ix) t)} → Op ix
          -- t 目标键（必须在 realm 里）；s stub 键（fill 用，whole 忽略）；d 答卷键
Res (transport _ _ _ _) = Filled
next (transport …) _ = ix 不变
```

| m | 读 | 写到 t | 回 |
| --- | --- | --- | --- |
| fill | s 的 stub、d 的答卷 | stub 的 import / 定义 / 签名照抄，postulate 块里每个名字换成答卷里它的子句；答卷多出的声明追加 | `filled k`，k = 答卷里没给子句、仍留 postulate 的名字数 |
| whole | d 的答卷 | 答卷原文 | `filled 0`；答卷 parse 不了或模块名不对则 `rejected` |

`fill` 的精确算法在 `05-backend.md` §3。程序用它的两种方式：解答时要求 `filled 0`；洞阶段的根测试允许 `filled k`，k 写进 verdict。

## 4 改动四：`audit`，反驳的把门人

```agda
audit : {ix : Ix} → Path → Op ix
Res (audit _) = Bool            -- true = token 流里没有 postulate / primitive / macro / tactic / unquote* / 非 OPTIONS 的 pragma
next (audit _) _ = ix 不变
```

只用在反驳上：反驳在没有 `--safe` 的帧里查（它 import 的是 stub），所以它自己不能带任何 unsafe 的东西。
正文不需要 audit：粘合帧的 `--safe` 会抓。

## 4.5 改动五：`checkAt`，以及 `Env` 只记接口

agent 对孩子的 code 只有 open 没有 read（`02-agents.md` §2.3）。所以粘合与沙箱里 check 的是 **Store 里的键**，由检查器去读，agent 不持模块文本：

```agda
checkAt : {ix : Ix} → Header (envOf ix) → Path → Op ix
          -- h：允许的最大头（类型保证 imports ⊆ visible、flags ≼）；k：模块文本所在的键
Res (checkAt _ _) = Verdict            -- ok Iface ∣ fail 路径 报错原文
next (checkAt h k) (ok i) = E ▸ i      -- 和 check 一样：下一个模块能 import 它
```

后端读键的文本、parse、核对实际 import ⊆ h 的 import、检查、回接口（`05-backend.md` §3b）。
文本是真源码，所以报错带真实的行号列号，比 `check` 的树上路径好读。

为了让 `next` 不需要模块值，`Env` 的第二个构造子改成只记接口：

```agda
data Env where
  base : (ModName → Bool) → Flags → Env
  _▸_  : (E : Env) → Iface → Env                 -- 原来是 Code E × Iface；visible 用 Iface.name
```

`check : Code E → Op` 保留（DriveToy 还用它），`next (check c) (ok i) = E ▸ i`。`Code E` 里的 `fresh`、`opts-ok` 不变。

后果：`visible (E ▸ i) n` 取决于接口 i 的名字。i 是跑出来的数据时（`λ { (ok i) → … }` 里），"import 刚 check 过的模块"的头
不能再写 `tt`，要用 `mkHeader` / `mkCode` 在运行时造（名字对就 `just`）：ToyEnv 的 `M2 i`、`hKid i₁ i₂` 改成这样，DriveToy 原本就这样。
字面量环境（`E₀`、`E⁻`）下的头照旧 `tt`。

## 5 改动后的 Op 一览

| 构造子 | 变化 |
| --- | --- |
| `parse`、`check`、`eval`、`render`、`log`、`sh`、`goals`、`give`、`split` | 不变 |
| `enter h q p` | `p : Path`；前置条件 `isPrefix (realmOf ix) p` |
| `leave` | 不变 |
| `ask q` | `q : Query`；回 `List String` |
| `get k`、`set k v` | `k : Path`；`set` 前置条件 `isPrefix (realmOf ix) k` |
| `transport m t s d` | 新 |
| `audit k` | 新 |
| `checkAt h k` | 新：检查 Store 里键 k 的模块；h 是允许的最大头；ok 时环境多一个接口 |
| `Env._▸_` | 第二个分量从 `Code E × Iface` 改成 `Iface` |

`Res`、`next` 各加三行；`AgdaSig` 的定义不变。

## 6 跟着改的文件

| 文件 | 改什么 |
| --- | --- |
| `src/ToyEnv.agda` | 键写成路径；`W` 加一个步号和四张脚本（check 的判决、ask 的答卷、transport 的回应、audit 的回应）；`respS` 补 ask / transport / audit / checkAt 四个分支；`M2 i`、`hKid i₁ i₂` 改用 mkHeader / mkCode（见 `06-toys-tests.md` §1） |
| `src/StoreToy.agda` | 十一个程序的键改成路径，如 `"a" ∷ "x" ∷ []`；§7 九条 refl 的值不变 |
| `src/DriveToy.agda` | `kid` 等用到 realm 的地方改成路径；新程序见 `06-toys-tests.md` §3 |
| `tests/neg/NegRealm.agda`、`NegWiden.agda` | 键与 realm 改成路径；仍必须失败 |
| `tests/gen/LogTx.agda`、`tests/store/logtx.py` | 日志里的键 `"a/x"` 转成 Agda 时按 `/` 拆成列表；生成的文件自己实例化 `module S = Store Path String discretePath discreteString` |

## 7 验收

| 编号 | 标准 | 命令 | 期望 |
| --- | --- | --- | --- |
| E1 | 全部模块通过 | `./check.sh` | 无 `error`，退出码 0 |
| E2 | 字面量键照旧自动算出 | `src/StoreToy.agda` 不写任何显式证明就通过 | 包含在 E1 |
| E3 | 变量前缀用引理能写出 | `src/Node.agda` 里 `setN`、`enterKid` 通过 | 包含在 E1 |
| E4 | 两条引理 | `Path.agda` 里 `_ : isPrefix ("a" ∷ []) ("a" ∷ "x" ∷ []) ≡ true ; _ = refl`；`prefix-++`、`≤ᵇ-refl`、`half-≤` 通过 | 包含在 E1 |
| E5 | 旧反例仍被拒 | `./neg.sh` | 七行 `rejected as expected` |
| E6 | 新反例被拒 | `./neg.sh` | 再三行：`NegTransport`（transport 的目标在 realm 外）、`NegNote`（NodeSig 的 set 写 code/，Note 没有这个构造子）、`NegPeek`（孩子的头想 import 父刚 check 的模块） |
| E7 | ToyEnv 五条 refl 不变 | `./check.sh` | 包含在 E1 |
| E8 | 日志转 Agda 仍 refl | `./store.sh` 的 F 组 | `F3 LogTx: ok`（键按 `/` 拆成路径后 `S.runTx` 仍按 refl 算） |
| E9 | `_▸_` 只记接口后 ToyEnv、DriveToy、Node 都通过；`M2 i`、`hKid i₁ i₂` 这类依赖接口名字的头在运行时用 mkHeader / mkCode 造，ToyEnv 五条 refl 的值不变 | `./check.sh` | 包含在 E1 |

结果（2026-10-22，M0）：E1–E9 全过。E6 三个新反例失败的原因：NegTransport 是 realm 证明无解（Unsolved metas），NegNote 是 `Op` 对不上 `NodeOp`，NegPeek 是 `Unit` 对不上 `⊥`。

搞乱了的典型症状：`check.sh` 在 `Env.agda` 报 `prefixOf` 未定义 → 某处还用着旧名字；在 `StoreToy.agda` 报 `String != List String` → 哪个键没改成路径。
