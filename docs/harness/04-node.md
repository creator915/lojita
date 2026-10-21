# 04 Node.agda：文件 agent 的程序

一句话：`node d p` 是挂在前缀 p 上的文件 agent。它只用 `NodeSig` 里的步，每一轮 ask 一次、分类答卷、搬运、沙箱里 check，
解答就粘合，分解就逐个开孩子，反驳就交反驳；结局写进 `p/result` 再返回。全部分支都是有限树上的程序，`soundHonest` 对它成立。

## 0 文件结构

```
 §1 类型        Spec  Result  Note  Why
 §2 签名        NodeOp（NodeSig 的步）  embed : NodeOp ix → Op ix  embedRun
 §3 键          p ++ …：specStub specTest codeOf draftOf kidOf noteKey；setN / enterKid 把引理包好
 §4 答卷        classify（文件名表 → 解答 / 分解 / 反驳 / 不合格）；hMax（沙箱里允许的最大头）
 §5 帧          sandbox  checkAll  glue
 §6 提示词      rules  promptFirst  promptRetry  promptRedesign（都是 Query）
 §7 主循环      node  loop  solve  design  kids  redesign  refute
```

## 1 类型

```agda
record Spec : Type where                 -- 孩子的身份：模块名；stub 与 test 两段文本在 p/spec/ 行里
  field name : String

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
```

## 2 NodeSig：工具注册表

```agda
data NodeOp : Ix → Type where
  ask       : {ix} → Query → {1 ≤ᵇ quotaOf ix} → NodeOp ix
  get       : {ix} → Path → NodeOp ix
  setN      : {ix} → Note → String → NodeOp ix               -- 键由 Note 算出，证明由 prefix-++ 给
  transport : {ix} (m : Move) (t s d : Path) {isPrefix (realmOf ix) t} → NodeOp ix
  audit     : {ix} → Path → NodeOp ix
  checkAt   : {ix} → Header (envOf ix) → Path → NodeOp ix     -- 让检查器读 Store 里的模块；agent 自己不读
  enter     : {ix} (h : Header (envOf ix)) (q : ℕ) (p : Path) {q ≤ᵇ quotaOf ix} {isPrefix (realmOf ix) p} → NodeOp ix
  leave     : {ix} → {hasParent ix} → NodeOp ix
  log       : {ix} → String → NodeOp ix

embed : NodeOp ix → Op ix                -- 逐个构造子对过去；setN 翻成 set，带上算出来的键和证明
embedRun : Run NodeSig A ix → Run AgdaSig A ix     -- move o k ↦ move (embed o) (k ∘ 回应的对应)
```

没有的：`sh`、`eval`、`render`、`goals` / `give` / `split`、裸的 `set`，也没有 `parse` / `check`（agent 不持模块值，读模块的是检查器）。"禁止别的改法"就是这张表。

## 3 键与证明

```agda
specStub p = p ++ "spec" ∷ "stub" ∷ []            specTest p = p ++ "spec" ∷ "test" ∷ []
codeOf p f = p ++ "code" ∷ f ∷ []                 draftOf p step f = p ++ "draft" ∷ show step ∷ f ∷ []
kidOf p K  = p ++ "kids" ∷ K ∷ []                 noteKey p (memo n) = p ++ "memo" ∷ show n ∷ [] …

pf-code  p f = subst Bool→Type (sym (prefix-++ p _)) tt     -- 每个"在 p 下"的键一条，形状都一样
enterKid : … → enter h₀ (half q) (kidOf p K) {half-≤ q} {pf-kid p K}
```

答卷的步号 `step` 从哪来：`ask` 回文件名表时，后端把这一步的步号写在表头：回应是 `List String`，约定第一个元素是步号的十进制文本，其余是文件名。
程序据此拼 `draftOf p step f`。

## 4 答卷分类

```agda
hMax : (fl : Flags) (done : List ModName) → Header E    -- E₀ 名单 + 本沙箱里已 check 过的模块名；mkHeader 算出证明

data Kind : Type where
  solution : Kind                          -- 文件 = {X.agda, XTest.agda}（或 _.agda 当 X.agda，无测试）
  design   : List String → Kind            -- 文件 = X.agda、XTest.agda，加若干对 K.agda、KTest.agda；K 就是孩子名
  refute   : Kind                          -- 文件含 XRefute.agda
  malformed: String → Kind                 -- 别的：缺 X.agda、孩子缺一半、名字不合法

classify : (X : String) → List String → Kind
```

规则按这个顺序判：有 `XRefute.agda` → refute；没有 `X.agda` 也没有 `_.agda` → malformed；其余文件按名字配对成孩子，配不成对 → malformed；没有孩子 → solution；有 → design。

## 5 三个帧

```agda
-- fl = E₀⁻ 是沙箱，fl = E₀ 是粘合；都在同一前缀、零配额；进去逐个 checkAt，出来忘掉
sandbox : (fl : Flags) (keys : List Path) → Run NodeSig (λ _ → Verdict′) ix
sandbox fl keys = move (enter (h₀ fl) 0 p {tt} {≤ᵇ-refl…}) λ _ → checkAll fl [] keys λ v → move leave λ _ → done v

checkAll fl done []       k = k pass
checkAll fl done (x ∷ xs) k = move (checkAt (hMax fl done) x) λ where
  (fail path msg) → k (failed msg)
  (ok i)          → checkAll fl (Iface.name i ∷ done) xs k     -- 索引换成 E ▸ i：下一个模块能 import 这个

glue = sandbox E₀
```

agent 不 get 模块文本，不 parse：`checkAt` 把键交给检查器，检查器读。`hMax` 列出允许的最大 import 集（E₀ 加本沙箱里已过的模块），后端核对实际 ⊆ 它。
索引怎么写：`checkAll` 的每一步续体类型由 `next` 给，和 `DriveToy.chain` 一样逐步显式；`k` 的类型要对所有可能的终点环境成立，所以写成 `{j : Ix} → Verdict′ → Run NodeSig … j`。

```
 栈      进沙箱                              出沙箱
 (E₀⁻,q,p) ─enter─▶ (E₀⁻,0,p)·(E₀⁻,q,p) ─check…─▶ (E₀⁻▸m₁▸m₂…,0,p)·(E₀⁻,q,p) ─leave─▶ (E₀⁻,q,p)
 粘合同形，只是栈顶的 flag 是 E₀（多 --safe）
```

## 6 提示词（Query）

每条 `lit` 是固定文字，程序里写死；`row` / `last` 由后端填。读 `trace/<step>/prompt` 时会看到这几段，顺序固定：

```
 【任务】你在填一个 Agda 包 X。下面是它的 stub 和测试的 stub；签名与具体定义不能改，洞是 postulate 块里的名字
 【stub】                      row  p/spec/stub
 【测试】                      row  p/spec/test
 【规则】只能 import：<E₀ 名单>；不许 postulate / TERMINATING / … ；输出若干文件，每个以 "-- file: 名字.agda" 开头
 【分包】X.agda 可以 import 一个新名字 K，但必须同时交 K.agda（stub：签名 + postulate）和 KTest.agda（stub）
 【反驳】若规约矛盾，只交 XRefute.agda：import X 与 XTest，证 absurd : ⊥，不许 postulate
 【上次】                      last 2 p/verdict   last 3 p/memo            （第一轮为空）
 【改设计】（仅 redesign）      row  当前根正文   row  孩子的反驳   lit 说明哪个孩子怎么了
```

## 7 主循环

```agda
node : (d : ℕ) (p : Path) (sp : Spec) → Run NodeSig (λ _ → Result) (frame p q)
node zero    p sp = write result "exhausted" ; done exhausted
node (suc d) p sp = setN (memo 0) ("quota=" ++ show q) ; loop d p sp q      -- I8 用这一行

loop d p sp zero    = write result "exhausted" ; done exhausted
loop d p sp (suc n) = move (ask (promptFirst/Retry …)) λ names →
  case classify X names of
    solution     → solve   d p sp n step
    design ks    → design  d p sp n step ks
    refute       → refute  d p sp n step
    malformed s  → setN (verdict …) s ; setN (memo …) …; loop d p sp n
```

### 7.1 solve

```
 transport fill (codeOf p X.agda)     (specStub p) (draftOf p step X.agda)      → 必须 filled 0
 transport fill (codeOf p XTest.agda) (specTest p) (draftOf p step XTest.agda)  → 必须 filled 0
 sandbox E₀⁻ [code X, code XTest]  → 没过：verdict、memo、loop n
 glue    E₀  [code X, code XTest]  → 没过：verdict、memo、loop n
 过：setN result "solved 2 <键> <键>"；done (solved [...])
```

### 7.2 design

```
 对每个孩子 K：transport whole (specStub (kidOf p K)) _ (draftOf p step K.agda)
               transport whole (specTest (kidOf p K)) _ (draftOf p step KTest.agda)
 transport whole (codeOf p X.agda) _ (draftOf p step X.agda)
 transport fill  (codeOf p XTest.agda) (specTest p) (draftOf p step XTest.agda)   → filled k，k 写进 verdict（留到粘合的测试数）
 sandbox E₀⁻ (所有孩子的 stub、test-stub，再 code X、code XTest)   → 洞阶段：没过则 verdict、memo、loop n
 过：kids d p sp n ks []
```

### 7.3 kids

```
 kids … []       acc = glue E₀ (acc ++ [code X, code XTest]) → 过：result solved；没过：redesign (glueFailed msg)
 kids … (K ∷ ks) acc = enterKid K ; r ← node d (kidOf p K) (spec K) ; leave ;
                       case r of solved ms → kids … ks (acc ++ ms)
                                 refuted k → redesign (kidRefuted K k)
                                 exhausted → redesign (kidExhausted K)
```

孩子顺序跑；每个孩子拿 `half` 当前剩余配额。

### 7.4 redesign

```
 setN memo （why 的文字）
 ask (promptRedesign …) → names
 对答卷里每个孩子 K：
   get 旧 spec 两段、get 新 draft 两段：逐字相等 → keep（K 的 result 照用）
                                           不等   → transport whole 两段；K 进重做表
 答卷里没有了的旧孩子：setN (dropped K) 轮号
 transport whole 根正文；transport fill 根测试
 sandbox E₀⁻ (全部孩子 stub + 根)  → 没过：verdict、memo、loop n
 过：kids … 重做表 (keep 的 result 清单)
```

### 7.5 refute

```
 transport whole (codeOf p XRefute.agda) _ (draftOf p step XRefute.agda)
 audit (codeOf p XRefute.agda)  → false：verdict "反驳里有 unsafe"、loop n
 sandbox E₀⁻ [specStub p, specTest p, code XRefute]  → 没过：verdict、loop n
 过：setN result "refuted <键>"；done (refuted …)
```

## 8 程序保证的不变量

| 编号 | 不变量 | 由谁保证 |
| --- | --- | --- |
| N1 | 每次 checkAt 都在沙箱或粘合帧里 | `checkAt` 只在 `checkAll` 里出现，`checkAll` 只被 `sandbox` 调 |
| N8 | agent 不读任何模块文本 | NodeSig 里没有 `parse`；`get` 只用在 redesign 比对孩子的 spec 两段文本上 |
| N2 | `code/*` 只经 transport 写 | `setN` 的 Note 没有 code 这一种 |
| N3 | 孩子的 spec 先于 enter | `design` / `redesign` 里 transport 在 `kids` 之前 |
| N4 | result 先于 leave | 每个 `done` 之前一条 `setN result` |
| N5 | 配额：ask 次数 ≤ 开局配额 | `loop` 按 `suc n` 匹配；`enter` 给 `half q` |
| N6 | solved 清单是依赖序 | 孩子的清单在前，自己的在后；孩子内部同理 |
| N7 | 孩子只看 E₀ 和自己的前缀 | `enterKid` 的头是 `h₀`（E₀ 名单），realm 是 `kidOf p K` |

## 9 验收：`src/ToyNode.agda` 的六局，全部 refl

脚本余模型（`ToyEnv.backend` 升级版，见 `06-toys-tests.md` §1）按剧本答 ask / check / transport / audit。每局断言：结局、trace 长度、enter 次数、写了哪些键。

| 局 | 剧本 | 断言 |
| --- | --- | --- |
| S1 单节点一轮过 | ask → [X.agda, XTest.agda]；fill ×2 → filled 0；沙箱 check ×2 ok；粘合 ×2 ok | `result ≡ solved [code X, code XTest]`；enter 2 次；`p/result` 行存在 |
| S2 一轮没过再过 | 第一次沙箱第二个 check 回 fail；第二轮全 ok | 结局 solved；`p/verdict/1` 行有 fail 的原文；ask 2 次 |
| S3 分解一个孩子 | ask → [X, XTest, K, KTest]；whole ×3；fill → filled 1；洞阶段 4 个 ok；孩子：ask → [K, KTest]、fill ×2、沙箱、粘合；回来粘合 4 个 ok | 结局 `solved [kid K, kid KTest, X, XTest]`；enter 共 6 次（沙箱、孩子、孩子内 2、孩子粘合、粘合） |
| S4 孩子反驳、父改设计 | 孩子 ask → [KRefute]；audit true；沙箱 ok → refuted；父 memo；父 ask → 新设计（K 的 spec 变了）；孩子再跑，这次 solved；粘合 | 结局 solved；父 `memo/` 恰 2 行（quota 行 + 反驳行）；孩子前缀下 `dropped` 不存在 |
| S5 两个孩子一个 keep | A solved；B refuted；父改设计，A 的两段 spec 逐字相同、B 的变了 | A 只被 enter 1 次（trace 里 A 前缀只有一组）；B 2 次；结局 solved，清单含 A 的旧清单 |
| S6 配额耗尽 | 配额 1；沙箱 fail | 结局 `exhausted`；`p/result` 行为 `exhausted`；ask 1 次 |

每局都是 `_ : … ≡ … ; _ = refl`。六局过了，`node` 的控制流就对了；剩下的是后端（`05`）和真 LLM（`07` 的 M2 起）。
