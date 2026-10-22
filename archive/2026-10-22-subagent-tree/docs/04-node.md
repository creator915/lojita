# 04 Node.agda：文件 agent 的程序

一句话：`node d q p X` 是挂在前缀 p 上的文件 agent（树深 d、配额 q、模块名 X）。它只用 `NodeSig` 里的步，每一轮 ask 一次、分类答卷、搬运、沙箱里 check，
解答就粘合，分解就逐个开孩子，反驳就交反驳；结局写进 `p/result` 再返回。全部分支都是有限树上的程序，`soundHonest` 对它成立。
`Node` 是参数化模块：参数是 E₀ 的包名单、E₀ 的 flag（含 `--safe`，粘合用）、E₀⁻ 的 flag，加三条算出来的证明（字面量名单下都是 `tt`）。

## 0 文件结构

```
 §0 环境        E⁻ = base (_∈ₘ E₀mods) E₀⁻flags；hSand（沙箱 / 孩子的头）hGlue（粘合的头，多 --safe）
 §1 类型        Result  Note  Why  Kind  Verdict′
 §2 签名        NodeOp（NodeSig 的步）  embed : NodeOp ix → Op ix  embedRun
 §3 键          p ++ …：specStub specTest codeOf draftOf kidOf kidStub kidTest noteKey；ok-++ / ok-refl / ok-half 把引理包好
 §4 答卷        classify（文件名表 → 解答 / 分解 / 反驳 / 不合格）
 §5 帧          checkAll  sandbox（hSand = 沙箱，hGlue = 粘合）
 §6 提示词      prompt  promptRedesign（都是 Query）
 §7 主循环      Loop.nodeK loop askStep dispatch bounce solve writeKids whole2 writeRoot kids afterKid redesign … compareKids refuteStep；node
```

## 1 类型

```agda
-- 节点的身份就是模块名 X : String；stub 与 test 两段文本在 p/spec/ 行里

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

data Verdict′ : Type where               -- 一组 check 的结论
  pass   : Verdict′
  failed : String → Verdict′
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
NodeSig = record { Op = NodeOp ; Res = λ o → Res (embed o) ; next = λ o r → next (embed o) r }
embedRun : Run NodeSig A ix → Run AgdaSig A ix     -- move o k ↦ move (embed o) (embedRun ∘ k)：回应与下一拍按定义相同
```

没有的：`sh`、`eval`、`render`、`goals` / `give` / `split`、裸的 `set`，也没有 `parse` / `check`（agent 不持模块值，读模块的是检查器）。"禁止别的改法"就是这张表。

## 3 键与证明

```agda
specStub p = p ++ "spec" ∷ "stub" ∷ []            specTest p = p ++ "spec" ∷ "test" ∷ []
codeOf p f = p ++ "code" ∷ f ∷ []                 draftOf p step f = p ++ "draft" ∷ step ∷ f ∷ []      -- step 是 ask 回的步号文本
kidOf p K  = p ++ "kids" ∷ K ∷ []                 noteKey p (memo n) = p ++ "memo" ∷ show n ∷ [] …
kidStub p K = p ++ "kids" ∷ K ∷ "spec" ∷ "stub" ∷ []   kidTest p K = p ++ "kids" ∷ K ∷ "spec" ∷ "test" ∷ []   -- 写成 p ++ …，prefix-++ 直接用

ok-++ p s   = subst Bool→Type (sym (prefix-++ p s)) tt     -- 每个"在 p 下"的键一条，形状都一样：transport、setN（noteOk）
ok-refl p   = subst Bool→Type (sym (prefix-refl p)) tt     -- 同前缀开沙箱 / 粘合
ok-half q   = subst Bool→Type (sym (half-≤ q)) tt          -- 孩子的配额
开孩子：enter hSand (half q) (kidOf p K) {ok-half q} {ok-++ p _}
```

答卷的步号 `step` 从哪来：`ask` 回文件名表时，后端把这一步的步号写在表头：回应是 `List String`，约定第一个元素是步号的十进制文本，其余是文件名。
程序据此拼 `draftOf p step f`。

## 4 答卷分类

```agda
data Kind : Type where
  solution  : String → Kind                -- 文件 = {X.agda, XTest.agda}；带主文件名（没有 "-- file:" 标记时是 _.agda，当 X.agda 用）
  design    : String → List String → Kind  -- 主文件名、孩子名表：每个 K 配 K.agda、KTest.agda
  refute    : Kind                         -- 文件含 XRefute.agda
  malformed : String → Kind                -- 别的：缺 X.agda、孩子缺一半、名字不合法

classify : (X : String) → List String → Kind     -- 参数是文件名表（不含步号）；stepOf / filesOf 把 ask 的回应拆开
```

规则按这个顺序判：有 `XRefute.agda` → refute；没有 `X.agda` 也没有 `_.agda` → malformed；其余文件（去掉 X.agda、_.agda、XTest.agda）按名字配对成孩子：
`KTest.agda` 要有 `K.agda`、`K.agda` 要有 `KTest.agda`、K 只含字母数字，配不成对 → malformed；没有孩子 → solution；有 → design。

## 5 三个帧

```agda
-- h = hSand 是沙箱（E₀⁻），h = hGlue 是粘合（E₀）；都在同一前缀、零配额；进去逐个 checkAt，出来忘掉；结论交给续体 k
sandbox : (h : Header E⁻) (keys : List Path) → (Verdict′ → Run NodeSig R ((E⁻ , q , p) , rest)) → Run NodeSig R ((E⁻ , q , p) , rest)
sandbox h keys k = move (enter h 0 p {tt} {ok-refl p}) λ _ → checkAll (child E⁻ h) (flags h) [] keys λ _ v → move leave λ _ → k v

-- 栈顶环境 E′ 是显式参数：每过一个模块换成 E′ ▸ i；续体对任何终点环境 E″ 成立（只有它在变）
checkAll : (E′ : Env) (fl : Flags) (seen : List ModName) (keys : List Path)
         → ((E″ : Env) → Verdict′ → Run NodeSig R ((E″ , 0 , p) , rest)) → Run NodeSig R ((E′ , 0 , p) , rest)
checkAll E′ fl seen []       k = k E′ pass
checkAll E′ fl seen (x ∷ xs) k with mkHeader E′ (E₀mods ++ seen) fl          -- hMax：证明算出来
... | nothing = k E′ (failed "header: …")
... | just h  = move (checkAt h x) λ where
    (fail _ msg) → k E′ (failed msg)
    (ok i)       → checkAll (E′ ▸ i) fl (Iface.name i ∷ seen) xs k           -- 索引换成 E′ ▸ i：下一个模块能 import 这个
```

agent 不 get 模块文本，不 parse：`checkAt` 把键交给检查器，检查器读。`hMax`（= `mkHeader E′ (E₀mods ++ seen) fl`）列出允许的最大 import 集（E₀ 加本沙箱里已过的模块），后端核对实际 ⊆ 它。
索引怎么写：进沙箱后只有栈顶的环境在变，所以把它做成 `checkAll` 的显式参数，续体对任何 `E″` 成立；`leave` 的前置条件 `hasParent` 和 `next leave` 都按定义算回 `(E⁻ , q , p) , rest`（`q - 0 = q` 按定义成立）。

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
 【改设计】（仅 promptRedesign） row  当前根正文   row  孩子的反驳   lit 说明哪个孩子怎么了（showWhy）
```

`prompt p X` 是第一轮和重试共用的一条（【上次】由后端填，第一轮为空）；`promptRedesign p X why = prompt p X ++ 【改设计】`。

## 7 主循环

索引的写法（这是 M0 最容易卡的地方，实际这样过的）：

- 节点帧永远是 `((E⁻ , q , p) , rest)`。配额 q 只是索引，**不**拿它做递归：孩子回来后父的配额是 `q - half q`，结构上不比 q 小。
- 递归量是 **fuel**（开局 = q，每次 ask 减一，结构递减）、树深 d、孩子表；每次 ask 前用 `fromDec (1 ≤ᵇ q)` 在运行时查配额，`nothing` 就 exhausted。
- 孩子回来走**续体**（CPS）：`Cont R p rest = (q′ : ℕ) → Result → Run NodeSig R ((E⁻ , q′ , p) , rest)`。孩子的终点配额不定，续体对任何 q′ 都写得出 `leave`，
  `next leave` 按定义算回父的帧 `(E⁻ , q - half q , p) , rest`。`node d q p X = nodeK d q p X (λ _ r → done r)`。

```agda
nodeK zero    q p X k = finish q p exhausted k                         -- finish：写 p/result，交给续体
nodeK (suc d) q p X k = setN (memo 0) ("quota=" ++ show q) ; loop d q q 0 p X k     -- I8 用这一行；fuel 从 q 起，轮号从 0 起

loop d q zero    n p X k = finish q p exhausted k
loop d q (suc f) n p X k with fromDec (1 ≤ᵇ q)                        -- askStep
  nothing   → finish q p exhausted k
  just pf   → move (ask (prompt p X) {pf}) λ names →                   -- 配额 predℕ q，轮号 suc n
    case classify X (filesOf names) of                                -- step = stepOf names
      solution main     → solve …
      design main ks    → writeKids …（每个孩子 whole 两段）→ writeRoot …（根 whole、测试 fill、洞阶段沙箱）→ kids …
      refute            → refuteStep …
      malformed s       → bounce …                                     -- bounce：verdict/n、memo/n，再 loop d q f n
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
 kids … []       got = sandbox hGlue (kidMods got ++ [code X, code XTest]) → 过：finish (solved …)；没过：redesign (glueFailed msg) got
 kids … (K ∷ ks) got = enter hSand (half q) (kidOf p K) ; nodeK d (half q) (kidOf p K) K λ q′ r → leave ;
                       case r of solved ms → kids … ks (got ++ [(K , ms)])          -- got : Kids = List (孩子名 × 它的 solved 清单)
                                 refuted k → redesign (kidRefuted K k) got
                                 exhausted → redesign (kidExhausted K) got
```

孩子顺序跑；每个孩子拿 `half` 当前剩余配额，父剩 `q - half q`。`got` 记每个回来的孩子的清单：改设计时 keep 的孩子直接沿用。

### 7.4 redesign

```
 setN (memo n) (showWhy why)                      -- fuel 为 0 就到此 exhausted
 ask (promptRedesign …) → names                   -- 同样先 fromDec 查配额
 答卷是 design main ks：对每个孩子 K（compareKids）
   K 在 got 里：get 旧 spec 两段、get 新 draft 两段：逐字相等 → keep（K 的清单照用）
                                                     不等   → transport whole 两段；K 进重做表
   K 是新的：transport whole 两段；进重做表
 got 里答卷没有了的旧孩子：setN (dropped K) 轮号（dropGone）
 writeRoot：transport whole 根正文；transport fill 根测试；沙箱 (全部孩子 stub + 根)  → 没过：bounce
 过：kids … 重做表 (keep 的孩子清单)
 答卷是 solution：旧孩子全部 dropped，走 solve；是 refute：走 refuteStep；malformed：bounce
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
| S1 单节点一轮过（d 2，q 4） | ask → [X.agda, XTest.agda]；fill ×2 → filled 0；沙箱 check ×2 ok；粘合 ×2 ok | `result ≡ solved [code X, code XTest]`；enter 2 次；`t/result` = `solved 2 t/code/X.agda t/code/XTest.agda`；`t/memo/0` = `quota=4` |
| S2 一轮没过再过（d 2，q 4） | 第一次沙箱第二个 check 回 `fail [] "boom"`；第二轮全 ok | 结局 solved；`t/verdict/1` = `boom`（fail 的原文）；ask 2 次 |
| S3 分解一个孩子（d 2，q 4） | ask → [X, XTest, K, KTest]；whole ×3；fill → filled 1；洞阶段 4 个 ok；孩子：ask → [K, KTest]、fill ×2、沙箱、粘合；回来粘合 4 个 ok | 结局 `solved [kid K, kid KTest, X, XTest]`；enter 共 5 次（沙箱、孩子、孩子的沙箱、孩子的粘合、粘合）；`t/verdict/1` = `deferred=1`；孩子的 `result` 行、`spec/test` 行存在 |
| S4 孩子反驳、父改设计（d 2，q 8） | 孩子 ask → [KRefute]；audit true；沙箱 ok → refuted；父 memo；父 ask → 新设计（K 的测试变了）；孩子再跑，这次 solved；粘合 | 结局 solved；父 `memo/` 恰 2 行（`memo/0` = quota 行、`memo/1` = `kid K refuted its spec: …`、`memo/2` 不存在）；`t/kids/K/dropped` 不存在；`t/kids/K/spec/test` 是第二版；ask 共 4 次 |
| S5 两个孩子一个 keep（d 2，q 16） | A solved；B refuted；父改设计，A 的两段 spec 逐字相同、B 的变了 | A 只被 enter 1 次（数目标前缀 = `t/kids/A` 且不等于当前 realm 的 enter，排除 A 自己的沙箱 / 粘合）；B 2 次；结局 solved，清单含 A 的旧清单；`dropped` 都不存在 |
| S6 配额耗尽（d 1，q 1） | 配额 1；沙箱 fail | 结局 `exhausted`；`t/result` 行为 `exhausted`；ask 1 次 |

每局都是 `_ : … ≡ … ; _ = refl`。六局过了，`node` 的控制流就对了；剩下的是后端（`05`）和真 LLM（`07` 的 M2 起）。
配额要够：孩子拿父当前配额的一半，S4 / S5 里孩子要跑两次，q 太小第二次就拿到 0（exhausted）；所以 S4 用 8、S5 用 16。

结果（2026-10-22）：六局全 refl，`./check.sh` 里 ToyNode 一项 1 s 内过。
