# 08 根会话、Boot.agda、E₀、IO 根

> **2026-10-22 复位**：§1、§3、§4、§5 有效。§2 的 `Boot.agda`（`embedRun (node …)`、"node 自己在 enter 孩子时才把 realm 收窄"）作废：根会话是挂在根 `[]` 上的 agent，写 `<R>/spec/*` 与 `<R>/quota` 后等 `<R>/result`，见 `../reset-2026-10-22.md` §4.7。

一句话：根会话是人与 LLM 的那几轮对话，产物是根的两段 spec、E₀、配额、树深；v1 里这些是 `Boot.agda` 的常量。
根是唯一碰 IO 的节点，但它也只是一个 `Run` 程序；验证时对手是 mock 余模型，部署时换成真 handler。两个微服务 = 同一签名的两端。

## 1 根会话做的事

```
 2.0 确认需求    几轮对话 / 测试，和传统 agent 无异
 2.1 初始化      写 <R>/spec/stub、<R>/spec/test；定 E₀（包名单 + flag）；定配额、树深
 开局            启动根的文件 agent：node d [R]
 收尾            读 <R>/result：solved → 取产物；refuted → 需求矛盾，改 spec 再开；exhausted → 加配额或改 spec
```

v1 的"对话"由人直接写进 `Boot.agda` 的常量；以后根会话本身也是一个 `Run` 程序，它的 ask 就是和人说话。

## 2 `src/Boot.agda`（M2 新）

```agda
module Boot where
-- E₀：M2–M4 用的名单与 flag
E₀-mods  = natM ∷ preludeM ∷ []                      -- Cubical.Data.Nat、Cubical.Foundations.Prelude（≡ 在这里）
E₀-flags = "--cubical" ∷ "--safe" ∷ []               -- 粘合帧用
E₀⁻flags = "--cubical" ∷ []                          -- 节点帧、沙箱帧、孩子帧用
quota    = 6 ;  depth = 3

-- 三个任务的 spec 常量
twiceStub  = "module Twice where\nopen import Cubical.Data.Nat\npostulate\n  twice : ℕ → ℕ\n"
twiceTest  = "module TwiceTest where\nopen import Cubical.Foundations.Prelude\nopen import Cubical.Data.Nat\nopen import Twice\npostulate\n  test : twice 3 ≡ 6\n"
powStub    = "module Pow where\nopen import Cubical.Data.Nat\nopen import Mul\npostulate\n  pow : ℕ → ℕ → ℕ\n"        -- 已 import Mul：第一轮必是分解
powTest    = … pow 2 3 ≡ 8 …
contraStub = … f : ℕ → ℕ … ;  contraTest = … test1 : f 0 ≡ 1 … test2 : f 0 ≡ 2 …

-- 开局程序：写 spec → 写 session 行 → 跑 node → 打印结局
boot : (R : String) (stub test : String) → Run AgdaSig (λ _ → Result) (ix₀ R)
boot R stub test =
  move (set (R ∷ "spec" ∷ "stub" ∷ []) stub) λ _ →
  move (set (R ∷ "spec" ∷ "test" ∷ []) test) λ _ →
  move (set ("session" ∷ R ∷ "0" ∷ []) ("task " ++ R)) λ _ →
  embedRun (node depth (R ∷ []) (spec R))

twice  = boot "twice"  twiceStub  twiceTest
pow    = boot "pow"    powStub    powTest
contra = boot "contra" contraStub contraTest
```

`ix₀ R = (base (_∈ₘ E₀-mods) E₀⁻flags , quota , []) , []`：根会话的帧 realm 是空路径，所以它能写 `<R>/…` 和 `session/…`。
`node` 自己在 enter 孩子时才把 realm 收窄；根的文件 agent 跑在 realm `[R]` 的帧里——`boot` 先 `enter h₀ quota (R ∷ [])` 再调 `node`，`node` 回来后 `leave`。

打印：驱动器把 `done` 的值按类型打出来，`node.sh` 把它整理成一行 `result: …`。

## 3 E₀ 怎么定

```
 1 列出任务要用的库模块：函数、类型、_≡_ 在哪个模块里
 2 只放 --safe 的模块：cubical 库全部是；Agda.Builtin.TrustMe、Agda.Builtin.Reflection 不进
 3 flag：E₀ = 库的 infective flag（--cubical）+ --safe；E₀⁻ = 去掉 --safe。.agda-lib 的 --guardedness 后端自动加，不写
 4 把名单写进 Boot 的 E₀-mods，并写进提示词的【规则】段（Node.rules 从同一个常量生成，两处不会不一致）
 5 任务中不变。要加模块 = 新开一局
```

## 4 内核、壳、协议文件（M5 以后）

一个微服务 = Agda 内核 + IO 壳。内核是纯 Agda 树，壳是 `Run Σ` 程序，只有壳碰 Σ（时钟、LLM、网络、sh）。

```
 内核 K      纯 Agda 树；根导出纯接口，如 step : State → Input → State × Output
 壳  S       Run AgdaSig 程序：读世界 → 调 K 的函数 → 写世界
 验证        STest：mock : Comodel AgdaSig W（脚本余模型，ToyEnv 的样子）
             t : fst (snd (Play.play mock S w₀)) ≡ expected ; t = refl
 部署        agda --cubical-drive=S --cubical-handler=ask:http:… --cubical-handler=store:DIR
```

同一环境里两个内核要交互，**不在壳里写协议**。写一个 Agda 协议文件，把两棵树拼成一棵，再给它一个壳：

```
 协议 P.agda   纯：import K₁ 的根、K₂ 的根，定义消息往来的合成；PTest 是对合成的规约；P 是更大的树的根
 P 的壳        一个壳驱动 P
 规则          Agda 树内：语境包外一文件一父（K₁、K₂ 的根现在的父是 P）
               树外：多个壳可以调同一个内核。壳不是 Agda 文件，不受一父限制
 好处          协议在 Agda 世界里，和别的文件一样被 check、被搬运、有 spec
 拼不进来的    时钟、LLM、远端服务：模拟文件 = 脚本余模型，供形式验证；部署时换真手
```

脑手分离：权限与资源住在窗口下面。Σ 里只带配额与 realm 两个数（类型管），handler 表开工前配好（后端管），
唯一的假设是 Honest：手每答一步都是 Σ 允许的一步；`soundHonest` 把它变成"整局合法"。跨机器时，两个壳之间是一个 socket 文件，协议仍是 P.agda；对方那一端在验证里是 mock。

## 5 多个根

一台中心化设备一个根 = 一个 store 目录 `runs/<R>-<时间>`：同一环境里的多个内核用协议文件拼成一棵树，所以仍是一个根。
跨机器才是多个根，各自目录或各自机器，只共享 E₀ 里的协议签名。根会话不会多：绝大多数工作在文件 agent 上。

## 6 验收

| 编号 | 标准 | 命令 | 期望 |
| --- | --- | --- | --- |
| R1 | Boot 先写 spec 再开 node | `schema.py`（I4、I5） | OK |
| R2 | session 行存在 | dump | `session/twice/0` = `task twice` |
| R3 | 三个 main 都能跑 | `./node.sh dry …`（M2、M3、M3′） | 各自的结局 |
| R4 | E₀ 名单与提示词一致 | `report.py --prompt <第一条>` | 【规则】段列出的模块 = `E₀-mods` |
| R5 | 根的结局打印 | `node.sh` 最后一行 | `result: solved …` / `refuted …` / `exhausted` |
