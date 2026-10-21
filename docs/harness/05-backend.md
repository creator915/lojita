# 05 后端 v8：Drive.hs 的六处改动

一句话：后端是手。v8 在 v7 上只动 `Drive.hs`：路径 join、`ask` 渲染提示词并把答卷拆进 Store、`transport`、`audit`、日志行加 `by`、接口缓存只在 `--safe` 帧写。
`check`、`enter` / `leave` 的快照栈、`store:DIR`、`Code.hs`、生成器都不动。源码留 `/root/agda-backend/v8/`，二进制 `/usr/local/bin/agda-cubical-run.v8`。

## 0 v7 里会碰到的地方（对照）

```
 respond          按步的构造子名分派：("ask",[p,_])、("get",[k])、("set",[k,v,_])、("enter",[_,q,p,_,_]) …
 askHandler       ask:fixed / ask:script / ask:mailbox / ask:http
 storeGet/Set     内存 Map + log.jsonl 追加 + blob/
 answerCheck      Code 值 → 核对 import ⊆ 头 → virtualModule → withCleanOptions … True（写接口）→ getNonMainModuleInfo
 withCleanOptions 第三个参数 keepIfaces 决定写不写 .agdai
```

## 1 路径 join

realm 与键从 Agda 过来是 `VList [VStr …]`。两条规则，之后一切照旧：

```
 realm  每段后加 "/"：[]  → ""      ["a"] → "a/"      ["twice","kids","mul"] → "twice/kids/mul/"
 键     段间 "/"：       ["a","x"] → "a/x"             ["twice","spec","stub"] → "twice/spec/stub"
```

`enter` 的第三个参数、`get` / `set` / `transport` / `audit` 的键都先 join。日志里的 `k`、`r` 字段因此和 v7 一模一样。

## 2 ask：渲染、问、落盘、拆文件

输入是 `Query` 值（`VList` 的 `Item`）。步骤：

```
 1 渲染   lit s        → s
          row k        → join k 的值；没有这行 → "（空）"
          last n k     → 前缀 join k 下行号最大的 n 行，按行号升序，每行 "### <键>\n<值>\n"
          项之间空一行；都在当前 realm 内读（realm 外当作空）
 2 落盘   set <realm>trace/<step>/prompt = 提示词                      by=ask
 3 问     askHandler（fixed / script / http 不变；script 的分隔见 §7）
 4 落盘   set <realm>trace/<step>/reply = 答卷原文（> 2 KB 进 blob）     by=ask
 5 拆     行首匹配 ^-- file: ([A-Za-z0-9_]+\.agda)\s*$ 开新文件，该行不计入内容；
          以 ``` 开头的行丢掉（markdown 围栏）；
          没有任何标记 → 整份（去围栏）是一个文件 _.agda；
          文件名不合法（含路径分隔、不以 .agda 结尾）→ 整份拒收：不写 draft，回只有步号的表
 6 落盘   每个文件 set <realm>draft/<step>/<名字> = 内容                  by=ask
 7 回     VList [VStr <step>, VStr 名字₁, VStr 名字₂, …]                 第一个元素是步号
```

`<step>` 是驱动器的步号（`respond` 的 n）。没配 ask handler 照旧 softError。

## 3 transport：写 code 行的唯一入口

参数 `[m, t, s, d, _]`：`m` 是 `fill` / `whole`，三个键先 join。都要求 `t` 在 realm 内（类型已保证，后端兜底同 `set`）。

### whole

```
 读 d → parseModuleText → 失败：rejected "parse: …"
 模块名核对：t 的最后一段去掉 .agda 应等于模块名 → 不等：rejected "module name"
 set t = d 的原文                                                      by=transport
 回 filled 0
```

### fill

```
 读 s（stub）、d（答卷），各自 parseModuleText → 失败：rejected
 模块名都要等于 t 的名字 → 不等：rejected "module name"
 取两边 module … where 里的顶层声明表 S、D（跳过 Comment）
 结果 R 按 S 的顺序生成：
   S 里的 Import / Open / OptionsPragma / Infix        → 照抄
   S 里的 Data / DataSig / DataDef / Record* / Mutual  → 照抄；D 里同名的 data / record → rejected "redefined: T"
   S 里的 TypeSig f T 加它的 FunClause（具体定义）        → 照抄；D 里同名 → rejected "redefined: f"
   S 里的 Postulate [TypeSig f₁ T₁, …]                 → 对每个 fᵢ：
        D 里有 lhs 头为 fᵢ 的 FunClause（≥ 1 条） → 输出 TypeSig fᵢ Tᵢ（类型取 S 的）+ D 的这些 FunClause；D 里 fᵢ 的 TypeSig 忽略
        D 里没有                                → 输出 Postulate [TypeSig fᵢ Tᵢ]（仍是洞），计数 +1
 D 里剩下的声明（S 没提到的名字：辅助函数、私有定义）→ 追加在 R 末尾；D 的 Import / Open → 插在 S 的 import 之后（check 会核对它们 ⊆ E₀）
 set t = prettyModule R                                                 by=transport
 回 filled <计数>
```

`fill` 保证：签名、具体定义、import 的集合由 stub 决定，答卷只能提供洞的子句和多出的辅助。

## 3b checkAt：检查器自己读 Store

参数 `[h, k]`：`h` 是 Agda 侧的 `Header` 值（import 名单、flag），`k` 先 join。

```
 读 join k 的文本 → 没有这行：fail [] "missing <键>"
 parseModuleText → 失败：fail [] 报错（带真实行列号）
 实际 import ⊆ h 的 import → 否则 fail [] "imports not in the header: …"（同 answerCheck）
 virtualModule（从 Haskell 树直接造，不经 toV / fromV）；withCleanOptions st flags keepIfaces（§6）；getNonMainModuleInfo
 ok → buildIface，回 ok iface；失败 putTC 回滚，回 fail（范围是真实文本的行列号）
```

和 `check` 的差别只有来源：`check` 的模块是 Agda 项里的树，`checkAt` 的模块是 Store 里的文本。两者共用 `answerCheck` 的后半段。

## 4 audit：反驳的黑名单

参数 `[k]`。读 join k 的文本，走 `parseFile tokensParser`（lexer），扫 token：

```
 关键字  postulate  primitive  macro  tactic  unquote  unquoteDecl  unquoteDef  unquoteData     → false
 pragma  {-# 开头、名字不是 OPTIONS                                                                 → false
 其余    → true
```

读不到键、词法错 → false。注释和字符串字面量是别的 token 种类，不会误判。
前提：E₀ 里只有 `--safe` 的模块（cubical 库全是），`Agda.Builtin.TrustMe` 这类不进 E₀。

## 5 日志行加 `by`

`storeSet` 多一个参数 `by :: String`，写进每行：`"by":"set"`（程序的 set）、`"by":"ask"`、`"by":"transport"`。
`fold.py`、dump 只看 `op` / `k` / `v` / `h`，不受影响；`schema.py` 靠它查 I2、I3、I5。

## 6 接口缓存只在 `--safe` 帧写

`answerCheck` 里 `withCleanOptions st flags keepIfaces`：`keepIfaces = "--safe" ∈ flags`。
沙箱帧（E₀⁻）的 check 不写 `.agdai`，粘合帧（E₀）写。原因：同名模块在两种 flag 下各留一份接口会互相触发重查（v6 已踩过"选项变了无限重查"）。

## 7 `ask:script` 的答卷格式

v7 是一行一答。答卷是多行的模块，所以 v8 的脚本文件用一行只有 `%%` 的分隔线隔开各答卷；原来一行一答的文件照样能读（没有 `%%` 就按行）。
`tests/node/scripts/*.txt` 都是这个格式（见 `06-toys-tests.md` §5）。

## 8 不动的

`check`、`eval`、`render`、`goals` / `give` / `split`、`enter` / `leave` 的快照栈、`sh`、`log`、`store:DIR` 的打开 / 恢复 / blob、`--cubical-store-dump`、`Code.hs`、`agda-code-gen`、`Runtime.hs`。

## 9 构建与安装

```
 源码   /root/agda-backend/v8/Drive.hs（从 v7/Drive.v7.hs 复制后改）；agda-source 里对应的文件同步
 构建   cd /root/agda-backend/agda-source && cabal build agda-cubical-run    （日志写到 /root/agda-backend/build-v8.log）
 安装   cp $(cabal list-bin agda-cubical-run) /usr/local/bin/agda-cubical-run.v8 && ln -sf /usr/local/bin/agda-cubical-run.v8 /usr/local/bin/agda
 回退   ln -sf /usr/local/bin/agda-cubical-run.v7 /usr/local/bin/agda
```

## 10 验收

| 编号 | 标准 | 命令 | 期望 |
| --- | --- | --- | --- |
| B1 | v7 全部回归 | `./store.sh`、`./drive.sh`、后端 `test/CubicalRuntime/run-tests.sh` | 25 过；十二个程序照旧；回归通过 |
| B2 | join 正确 | `./store.sh` 的 B2（`kidSees`、`kidWrites`，键已是路径） | 同 v7 的答案；dump 里的键仍是 `a/x` |
| B3 | ask 渲染与拆文件 | `./drive.sh` 的 `askSplit`（`ask:script` 给一份两个文件的答卷） | 打印 `"<步号>" ∷ "M1.agda" ∷ "M1Test.agda" ∷ []`；dump 里有 `…/trace/<step>/prompt`、`reply`、`draft/<step>/M1.agda`、`M1Test.agda` |
| B4 | ask 无标记答卷 | `drive.sh` 的 `askPlain` | 回 `_.agda` 一个文件 |
| B5 | fill 正常 | `drive.sh` 的 `fillOne`：stub `postulate twice : ℕ → ℕ`，答卷给 `twice n = n + n`，fill 后 check、eval `twice 3` | `value (Lit (LitNat (pos 6)))`；`code/M1.agda` 的文本里 `twice : ℕ → ℕ` 后跟 `twice n = n + n` |
| B6 | fill 留洞计数 | `drive.sh` 的 `fillPartial`：stub 两个 postulate，答卷只给一个 | `filled 1`；文本里仍有一个 `postulate` |
| B7 | fill 拒绝 | `drive.sh` 的 `fillReject`：答卷重定义 stub 里的 data | `rejected "redefined: T"` |
| B8 | whole 拒绝 | `drive.sh` 的 `wholeBadName`：答卷模块名与目标不符 | `rejected "module name"` |
| B9 | audit | `drive.sh` 的 `auditBad`（含 `postulate absurd : ⊥`）、`auditOk` | `false`、`true` |
| B10 | 两种 flag 的帧 | `drive.sh` 的 `twoFlags`：同一含 postulate 的 stub，E₀⁻ 帧 check、再开 `--safe` 帧 check | `(true , false)`；第二次的报错含 `postulate` 或 `Safe` |
| B11 | `by` 字段 | `python3 tests/store/schema.py runs/drive-fillOne` | `OK`；手看 log.jsonl：code 行 `by:"transport"`，trace 行 `by:"ask"` |
| B12 | 接口缓存策略 | 跑 `twoFlags` 后看 `_build/…/_lojita_virtual/` | 只有 `--safe` 帧 check 过的模块有 `.agdai` |
| B13 | script 分隔 | `drive.sh` 的 `askSplit` 用的脚本文件含 `%%` | 同 B3 |
| B14 | checkAt | `drive.sh` 的 `checkAtOne`：set 一段模块文本到键 → checkAt → eval `twice 3` | `value (Lit (LitNat (pos 6)))`；再 set 一段带类型错的文本 → `fail … 行号:列号 …`（真实位置） |
| B15 | checkAt 的 import 核对 | `drive.sh` 的 `checkAtPeek`：文本 import 了头里没有的模块 | `fail [] "imports not in the header: …"` |

搞乱了的典型症状：`drive.sh` 的旧程序打印 `unknown step`（分派表少了一行）；`store.sh` B 组 dump 不等（join 多了或少了 `/`）；
`check` 后 Agda 无限 "Checking M1"（接口缓存策略写反了）。
