# 06 玩具、测试、检查器、脚本

> **2026-10-22 复位**：§4（ToyNode 六局）作废，六局的断言留作新调度器玩具的目标；§8 里 NegNote 已随 Node 归档，NegPeek 与 NegLeave / NegQuota / NegRealm / NegWiden / NegTransport 查的是栈帧机制，随 Σ 换；§9 的 check.sh 已改（见文件），node.sh 待新计划。§1–§3、§5–§7 有效。

一句话：每样东西一行能说清它查什么、过了长什么样。改动的文件标"改"，新文件标"新"。期望输出写死在这里，和脚本里的注释一致。

## 1 `src/ToyEnv.agda`（改）：脚本余模型

它是"纯手"：不接 Agda 进程，按剧本答每一步，让 ToyNode 能全 refl。

```
 W ix = Script × ℕ × S.Board          剧本 × 步号 × 内存里的 Store
 Script = record
   checks     : List Verdict           check 按序答；用完一律 ok（同 v7）
   asks       : List (List (String × String))   每次 ask 一份答卷：(文件名 , 文本) 的表；用完回只有步号的表（同后端拒收时的回应）
   transports : List Filled             transport 按序答；用完一律 filled 0
   audits     : List Bool               audit 按序答；用完一律 true
```

`respS` 新增三个分支：

```
 ask q        取 asks 的头一份：对每个 (名 , 文) 写 board[realm/draft/<步号>/名] := 文；回 步号 ∷ 名字表；步号 +1
 transport    whole：board[t] := board[d]；fill：board[t] := board[d]（玩具不真拼，拼接是后端的事）；回 transports 的头一个
 audit        回 audits 的头一个
 checkAt h k  同 check：按 checks 剧本答；用完一律 ok，接口的名字取键的最后一段去掉 .agda
 get / set    不变，键是路径（join 成 "a/x" 存进 S.Board，和后端一致）
```

`M2 i`、`hKid i₁ i₂` 改用 `mkHeader` / `mkCode` 在运行时造（`_▸_` 只记接口后，"M1 看得见"取决于接口的名字，见 `03-env.md` §4.5）。

验收：`./check.sh` 过；原来的五条 refl（"yes"、M2 可见、M3 不可见、配额 2、五步）不变——"yes" 现在是答卷里第一个文件的名字；另加一条：答卷落在子实例的 `draft/0/` 下。

## 2 `src/StoreToy.agda`（改）：键改路径

十一个程序的键从 `"a/x"` 改成 `"a" ∷ "x" ∷ []`。§7 九条 refl 的值不变：`just "1"`、`nothing`、`just "2"`、`(just "1" , nothing)`、`just "9"`、三个 persist、`commuteXY ≡ commuteYX`、`big ≡ true`、`loop 10 0 ≡ 0`。
`./store.sh` 的 B 组在真后端上答案也不变（join 回 `a/x`）。

## 3 `src/DriveToy.agda`（改）：真后端上的新程序

原十二个不动（`kid` 的 realm 改成路径）。新加：

| 程序 | 做什么 | 期望打印 |
| --- | --- | --- |
| `askSplit` | `ask` 一个两项的 Query；handler 是 `ask:script`，脚本给一份两文件的答卷 | `"<步号>" ∷ "M1.agda" ∷ "M1Test.agda" ∷ []` |
| `askPlain` | 同上，脚本给的答卷没有 `-- file:` 标记 | `"<步号>" ∷ "_.agda" ∷ []` |
| `fillOne` | set stub 与答卷到两个键 → transport fill → checkAt → eval `twice 3` | `value (Lit (LitNat (pos 6)))` |
| `checkAtOne` | set 一段模块文本到键 → checkAt → eval；再 set 一段类型错的 → checkAt | `value (Lit (LitNat (pos 6)))`；`fail … 行号:列号 …` |
| `checkAtPeek` | 文本 import 了头里没有的模块 | `fail [] "imports not in the header: …"` |
| `fillPartial` | stub 两个 postulate，答卷只填一个 | `filled 1` |
| `fillReject` | 答卷重定义 stub 的 data | `rejected "redefined: T"` |
| `wholeBadName` | 答卷模块名和目标键不符 | `rejected "module name"` |
| `auditBad` | set 一段含 `postulate absurd : ⊥` 的反驳 → audit | `false` |
| `auditOk` | set 一段干净的反驳 → audit | `true` |
| `twoFlags` | 含 postulate 的 stub：E₀⁻ 帧 check → ok；enter 加 `--safe` 的帧再 check → fail | `(true , false)` |

`drive.sh` 的注释里逐个写上这些期望；跑完对照。

## 4 `src/ToyNode.agda`（新）：六局

见 `04-node.md` §9 的表。每局：造剧本 → `Play.play backend (embedRun (node d q ("t" ∷ []) "X")) (剧本 , 0 , emptyBoard)` → 断言结局、enter / ask 次数、关键行，全部 `refl`。
`Node` 的实例：`module N = Node (natM ∷ []) safeCubical ("--cubical" ∷ []) tt tt tt`。
数 enter 次数的函数：遍历 trace 数 `enter` 构造子；数"开某个孩子"的次数：目标前缀等于它且不等于当前 realm（排除孩子自己的沙箱 / 粘合）。查键的函数：`board "t/result" ≡ just "…"`（键是 join 过的字符串）。

## 5 `tests/node/scripts/*.txt`（新）：预置答卷

给 `ask:script` 用，答卷之间一行 `%%`。每份答卷里用 `-- file:` 分文件。

| 文件 | 剧本 | 用在 |
| --- | --- | --- |
| `twice-pass.txt` | 一份答卷：Twice.agda 填 `twice n = n + n`，TwiceTest.agda 填 `test = refl` | M2 dry |
| `twice-fail-once.txt` | 第一份类型错（`n + twice`），第二份对 | M2 dry、A5（重启记得）前半 |
| `twice-fail-only.txt` | 只有一份错的 | A5：第一局 exhausted |
| `pow-design.txt` | 根：Pow.agda import Mul，带 Mul.agda / MulTest.agda 的 stub，PowTest 用 MulTest 的陈述证；孩子：Mul 填好 | M3 dry |
| `contra-refute.txt` | 根的 spec 矛盾；答卷是 ContraRefute.agda | M3′ dry |
| `pow-redesign.txt` | 根第一次给 Mul 一个矛盾的 spec；孩子反驳；根第二次改 spec；孩子填好 | M3″ dry |
| `two-kids-keep.txt` | 根开 A、B；A 填好；B 反驳；根改设计时 A 的 spec 原文不变 | M4 dry |

## 6 `tests/store/schema.py`（新）：键表不变量检查器

```
 用法   python3 tests/store/schema.py runs/<局>            读 log.jsonl（和 fold.py 一样不依赖别的库）
 过     OK  rows=<n>  nodes=<m>                             退出码 0
 没过   每条违规一行：I2 violated at n=57: twice/code/Twice.agda written by set   退出码 1
```

查的八条 I1–I8 见 `01-objects.md` §9。它也顺带打印每个节点的 ask 次数与配额（I8 的证据）。

## 7 `tests/node/report.py`（新）：一局的报告

```
 用法   python3 tests/node/report.py runs/<局> [--prompt STEP] [--check-isolation]
 输出   twice                     rounds=2  memos=1  result=solved 2
          kids/mul                rounds=1  memos=1  result=solved 2
        --prompt 57   打印 trace/57/prompt 的原文
        --check-isolation   每个孩子 code/* 的首行不出现在父的任何 prompt 里 → "isolation OK" 或列出违规
```

读的是 `--cubical-store-dump` 的 JSON（脚本自己调 dump）。

## 8 `tests/neg/`（改 + 新）：十个必须编译失败的反例

| 文件 | 为什么必须失败 | 状态 |
| --- | --- | --- |
| NegVisible、NegFlags、NegUnsafe、NegLeave、NegQuota | 同 v7 | 不动 |
| NegRealm、NegWiden | 键与 realm 改成路径 | 改 |
| NegTransport | `transport` 的目标键在 realm 外 | 新 |
| NegNote | 在 `Run NodeSig` 里想用 `set` 写 `code/…`：NodeSig 没有裸的 `set`（`Env.Op` 的 set 对不上 `NodeOp`），`Note` 也没有 code 这一种 | 新 |
| NegPeek | 孩子帧的头想 import 父在节点帧里 check 过的模块：`mkHeader` 造不出 | 新 |

`./neg.sh`：十行 `rejected as expected`。

## 9 脚本

| 脚本 | 做什么 | 过了 |
| --- | --- | --- |
| `check.sh`（改） | 加 `src/Path.agda`、`src/Node.agda`、`src/ToyNode.agda`（M0 已加）、`src/Boot.agda`（M2） | 无 error |
| `neg.sh`（不改） | 自动扫 `tests/neg/*.agda` | 十行 rejected |
| `drive.sh`（改） | 加 §3 的十一个程序；`askSplit` / `askPlain` 用 `--cubical-handler=ask:script:tests/node/scripts/drive-split.txt` | 每个程序下一行等于注释 |
| `store.sh`（改） | B 组后加 B9：对 `drive-fillOne` 这一局跑 `schema.py` | `28 passed, 0 failed` |
| `node.sh`（新） | `./node.sh dry <脚本> [--same-dir DIR]`：`ask:script`；`./node.sh run <任务> N`：`ask:http`。任务名 ∈ twice / pow / contra（对应 Boot 里的三个 main）。每局一个目录 `runs/<任务>-<时间>`；跑完调 `report.py`，打印一行结局 | dry：`result: solved …`；run：`solved k/N` |

`node.sh` 的一局：

```
 agda -v0 --cubical-drive=<main> --cubical-handler=store:runs/<局> --cubical-handler=ask:<script 或 http> src/Boot.agda
 agda -v0 --cubical-store-dump=runs/<局> src/Boot.agda > runs/<局>/dump.json
 python3 tests/store/schema.py runs/<局>
 python3 tests/node/report.py runs/<局>
```
