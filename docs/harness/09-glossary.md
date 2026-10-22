# 09 符号与术语

```
 E₀        任务的语境：能 import 的包名单 + flag（含 --safe）。任务中不变；唯一能被多个文件 import 的东西
 E₀⁻       E₀ 去掉 --safe。节点帧、沙箱帧、孩子帧的 flag
 Σ         签名：窗口。AgdaSig 是后端实现的全部步；NodeSig 是文件 agent 能用的子集
 p         节点前缀，路径 List String，如 ["pow","kids","mul"]；也是它的 realm。写成 pow/kids/mul
 <R>       根名；一局一个 store 目录 runs/<R>-<时间>
 stub      带洞的模块：import、具体的 data / record / 谓词可以有；洞是 postulate 块里的名字
 spec      接口 = 两个 stub 的文本：p/spec/stub（X.agda）、p/spec/test（XTest.agda）。父写
 正文      洞填好的文本：p/code/X.agda、p/code/XTest.agda
 fill      搬运：stub 的签名与定义 + 答卷的子句；只换 postulate 块里的名字
 whole     搬运：整个换成答卷
 keep / whole / drop   改设计时对每个孩子的三种处置：spec 不变、重写 spec、丢弃
 沙箱      enter 同前缀、零配额、E₀⁻ 的帧；check 完 leave，后端忘掉
 粘合      enter 同前缀、零配额、E₀ 的帧；按依赖序 check 子树全部模块；--safe 在这里生效
 洞阶段    分解之后、开孩子之前的沙箱 check：A.stub × B.stub × root ⊢ root.Test
 反驳      XRefute.agda：import 两个 stub，证 absurd : ⊥；audit 过；在 E₀⁻ 里 check 过 → 规约矛盾
 audit     后端在 token 流上查黑名单：postulate / primitive / macro / tactic / unquote* / 非 OPTIONS 的 pragma
 verdict   一次 check 的判决行 p/verdict/<n>
 memo      笔记行 p/memo/<n>；memo/0 是 quota=<q>
 trace     每次 ask 的提示词与答卷 p/trace/<step>/{prompt,reply}，后端写
 draft     答卷拆出的文件 p/draft/<step>/<名字>，后端写
 result    结局行 p/result：solved <k> <键>… / refuted <键> / exhausted
 Result    node 的返回值：solved 清单 / refuted 键 / exhausted
 Query     提示词的查询：lit / row / last；后端渲染
 Note      NodeSig 的 set 能写的键：memo / verdict / result / dropped
 holds     持有：父 → p/kids/K；唯一持有者；级联丢弃
 imports   引用：文件 → E₀ 模块（或自己的孩子，与 holds 重合）
 持有 / 引用  依赖对方的存在 / 依赖对方的内容；前者寿命包含、不可成环、级联；后者无关、可复制
 一条原则  被依赖的接口动了，依赖它的跟着动；接口没动，链到此终止
 iface / full  接口哈希（spec）/ 全哈希（正文）；前者决定 keep，后者决定重查
 文件 agent  node d p 的一次运行；memory = p 下的行；权限 = realm p
 根会话    人与 LLM 的对话；写根的 spec 与 E₀；一个会话 = 一个根
 Honest    手每答一步都是 Σ 允许的一步；soundHonest 把它变成整局合法
 脑 / 手   Run Σ 程序 / 余模型（后端）；窗口 = Σ
 checkAt   让检查器读 Store 里键 k 的模块：agent 对孩子的 code 只有 open 没有 read
 抽象文件  (状态 , open / close / read / write 四类操作)；Σ 是这些文件的目录；进程、硬件也是文件
 操作类型 / 具体操作   write 是一类；set、transport、ask 的落盘是三种具体的 write，工具与权限不同
 agent 文件  每个计算文件配一个：memory（变更的思维链叠加）+ 权限（文件 × 操作类型）；1.agent 能 open 2.agent
 内核 / 壳 / 协议文件  纯 Agda 树 / 碰 Σ 的 Run 程序 / 把多棵内核树拼成一棵的 Agda 文件
 挂载表    --cubical-handler 的表 = 哪些抽象文件存在；开工前配好
 step / n  后端全局步号 / 节点自己的轮号
 by        日志行的来源字段：set / ask / transport
 fuel / Cont  node 的递归量（开局 = 配额，每次 ask 减一；配额本身是索引，不做递归）/ 孩子回来的续体（CPS）：04 §7
 I1–I8     键表不变量（01 §9，schema.py 查）；N1–N7 程序不变量（04 §8）；A1–A7 agent 验收（02 §5）；B1–B15 后端验收（05 §10）；E1–E9 Env 验收（03 §7）；R1–R5 根会话验收（08 §6）
```
