{-# OPTIONS --safe --cubical #-}
------------------------------------------------------------------------
-- Bench.agda —— 在 ProgramBench 的容器里当智能体（2026-10-13）
--   一步 = ask（配额扣一）→ 从回复里取第一个 ``` 块当命令 → sh 跑它 → 结果（退出码、输出，过长就掐中间）记进历史
--   命令是 echo COMPLETE_TASK_AND_SUBMIT_FINAL_OUTPUT 就结束；配额用完也结束（配额 = 步数上限）
--   提示词 = mini-swe-agent 的 ProgramBench 模板原文（规则一字不改，只把"工具调用"换成一个 ```bash 块）+ 到目前为止的全部历史
--   后端：--cubical-handler=ask:mailbox:/box（LLM 在宿主机，容器断网）、--cubical-handler=sh:/workspace
--   题目、测试、镜像都没变：只在镜像上叠一层解释器（bench/Dockerfile）
------------------------------------------------------------------------
module Bench where

open import Cubical.Foundations.Prelude using (Type)
open import Cubical.Data.List.Base using (List; []; _∷_; _++_)
open import Cubical.Data.Nat.Base using (ℕ; zero; suc; _∸_; _<ᵇ_)
open import Cubical.Data.Bool.Base using (Bool; true; false)
open import Cubical.Data.Sigma using (_×_; _,_; fst; snd)
open import Cubical.Data.Maybe.Base using (Maybe; nothing; just)
open import Agda.Builtin.String using (String; primShowNat)
open import Str hiding (_=ₛ_)
open import Env
open import Later using (Run; done; move)

------------------------------------------------------------------------
-- §1 提示词：规则照抄 mini-swe-agent 的 programbench.yaml
------------------------------------------------------------------------
systemText : String
systemText =
  "You are a helpful assistant that can interact with a computer.\n\n"
  ++ₛ "This is a reverse-engineering benchmark. You are given a compiled binary and its documentation.\n"
  ++ₛ "Your job is to write a new, original codebase from scratch that produces an executable with identical behavior.\n"
  ++ₛ "You must figure out the behavior solely by running and interacting with the provided binary.\n"
  ++ₛ "Writing original code based on observed behavior is the entire point of this benchmark.\n\n"
  ++ₛ "Any approach that shortcuts this — finding existing source code, wrapping the binary,\n"
  ++ₛ "or installing the original tool — does not count as a solution. It will be detected by an\n"
  ++ₛ "automated judge, marked as a disqualification, and scored as a failure.\n"
  ++ₛ "The trace will be posted to an online wall of shame.\n\n"
  ++ₛ "<RULES>\n## What is not allowed\n\n### 1. Obtaining source code\n\n"
  ++ₛ "The only source of truth about what the executable does is the executable itself and its\n"
  ++ₛ "bundled documentation. You must not search the internet, package registries, or any external\n"
  ++ₛ "source for information about this project's source code. Even if you recognize what the\n"
  ++ₛ "executable is, you must reimplement it from behavioral observation alone.\n\n"
  ++ₛ "This includes but is not limited to:\n"
  ++ₛ "- Cloning or browsing the original GitHub repository, its forks, or mirrors\n"
  ++ₛ "- Downloading the project from package registries: `cargo install <project>`, `go get github.com/<org>/<project>`, `pip install <project>`, `apt-get source <project>`, `npm install <project>`, etc.\n"
  ++ₛ "- Fetching source tarballs from project websites (e.g., `curl https://lua.org/ftp/lua-5.5.0.tar.gz`)\n"
  ++ₛ "- Using a package manager to download the project as a dependency and then reading its cached source (e.g., navigating into `~/.cargo/registry/src/` or `$(go env GOPATH)/pkg/mod/`)\n"
  ++ₛ "- Searching the web for the project's source code or implementation details\n\n"
  ++ₛ "### 2. Wrapping or reusing the original binary\n\n"
  ++ₛ "Your submission must be a genuine reimplementation. The provided `./executable` is for\n"
  ++ₛ "observation only — your final solution must not depend on it or any other pre-built version\n"
  ++ₛ "of the same tool at runtime.\n\n"
  ++ₛ "This includes but is not limited to:\n"
  ++ₛ "- Writing a wrapper script that delegates to the original binary (e.g., `exec zstd \"$@\"`)\n"
  ++ₛ "- Installing the tool from a package manager and shimming to it (e.g., `apt-get install nnn && cp $(which nnn) ./executable`)\n"
  ++ₛ "- Writing a `compile.sh` that simply makes the provided binary executable (`chmod +x ./executable`) or copies it (`cp ./executable ./executable`)\n"
  ++ₛ "- Building a binary whose main function shells out to an external tool (e.g., `Command::new(\"miniserve\").args(args).exec()`)\n"
  ++ₛ "- Re-linking prebuilt `.o` object files found in the workspace without writing new source code\n\n"
  ++ₛ "### 3. Binary analysis of the provided executable\n\n"
  ++ₛ "All information about the provided `./executable` must be obtained by interacting with it\n"
  ++ₛ "through its normal user interface (CLI flags, stdin/stdout, etc.).\n"
  ++ₛ "- You MUST NOT decompile `./executable` or use disassemblers (objdump, Ghidra, etc.) on it\n"
  ++ₛ "- You MUST NOT use strace, ltrace, or similar tracing/instrumentation tools on `./executable`\n\n"
  ++ₛ "Note: this restriction applies ONLY to the provided `./executable`. You are free to use any\n"
  ++ₛ "analysis tools on binaries that you produce yourself during development.\n\n"
  ++ₛ "## What IS allowed\n\n"
  ++ₛ "- Running the executable with any inputs, flags, and arguments to observe its behavior\n"
  ++ₛ "- Reading any documentation files bundled in the workspace\n</RULES>"

-- 任务说明；sysinfo = uname 的输出
instanceText : String → String
instanceText sysinfo =
  "## Task context\n\n"
  ++ₛ "We want to write the source code for a given executable.\n"
  ++ₛ "The executable is located at `./executable` in the workspace root.\n\n"
  ++ₛ "You also have access to the existing documentation.\n\n"
  ++ₛ "## Your task\n\n"
  ++ₛ "Implement the source code to generate an executable of exactly identical behavior as the original.\n\n"
  ++ₛ "No project-specific dependencies are pre-installed.\n"
  ++ₛ "You do NOT have access to the internet.\n"
  ++ₛ "**IMPORTANT**: Make sure that the executable(s) and everything else that is an artifact is not committed, i.e., is in your `.gitignore` file.\n"
  ++ₛ "Finally, commit your changes.\n\n"
  ++ₛ "Make sure that you have a `./compile.sh` file that produces an executable `./executable` in the workspace root.\n"
  ++ₛ "`compile.sh` should be executable and should install any dependencies needed to compile the executable.\n"
  ++ₛ "If your compile.sh fails to compile on a fresh checkout, your task has failed.\n\n"
  ++ₛ "## Important: This is a reverse-engineering benchmark\n\n"
  ++ₛ "Your goal is to write original code from scratch that reproduces the executable's behavior.\n"
  ++ₛ "The only way to learn what the executable does is to run it and read its bundled documentation.\n\n"
  ++ₛ "Any attempt to obtain source code — whether successful or not — or to wrap/reuse the\n"
  ++ₛ "provided binary will be detected by an automated judge, disqualified, and scored as zero.\n"
  ++ₛ "See the full rules in the system prompt above. Key points:\n\n"
  ++ₛ "- Do NOT search the internet, clone repos, or download the project from any package registry\n"
  ++ₛ "- Do NOT wrap, shim, or delegate to the provided `./executable` or any installed version of the same tool\n"
  ++ₛ "- Do NOT decompile the provided `./executable` or use strace/ltrace on it (analyzing your own binaries is fine)\n"
  ++ₛ "- You SHOULD extensively test the executable to understand its behavior before writing code.\n"
  ++ₛ "  If you are dealing with a TUI, tmux/libtmux has been installed to help you test/inspect/it.\n\n"
  ++ₛ "## Recommended Workflow\n\n"
  ++ₛ "1. Explore all documentation files\n"
  ++ₛ "2. Play with the executable to understand its behavior (however, you MUST NOT decompile `./executable` or perform any other form of binary or strace/ltrace analysis on it)\n"
  ++ₛ "3. Write the source code to implement the behavior\n\n"
  ++ₛ "## Command Execution Rules\n\n"
  ++ₛ "You can execute bash commands and edit files to implement the necessary changes.\n\n"
  ++ₛ "You are operating in an environment where\n\n"
  ++ₛ "1. You issue exactly one command\n"
  ++ₛ "2. The system executes the command in a subshell\n"
  ++ₛ "3. You see the result\n"
  ++ₛ "4. You write your next command\n\n"
  ++ₛ "Each response should include:\n\n"
  ++ₛ "1. **Reasoning text** where you explain your analysis and plan\n"
  ++ₛ "2. Exactly one fenced code block starting with ```bash and ending with ``` containing the command to run\n\n"
  ++ₛ "**CRITICAL REQUIREMENTS:**\n\n"
  ++ₛ "- Your response SHOULD include reasoning text explaining what you're doing\n"
  ++ₛ "- Your response MUST include EXACTLY ONE ```bash code block; only its content is executed\n"
  ++ₛ "- Directory or environment variable changes are not persistent. Every action is executed in a new subshell.\n"
  ++ₛ "- However, you can prefix any action with `MY_ENV_VAR=MY_VALUE cd /path/to/working/dir && ...` or write/load environment variables from files\n"
  ++ₛ "- Each command is killed after 180 seconds (exit code 124); run long jobs in the background or split them up\n"
  ++ₛ "- Submit your changes and finish your work by issuing the following command: `echo COMPLETE_TASK_AND_SUBMIT_FINAL_OUTPUT`.\n"
  ++ₛ "  Do not combine it with any other command. <important>After this command, you cannot continue working on this task.</important>\n\n"
  ++ₛ "Example of a CORRECT response:\n<example_response>\n"
  ++ₛ "I need to understand the structure of the repository first. Let me check what files are in the current directory to get a better understanding of the codebase.\n\n"
  ++ₛ "```bash\nls -la\n```\n</example_response>\n\n"
  ++ₛ "<system_information>\n" ++ₛ sysinfo ++ₛ "</system_information>\n\n"
  ++ₛ "## Useful command examples\n\npython is available as python3\n\n"
  ++ₛ "### Create a new file:\n\n```bash\ncat <<'EOF' > newfile.py\nimport numpy as np\nhello = \"world\"\nprint(hello)\nEOF\n```\n\n"
  ++ₛ "### Edit files with sed:\n\n```bash\n# Replace all occurrences\nsed -i 's/old_string/new_string/g' filename.py\n\n# Replace only first occurrence\nsed -i 's/old_string/new_string/' filename.py\n```\n\n"
  ++ₛ "### View file content:\n\n```bash\n# View specific lines with numbers\nnl -ba filename.py | sed -n '10,20p'\n```\n\n"
  ++ₛ "### Any other command you want to run\n\n```bash\nanything\n```"

submitCmd : String
submitCmd = "echo COMPLETE_TASK_AND_SUBMIT_FINAL_OUTPUT"

formatError : String
formatError = "<error>\nYour response did not contain a ```bash code block, so nothing was executed.\nEvery response must contain exactly one ```bash block with the command to run.\n</error>"

-- 一条命令的结果：mini-swe-agent 的 observation_template，超过 10000 字符留头尾各 5000
observe : ℕ × String → String
observe (rc , out) = "<returncode>" ++ₛ primShowNat rc ++ₛ "</returncode>\n<output>\n" ++ₛ elide 10000 5000 out ++ₛ "\n</output>"

-- 历史：每步（LLM 的回复 , 执行结果）
History : Type
History = List (String × String)

transcript : ℕ → History → String
transcript k []             = ""
transcript k ((r , o) ∷ h) =
  "\n\n---\n## Step " ++ₛ primShowNat k ++ₛ " · your response\n" ++ₛ r
  ++ₛ "\n\n## Step " ++ₛ primShowNat k ++ₛ " · result\n" ++ₛ o
  ++ₛ transcript (suc k) h

-- 还剩 n 步、不到 20 步时的提醒（原模板放在 observation 里，这里放在提示词末尾）
lowSteps : ℕ → String
lowSteps n with n <ᵇ 21
... | false = ""
... | true  =
  "\n\n<IMPORTANT>\nThere is a limit to the steps you can take. You are now " ++ₛ primShowNat n
  ++ₛ " steps away from reaching your limit. After you reach your limit your current solution will be auto-submitted.\n"
  ++ₛ "At this point, please abort any specific issues that you are debugging or solving and focus on the big picture. Please make sure that\n"
  ++ₛ "1. Your solution compiles and produces an executable (it's ok if it is still missing functionality)\n"
  ++ₛ "2. If there are any steps left to do, or limitations that you are aware of, please write them to a document \"AGENT_REPORT.md\". Focus on handing off to the next agent, i.e., focus on clearly describing the problems and any todo items that are left over.\n</IMPORTANT>"

prompt : String → ℕ → History → String
prompt sys n []   = systemText ++ₛ "\n\n" ++ₛ instanceText sys
prompt sys n hist =
  systemText ++ₛ "\n\n" ++ₛ instanceText sys ++ₛ transcript 1 hist ++ₛ lowSteps n
  ++ₛ "\n\n---\nContinue: brief reasoning, then exactly one ```bash block with the next command."

------------------------------------------------------------------------
-- §2 主循环：配额 = 步数上限
------------------------------------------------------------------------
record Result : Type where
  constructor result
  field
    status : String          -- submitted ∣ step limit reached
    steps  : ℕ               -- 问了几次

R : Ix → Type
R _ = Result

E₀ : Env                     -- 不检查 Agda 模块：什么都看不见
E₀ = base (λ _ → false) []

ix₀ : ℕ → Ix
ix₀ n = (E₀ , n) , []

module Agent (budget : ℕ) where
  go   : (n : ℕ) → String → History → Run AgdaSig R (ix₀ n)
  step : (n : ℕ) → String → History → String → Run AgdaSig R (ix₀ n)

  go zero    sys hist = done (result "step limit reached" budget)
  go (suc n) sys hist = move (ask (prompt sys (suc n) hist)) (step n sys hist)

  step n sys hist reply with firstBlock reply
  ... | nothing  = go n sys (hist ++ ((reply , formatError) ∷ []))
  ... | just cmd with trim cmd =ₛ submitCmd
  ...   | true  = done (result "submitted" (budget ∸ n))
  ...   | false = move (sh cmd) λ o → go n sys (hist ++ ((reply , observe o) ∷ []))

-- 先问系统信息，再开始；300 步
agent : Run AgdaSig R (ix₀ 300)
agent = move (sh "uname -srvm") λ o → Agent.go 300 300 (snd o) []

------------------------------------------------------------------------
-- §3 探针：sh 这一步本身（不问 LLM）
------------------------------------------------------------------------
P : Ix → Type
P _ = ℕ × String

probe : Run AgdaSig P (ix₀ 0)
probe = move (sh "echo out; echo err 1>&2; exit 3") λ o → done o

elideProbe : Run AgdaSig P (ix₀ 0)      -- 2 万字符的输出被掐成头尾各 5000
elideProbe = move (sh "head -c 20000 /dev/zero | tr '\\0' x") λ o → done (fst o , elide 10000 5000 (snd o))
