#!/usr/bin/env python3
"""信箱中继（宿主机）：容器里的后端把提示词写成 BOX/n.prompt，这里问 DeepSeek，答案写成 BOX/n.answer。
容器断网，LLM 只在这里。密钥只从环境变量 LOJITA_API_KEY 来。用法：relay.py BOX"""
import json, os, sys, time, urllib.request

BOX = sys.argv[1]
URL = os.environ.get("LOJITA_URL", "https://api.deepseek.com/chat/completions")
MODEL = os.environ.get("LOJITA_MODEL", "deepseek-flash")
KEY = os.environ["LOJITA_API_KEY"]
USAGE = os.path.join(BOX, "usage.jsonl")

def settled(path):
    """文件写完了：存在、大小 1 秒内没变"""
    if not os.path.exists(path):
        return False
    s1 = os.path.getsize(path); time.sleep(1.0)
    return os.path.exists(path) and os.path.getsize(path) == s1

def ask(prompt):
    body = json.dumps({"model": MODEL, "messages": [{"role": "user", "content": prompt}]}).encode()
    req = urllib.request.Request(URL, data=body, headers={
        "Content-Type": "application/json", "Authorization": "Bearer " + KEY})
    for attempt in range(5):
        try:
            t0 = time.time()
            with urllib.request.urlopen(req, timeout=900) as r:
                data = json.loads(r.read())
            usage = data.get("usage", {}); usage["seconds"] = round(time.time() - t0, 1)
            return data["choices"][0]["message"]["content"], usage
        except Exception as e:  # 网络 / 限流：退避重试
            print(f"[relay] attempt {attempt}: {e}", flush=True)
            time.sleep(5 * (attempt + 1))
    raise SystemExit("[relay] giving up")

n = 0
while True:
    p = os.path.join(BOX, f"{n}.prompt")
    while not settled(p):
        if os.path.exists(os.path.join(BOX, "stop")):
            sys.exit(0)
        time.sleep(0.5)
    prompt = open(p, encoding="utf-8").read()
    print(f"[relay] {n}: prompt {len(prompt)} chars", flush=True)
    answer, usage = ask(prompt)
    with open(USAGE, "a") as f:
        f.write(json.dumps({"n": n, "prompt_chars": len(prompt), "answer_chars": len(answer), **usage}) + "\n")
    tmp = os.path.join(BOX, f"{n}.answer.tmp")
    with open(tmp, "w", encoding="utf-8") as f:
        f.write(answer)
    os.rename(tmp, os.path.join(BOX, f"{n}.answer"))   # 后端一见到 n.answer 就读，所以要原子地出现
    print(f"[relay] {n}: answer {len(answer)} chars, {usage}", flush=True)
    n += 1
