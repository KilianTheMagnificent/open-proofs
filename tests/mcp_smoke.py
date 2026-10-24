#!/usr/bin/env python3
"""Smoke test for the Lean LSP MCP server configured in .mcp.json.

Starts the server exactly as .mcp.json says (stdio transport), lists its tools, and calls the
diagnostics and goal-state tools on a small scratch file under work/. Exit code 0 iff both calls
return the expected content.

Usage: python3 tests/mcp_smoke.py [--list]
"""

from __future__ import annotations

import json
import os
import subprocess
import sys
import threading
import time
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
PROBE = ROOT / "work" / "mcp_probe" / "Probe.lean"
PROBE_SRC = """import Mathlib.Tactic.NormNum

theorem probe_ok (a b : Nat) (h : a = b) : b = a := by
  exact h.symm

theorem probe_goal (n : Nat) (h : 0 < n) : 1 ≤ n := by
  omega

theorem probe_err : (2 : Nat) + 2 = 5 := by
  norm_num
"""


class Client:
    def __init__(self, cmd: list[str], env: dict, cwd: Path):
        self.p = subprocess.Popen(cmd, stdin=subprocess.PIPE, stdout=subprocess.PIPE,
                                  stderr=subprocess.PIPE, env=env, cwd=cwd, text=True, bufsize=1)
        self.id = 0
        self.stderr: list[str] = []
        threading.Thread(target=self._drain, daemon=True).start()

    def _drain(self) -> None:
        for line in self.p.stderr:
            self.stderr.append(line)

    def send(self, msg: dict) -> None:
        self.p.stdin.write(json.dumps(msg) + "\n")
        self.p.stdin.flush()

    def request(self, method: str, params: dict, timeout: float = 600) -> dict:
        self.id += 1
        rid = self.id
        self.send({"jsonrpc": "2.0", "id": rid, "method": method, "params": params})
        deadline = time.time() + timeout
        while time.time() < deadline:
            line = self.p.stdout.readline()
            if not line:
                raise RuntimeError("server closed stdout; stderr:\n" + "".join(self.stderr[-30:]))
            try:
                msg = json.loads(line)
            except json.JSONDecodeError:
                continue
            if msg.get("id") == rid:
                return msg
        raise TimeoutError(method)

    def close(self) -> None:
        try:
            self.p.stdin.close()
            self.p.terminate()
            self.p.wait(timeout=10)
        except Exception:
            self.p.kill()


def main() -> int:
    cfg = json.loads((ROOT / ".mcp.json").read_text())["mcpServers"]["lean-lsp"]
    env = dict(os.environ)
    env.update(cfg.get("env", {}))
    env["PATH"] = f"{Path.home() / '.elan' / 'bin'}:{Path.home() / '.local' / 'bin'}:{env.get('PATH', '')}"
    PROBE.parent.mkdir(parents=True, exist_ok=True)
    PROBE.write_text(PROBE_SRC)
    c = Client([cfg["command"], *cfg.get("args", [])], env, ROOT)
    ok = True
    try:
        init = c.request("initialize", {"protocolVersion": "2025-06-18", "capabilities": {},
                                        "clientInfo": {"name": "mcp_smoke", "version": "0"}}, 120)
        print("server:", init.get("result", {}).get("serverInfo"))
        c.send({"jsonrpc": "2.0", "method": "notifications/initialized", "params": {}})
        tools = c.request("tools/list", {}, 120)["result"]["tools"]
        names = [t["name"] for t in tools]
        print("tools:", ", ".join(names))
        if "--list" in sys.argv:
            return 0
        t0 = time.time()
        diag = c.request("tools/call", {"name": "lean_diagnostic_messages",
                                        "arguments": {"file_path": str(PROBE)}}, 900)
        dtext = json.dumps(diag.get("result", diag))
        print(f"diagnostics ({time.time() - t0:.1f}s):", dtext[:600])
        if "probe_err" not in dtext and "unsolved" not in dtext.lower() and "error" not in dtext.lower():
            ok = False
            print("FAIL: expected an error diagnostic for probe_err")
        t0 = time.time()
        goal = c.request("tools/call", {"name": "lean_goal",
                                        "arguments": {"file_path": str(PROBE), "line": 7, "column": 3}}, 600)
        gtext = json.dumps(goal.get("result", goal), ensure_ascii=False)
        print(f"goal ({time.time() - t0:.1f}s):", gtext[:600])
        if "1 ≤ n" not in gtext and "1 \\u2264 n" not in gtext:
            ok = False
            print("FAIL: expected goal `1 ≤ n` at line 7")
    finally:
        c.close()
    print("MCP SMOKE " + ("OK" if ok else "FAILED"))
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
