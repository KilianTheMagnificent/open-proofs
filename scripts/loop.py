#!/usr/bin/env python3
"""Compatibility shim: the loop commands moved to `./op` (scripts/op.py).

  python3 scripts/loop.py preflight [--full]   checker self-tests (integrity + adversarial suites)
  python3 scripts/loop.py <anything else>      forwarded to ./op
"""

from __future__ import annotations

import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent


def run(cmd: list[str]) -> int:
    print("$ " + " ".join(cmd), flush=True)
    return subprocess.call(cmd, cwd=ROOT)


def preflight(full: bool) -> int:
    rc = run([sys.executable, "scripts/check.py", "--integrity"])
    rc |= run([sys.executable, "tests/run_adversarial.py", "--only", "lint"])
    rc |= run([sys.executable, "tests/run_adversarial.py", "--only", "integrity"])
    if full:
        rc |= run([sys.executable, "tests/run_adversarial.py", "--only", "lean"])
    print("PREFLIGHT " + ("OK" if rc == 0 else "FAILED: do not trust the checker until this is fixed"))
    return rc


def main() -> int:
    args = sys.argv[1:]
    if args and args[0] == "preflight":
        return preflight("--full" in args)
    return subprocess.call([sys.executable, str(ROOT / "scripts" / "op.py"), *args], cwd=ROOT)


if __name__ == "__main__":
    sys.exit(main())
