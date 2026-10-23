#!/usr/bin/env python3
"""Scan the pinned formal-conjectures checkout and list every `sorry`-bodied theorem.

Reads only the pinned upstream package (`.lake/packages/formal_conjectures`) and,
optionally, a local copy of the erdosproblems.com status database
(teorth/erdosproblems `data/problems.yaml`). Writes `work/candidates.json` (gitignored, regenerable):
one record per upstream theorem whose proof is exactly `sorry`, with its category,
attributes, statement text and (for Erdős problems) the erdosproblems.com status.

This is a *triage aid*, not part of the trusted checker. It uses regexes over
source text, so it can mis-parse unusual files; the checker never relies on it.

Usage:
  python3 scripts/triage.py [--erdos-yaml work/erdos-db/problems.yaml]
"""

from __future__ import annotations

import argparse
import json
import re
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
UPSTREAM = ROOT / ".lake" / "packages" / "formal_conjectures"

DECL_RE = re.compile(
    r"^(?P<mods>(?:(?:private|protected|nonrec|noncomputable)\s+)*)"
    r"(?P<kw>theorem|lemma)\s+(?P<name>[^\s:({\[]+)",
    re.MULTILINE,
)
NEXT_TOPLEVEL_RE = re.compile(
    r"^(?:/--|@\[|theorem\s|lemma\s|def\s|abbrev\s|noncomputable\s|instance\s|structure\s|"
    r"inductive\s|class\s|namespace\s|end\s|section\b|open\s|variable\s|private\s|protected\s|"
    r"local\s|scoped\s|notation\b|example\b|set_option\s|attribute\s|/-)",
    re.MULTILINE,
)
NS_RE = re.compile(r"^(namespace|end|section)\b[ \t]*([^\s]*)", re.MULTILINE)
SORRY_BODY_RE = re.compile(r":=\s*(?:by\s+)?sorry\s*$", re.DOTALL)


def strip_line_comments(s: str) -> str:
    return re.sub(r"--[^\n]*", "", s)


def namespace_at(text: str, pos: int) -> str:
    stack: list[tuple[str, str]] = []
    for m in NS_RE.finditer(text, 0, pos):
        kind, arg = m.group(1), m.group(2)
        if kind in ("namespace", "section"):
            stack.append((kind, arg))
        elif kind == "end" and stack:
            stack.pop()
    return ".".join(a for k, a in stack if k == "namespace" and a)


def attrs_before(text: str, start: int) -> str:
    """Return the `@[...]` attribute block immediately before `start` (may span lines)."""
    head = text[:start].rstrip()
    if not head.endswith("]"):
        return ""
    depth = 0
    i = len(head) - 1
    while i >= 0:
        c = head[i]
        if c == "]":
            depth += 1
        elif c == "[":
            depth -= 1
            if depth == 0:
                if i > 0 and head[i - 1] == "@":
                    return head[i - 1:]
                return ""
        i -= 1
    return ""


def docstring_before(text: str, start: int, attrs: str) -> str:
    head = text[:start].rstrip()
    if attrs:
        head = head[: len(head) - len(attrs)].rstrip()
    if head.endswith("-/"):
        j = head.rfind("/--")
        if j != -1:
            return head[j + 3: -2].strip()
    return ""


def parse_file(path: Path) -> list[dict]:
    text = path.read_text(encoding="utf-8")
    out = []
    decls = list(DECL_RE.finditer(text))
    for m in decls:
        start = m.start()
        name = m.group("name")
        body_start = m.end()
        nxt = NEXT_TOPLEVEL_RE.search(text, body_start)
        end = nxt.start() if nxt else len(text)
        chunk = strip_line_comments(text[body_start:end]).rstrip()
        attrs = attrs_before(text, start)
        ns = namespace_at(text, start)
        full = name if name.startswith("_root_.") else (f"{ns}.{name}" if ns else name)
        full = full.removeprefix("_root_.")
        is_sorry = bool(SORRY_BODY_RE.search(chunk))
        stmt = chunk
        k = chunk.rfind(":=")
        if k != -1:
            stmt = chunk[:k]
        cat = re.search(r"category\s+(research\s+open|research\s+solved|textbook|test|API)", attrs)
        out.append(
            {
                "decl": full,
                "line": text.count("\n", 0, start) + 1,
                "category": re.sub(r"\s+", " ", cat.group(1)) if cat else None,
                "formal_proof": "formal_proof" in attrs,
                "question": bool(re.search(r"\bquestion\b", attrs)),
                "sorry": is_sorry,
                "statement": re.sub(r"\s+", " ", stmt).strip(),
                "doc": re.sub(r"\s+", " ", docstring_before(text, start, attrs))[:600],
            }
        )
    return out


def module_name(path: Path) -> str:
    rel = path.relative_to(UPSTREAM).with_suffix("")
    parts = []
    for p in rel.parts:
        parts.append(f"«{p}»" if not re.match(r"^[A-Za-z_][A-Za-z0-9_']*$", p) else p)
    return ".".join(parts)


def load_erdos_status(yaml_path: Path | None) -> dict[str, dict]:
    if not yaml_path or not yaml_path.exists():
        return {}
    # Minimal YAML reader for the flat structure of problems.yaml (avoids a pyyaml dependency).
    status: dict[str, dict] = {}
    cur: dict | None = None
    section = None
    for line in yaml_path.read_text(encoding="utf-8").splitlines():
        m = re.match(r'^- number: "?(\d+)"?', line)
        if m:
            cur = {"number": m.group(1)}
            status[m.group(1)] = cur
            section = None
            continue
        if cur is None:
            continue
        m = re.match(r"^  (\w+):\s*(.*)$", line)
        if m:
            section = m.group(1)
            val = m.group(2).strip()
            if val:
                cur[section] = val.strip('"')
            continue
        m = re.match(r'^    state:\s*"?([^"]*)"?', line)
        if m and section:
            cur[f"{section}.state"] = m.group(1)
    return status


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--erdos-yaml", default=str(ROOT / "work" / "erdos-db" / "problems.yaml"))
    ap.add_argument("--out", default=str(ROOT / "work" / "candidates.json"))
    args = ap.parse_args()

    commit = subprocess.run(
        ["git", "-C", str(UPSTREAM), "rev-parse", "HEAD"], capture_output=True, text=True, check=True
    ).stdout.strip()
    erdos = load_erdos_status(Path(args.erdos_yaml))
    records = []
    for path in sorted((UPSTREAM / "FormalConjectures").rglob("*.lean")):
        rel = path.relative_to(UPSTREAM)
        for d in parse_file(path):
            if not d["sorry"]:
                continue
            d["file"] = str(rel)
            d["module"] = module_name(path)
            if rel.parts[1] == "ErdosProblems" and path.stem.isdigit():
                e = erdos.get(path.stem, {})
                d["erdos"] = {
                    "number": path.stem,
                    "informal": e.get("informal_status.state"),
                    "formal": e.get("formal_status.state"),
                }
            records.append(d)
    out = {"upstream_commit": commit, "count": len(records), "records": records}
    Path(args.out).parent.mkdir(parents=True, exist_ok=True)
    Path(args.out).write_text(json.dumps(out, indent=1, ensure_ascii=False) + "\n", encoding="utf-8")
    by_cat: dict[str, int] = {}
    for r in records:
        by_cat[str(r["category"])] = by_cat.get(str(r["category"]), 0) + 1
    print(f"upstream {commit}: {len(records)} sorry-bodied theorems; by category: {by_cat}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
