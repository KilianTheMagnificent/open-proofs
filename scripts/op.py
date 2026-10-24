#!/usr/bin/env python3
"""op: the open-proofs agent CLI (run as `./op <command>` from the repository root).

Commands (all print plain text; most accept --json):

  status [--brief]                 queue, locks, recent results (--brief: SessionStart hook, <1 s)
  next [--agent A] [--tier a,b] [--max-difficulty N] [--dir D] [--json]
                                   claim the next target (lock file; stale locks expire)
  heartbeat TARGET                 refresh your claim (provers: every ~20 min)
  release TARGET [--reason R]      give a claim back without an outcome
  scaffold TARGET [--force]        write the result file with the exact upstream statement and
                                   verify that it elaborates to the upstream type
  try FILE [--goals] [--timeout S] fast single-file compile: errors, warnings, goal states
  search name|type PATTERN         local declaration index (Mathlib, formal-conjectures, OpenProofs)
  search exact GOAL [--ctx C] [--import M] [--tactic exact?|apply?|rw?|simp?|aesop?|hint]
                                   run a search tactic on a goal and print its suggestions
  check TARGET|CLAIM [--assessment A] [--summary S] [--notes N]
                                   create the claim if needed and run the full checker (records)
  finish TARGET --outcome O --notes TEXT [--claim C] [--retry]
                                   close a target (proved needs a current PASS); releases the lock
  notes TARGET [--add TEXT]        per-target attempt log (what was tried, dead ends)
  refill [--dirs all|D1,D2] [--dry-run]
                                   add scored targets from every formal-conjectures directory
  build MODULE...                  lake build under the global build lock with resource caps
  commit -m MSG                    commit ledger/claims/notes/outbox/docs and checked results
  preflight [--full] | recheck     checker self-tests | re-check every claim

Resource caps (environment, with defaults): OP_LEAN_THREADS=2 (LEAN_NUM_THREADS for builds,
`-j` for try), OP_LEAN_MEMORY_MB=8192 (`lean -M`), OP_TRY_TIMEOUT=300 s, OP_MAX_TRIES=4 concurrent
`try` processes, OP_BUILD_TIMEOUT=3600 s, OP_LOCK_TTL_HOURS=3. Builds and checks are serialized
by a global build lock, so N parallel provers never run more than one `lake build` at a time.
"""

from __future__ import annotations

import argparse
import contextlib
import datetime as dt
import errno
import fcntl
import hashlib
import json
import os
import re
import socket
import subprocess
import sys
import time
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / "scripts"))

QUEUE = ROOT / "ledger" / "queue.json"
CLAIMS = ROOT / "claims.json"
RESULTS = ROOT / "ledger" / "results.json"
NOTES = ROOT / "ledger" / "notes"
LOCKS = ROOT / "work" / "locks"
TARGET_LOCKS = LOCKS / "targets"
UP = ROOT / ".lake" / "packages" / "formal_conjectures"
UP_SRC = UP / "FormalConjectures"
UP_BUILD = UP / ".lake" / "build" / "lib" / "lean"
OUR_BUILD = ROOT / ".lake" / "build" / "lib" / "lean"
TRYDIR = ROOT / "work" / "try"
INDEX = ROOT / "work" / "index" / "decls.tsv"

CAPS = {
    "threads": int(os.environ.get("OP_LEAN_THREADS", "2")),
    "memory_mb": int(os.environ.get("OP_LEAN_MEMORY_MB", "8192")),
    "try_timeout": int(os.environ.get("OP_TRY_TIMEOUT", "300")),
    "max_tries": int(os.environ.get("OP_MAX_TRIES", "4")),
    "build_timeout": int(os.environ.get("OP_BUILD_TIMEOUT", "3600")),
    "lock_ttl_h": float(os.environ.get("OP_LOCK_TTL_HOURS", "3")),
}
TIER_ORDER = {"a": 0, "b": 1, "c": 2}
OUTCOMES = ["proved", "failed", "blocked", "possible-misformalization", "skipped"]
DIR_SHORT = {"ErdosProblems": "Erdos"}


# ----------------------------------------------------------------------------- basics


def now() -> str:
    return dt.datetime.now(dt.timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")


def parse_time(s: str | None) -> float:
    if not s:
        return 0.0
    return dt.datetime.strptime(s, "%Y-%m-%dT%H:%M:%SZ").replace(tzinfo=dt.timezone.utc).timestamp()


def lean_env() -> dict:
    e = dict(os.environ)
    e["PATH"] = f"{Path.home() / '.elan' / 'bin'}:{e.get('PATH', '')}"
    e["LEAN_NUM_THREADS"] = str(CAPS["threads"])
    return e


def die(msg: str, code: int = 2) -> None:
    print(f"op: {msg}", file=sys.stderr)
    sys.exit(code)


@contextlib.contextmanager
def flock(name: str, timeout: float | None = None, poll: float = 0.5):
    """Exclusive advisory lock on work/locks/<name>; waits up to `timeout` seconds (None = forever)."""
    LOCKS.mkdir(parents=True, exist_ok=True)
    fh = open(LOCKS / name, "a+")
    start = time.time()
    while True:
        try:
            fcntl.flock(fh, fcntl.LOCK_EX | fcntl.LOCK_NB)
            break
        except OSError as e:
            if e.errno not in (errno.EAGAIN, errno.EACCES):
                raise
            if timeout is not None and time.time() - start > timeout:
                fh.close()
                raise TimeoutError(f"lock {name} busy for {timeout}s")
            time.sleep(poll)
    try:
        yield
    finally:
        fcntl.flock(fh, fcntl.LOCK_UN)
        fh.close()


@contextlib.contextmanager
def try_slot():
    """One of OP_MAX_TRIES concurrent `try` slots (bounds parallel Lean processes)."""
    LOCKS.mkdir(parents=True, exist_ok=True)
    while True:
        for k in range(CAPS["max_tries"]):
            fh = open(LOCKS / f"try.{k}", "a+")
            try:
                fcntl.flock(fh, fcntl.LOCK_EX | fcntl.LOCK_NB)
            except OSError:
                fh.close()
                continue
            try:
                yield k
            finally:
                fcntl.flock(fh, fcntl.LOCK_UN)
                fh.close()
            return
        time.sleep(1.0)


def slug(target: str) -> str:
    base = re.sub(r"[^A-Za-z0-9_.-]+", "_", target.replace("«", "").replace("»", ""))[:100]
    return f"{base}-{hashlib.sha1(target.encode()).hexdigest()[:6]}"


# ----------------------------------------------------------------------------- queue


def load_queue() -> dict:
    return json.loads(QUEUE.read_text())


def save_queue(q: dict) -> None:
    """One target per line so git diffs stay small."""
    q["updated"] = now()
    head = {k: v for k, v in q.items() if k != "targets"}
    lines = ["{"]
    for k, v in head.items():
        lines.append(f" {json.dumps(k)}: {json.dumps(v, ensure_ascii=False)},")
    lines.append(' "targets": [')
    ts = q["targets"]
    for i, t in enumerate(ts):
        lines.append("  " + json.dumps(t, ensure_ascii=False, sort_keys=True) + ("," if i < len(ts) - 1 else ""))
    lines.append(" ]")
    lines.append("}")
    tmp = QUEUE.with_suffix(".tmp")
    tmp.write_text("\n".join(lines) + "\n")
    tmp.replace(QUEUE)


def sort_key(t: dict):
    return (TIER_ORDER.get(t.get("tier", "c"), 9), t.get("difficulty", 3), t.get("priority", 500), t["id"])


def find_target(q: dict, tid: str) -> dict:
    t = next((x for x in q["targets"] if x["id"] == tid), None)
    if t is None:
        cands = [x["id"] for x in q["targets"] if tid in x["id"]]
        hint = f" (did you mean: {', '.join(cands[:5])})" if cands else ""
        die(f"no target {tid!r} in the queue{hint}")
    return t


def lock_path(tid: str) -> Path:
    return TARGET_LOCKS / f"{slug(tid)}.json"


def read_lock(tid: str) -> dict | None:
    p = lock_path(tid)
    if not p.exists():
        return None
    try:
        return json.loads(p.read_text())
    except json.JSONDecodeError:
        return None


def lock_stale(lk: dict) -> bool:
    return time.time() - parse_time(lk.get("heartbeat_at")) > CAPS["lock_ttl_h"] * 3600


def sweep_stale(q: dict) -> list[str]:
    """Return expired claims to `pending` (call with the queue lock held)."""
    freed = []
    for t in q["targets"]:
        if t.get("status") != "in-progress":
            continue
        lk = read_lock(t["id"])
        if lk is None or lock_stale(lk):
            t["status"] = "pending"
            if t.get("attempts") and t["attempts"][-1].get("outcome") is None:
                t["attempts"][-1].update({"finished": now(), "outcome": "expired",
                                          "notes": "claim expired (no heartbeat)"})
            lock_path(t["id"]).unlink(missing_ok=True)
            freed.append(t["id"])
    return freed


# ----------------------------------------------------------------------------- notes


def notes_path(tid: str) -> Path:
    return NOTES / f"{slug(tid)}.md"


def add_note(tid: str, text: str, agent: str = "") -> None:
    NOTES.mkdir(parents=True, exist_ok=True)
    p = notes_path(tid)
    with flock("notes"):
        if not p.exists():
            p.write_text(f"# Attempt log: `{tid}`\n\nAppend-only. Record what was tried, dead ends, and "
                         f"the next idea, so later sessions do not repeat them.\n\n")
        with p.open("a") as fh:
            fh.write(f"- {now()} [{agent or os.environ.get('OP_AGENT', 'agent')}] {text.strip()}\n")


def read_notes(tid: str, last: int = 0) -> list[str]:
    p = notes_path(tid)
    if not p.exists():
        return []
    entries = [l for l in p.read_text().splitlines() if l.startswith("- ")]
    return entries[-last:] if last else entries


# ----------------------------------------------------------------------------- upstream source


def split_name(name: str) -> list[str]:
    """Split a dotted Lean name, honouring «...» escapes (`A.«1609.08688».b` has three parts)."""
    return [p.strip("«»") for p in re.findall(r"«[^»]*»|[^.]+", name)]


def module_to_upstream_file(module: str) -> Path:
    parts = split_name(module)
    if parts[0] != "FormalConjectures":
        die(f"not an upstream FormalConjectures module: {module}")
    return UP.joinpath(*parts).with_suffix(".lean")


def olean_exists(module: str) -> bool:
    parts = split_name(module)
    rel = Path(*parts).with_suffix(".olean")
    if parts[0].startswith("FormalConjectures"):
        return (UP_BUILD / rel).exists()
    if parts[0].startswith("OpenProofs"):
        return (OUR_BUILD / rel).exists()
    return True  # Mathlib and friends come from the cache


def upstream_decl(module: str, decl: str) -> dict:
    """Locate a declaration in the upstream source and return the pieces a scaffold needs."""
    import triage

    path = module_to_upstream_file(module)
    src = path.read_text(encoding="utf-8")
    info = next((d for d in triage.parse_file(path) if d["decl"] == decl), None)
    if info is None:
        die(f"{decl} not found in {path.relative_to(UP)}")
    lines = src.splitlines()
    start = info["line"] - 1
    # Statement text: from the keyword to the final `:= by sorry` / `:= sorry` of the chunk.
    m = re.compile(r"^(?:(?:private|protected|nonrec|noncomputable)\s+)*(theorem|lemma)\s+(\S+)").match(lines[start])
    if not m:
        die(f"cannot parse the declaration line of {decl}")
    local_name = m.group(2)
    rest = "\n".join(lines[start:])
    nxt = triage.NEXT_TOPLEVEL_RE.search(rest, m.end())
    chunk = rest[: nxt.start()] if nxt else rest
    pm = list(re.finditer(r":=\s*(?:by\s+)?sorry\b", chunk))
    if not pm:
        die(f"{decl}: upstream proof is not a bare placeholder; nothing to scaffold")
    statement = chunk[m.end(): pm[-1].start()].rstrip()
    # `open ... in` lines directly above (between docstring/attributes and the keyword).
    prefix = []
    j = start - 1
    while j >= 0:
        s = lines[j].strip()
        if re.match(r"^open\b.*\bin$", s):
            prefix.insert(0, s)
            j -= 1
            continue
        if s.startswith("@[") or s.endswith("]") and "@[" in "\n".join(lines[max(0, j - 3): j + 1]):
            j -= 1
            continue
        break
    head = src[: sum(len(l) + 1 for l in lines[:start])]
    code = re.sub(r"/-.*?-/", "", head, flags=re.S)
    opens = [l.strip() for l in code.splitlines() if re.match(r"^open\b", l.strip()) and not l.strip().endswith(" in")]
    variables = []
    vm = re.finditer(r"^variable\b[^\n]*(?:\n[ \t]+[^\n]*)*", code, re.M)
    for v in vm:
        if re.search(r"\bin\s*$", v.group(0)):
            continue  # `variable ... in` scopes only the next upstream declaration
        variables.append(v.group(0).rstrip())
    ns = decl[: len(decl) - len(local_name)].rstrip(".") if decl.endswith(local_name) else ""
    local_notation = bool(re.search(r"^\s*local\s+(notation|infix|prefix|postfix|macro)", code, re.M))
    return {"path": path, "line": info["line"], "local_name": local_name, "statement": statement,
            "namespace": ns, "opens": opens, "open_in": prefix, "variables": variables,
            "category": info["category"], "formal_proof": info["formal_proof"],
            "local_notation": local_notation}


def ident(s: str) -> str:
    s = re.sub(r"[^A-Za-z0-9_]+", "_", s).strip("_")
    return s if re.match(r"^[A-Za-z_]", s) else f"P{s}"


def scaffold_paths(module: str, local_name: str) -> tuple[Path, str]:
    parts = split_name(module)[1:]  # drop FormalConjectures
    top = DIR_SHORT.get(parts[0], ident(parts[0]))
    stem = "_".join(ident(p) for p in parts[1:]) or "Main"
    short = ident(local_name.replace(".", "_"))[:60]
    rel = Path("OpenProofs") / "Results" / top / f"{stem}_{short}.lean"
    mod = ".".join(rel.with_suffix("").parts)
    return ROOT / rel, mod


# ----------------------------------------------------------------------------- building and compiling


def build(modules: list[str], quiet: bool = False) -> tuple[int, str]:
    if not modules:
        return 0, ""
    with flock("build"):
        p = subprocess.run(["lake", "build", *modules], cwd=ROOT, env=lean_env(), capture_output=True,
                           text=True, timeout=CAPS["build_timeout"])
    out = "\n".join(l for l in (p.stdout + p.stderr).splitlines() if not l.startswith(("✔", "⣿", "info:")))
    if not quiet and p.returncode != 0:
        print(out[-3000:])
    return p.returncode, out


def imports_of(path: Path) -> list[str]:
    import lint

    return lint.imports_of(path.read_text(encoding="utf-8"))


def ensure_deps(path: Path) -> list[str]:
    missing = [m for m in imports_of(path) if not olean_exists(m)]
    if missing:
        print(f"op: building missing imports first: {' '.join(missing)}", flush=True)
        rc, _ = build(missing)
        if rc != 0:
            die("could not build the imports (see output above)")
    return missing


def run_lean(path: Path, timeout: int) -> tuple[list[dict], str, float, bool]:
    t0 = time.time()
    cmd = ["lake", "env", "lean", "--json", f"-j{CAPS['threads']}", f"-M{CAPS['memory_mb']}", str(path)]
    rc = None
    with try_slot():
        try:
            p = subprocess.run(cmd, cwd=ROOT, env=lean_env(), capture_output=True, text=True, timeout=timeout)
            out, timed_out, rc = p.stdout + p.stderr, False, p.returncode
        except subprocess.TimeoutExpired as e:
            out = (e.stdout or b"").decode() if isinstance(e.stdout, bytes) else (e.stdout or "")
            timed_out = True
    msgs, other = [], []
    for line in out.splitlines():
        if line.startswith("{"):
            try:
                msgs.append(json.loads(line))
                continue
            except json.JSONDecodeError:
                pass
        if line.strip():
            other.append(line)
    if not timed_out and rc not in (0, None) and not any(m.get("severity") == "error" for m in msgs):
        # Lean died without reporting an error (e.g. memory_exception under -M, or a crash):
        # never let that look like success.
        tail = " | ".join(other[-3:])[:400]
        msgs.append({"severity": "error", "pos": {"line": 1, "column": 0}, "kind": "crash",
                     "data": f"lean exited with code {rc} without an error message "
                             f"(crash or resource limit -M{CAPS['memory_mb']}MB): {tail}"})
    return msgs, "\n".join(other), time.time() - t0, timed_out


def goals_copy(src: Path) -> Path:
    """Copy with `trace_state` before every tactic-position placeholder, to show the goals there."""
    text = src.read_text(encoding="utf-8")
    text = re.sub(r"^(\s*)sorry\s*$", r"\1trace_state\n\1sorry", text, flags=re.M)
    text = re.sub(r"\bby\s+sorry\b", "by trace_state; sorry", text)
    TRYDIR.mkdir(parents=True, exist_ok=True)
    dst = TRYDIR / f"goals_{os.getpid()}_{src.name}"
    dst.write_text(text)
    return dst


def format_msgs(msgs: list[dict], fname: str) -> list[str]:
    out = []
    for m in sorted(msgs, key=lambda m: (m["pos"]["line"], m["pos"]["column"])):
        sev = m["severity"]
        tag = {"information": "goal" if m.get("kind") == "trace" else "info"}.get(sev, sev)
        data = m["data"].rstrip()
        out.append(f"{fname}:{m['pos']['line']}:{m['pos']['column']}: {tag}: {data}")
    return out


# ----------------------------------------------------------------------------- commands


def cmd_status(args) -> int:
    q = load_queue()
    counts: dict[str, int] = {}
    for t in q["targets"]:
        counts[t["status"]] = counts.get(t["status"], 0) + 1
    branch = current_branch()
    pending = sorted([t for t in q["targets"] if t["status"] == "pending"], key=sort_key)
    inprog = [t for t in q["targets"] if t["status"] == "in-progress"]
    res = {}
    if RESULTS.exists():
        res = json.loads(RESULTS.read_text()).get("results", {})
    recent = sorted(res.items(), key=lambda kv: kv[1]["check"]["checked_at"], reverse=True)[: (3 if args.brief else 8)]
    npass = sum(1 for v in res.values() if v["check"]["verdict"] == "PASS")
    print(f"open-proofs on branch {branch} | claims: {npass}/{len(res)} PASS | queue: "
          + ", ".join(f"{k} {v}" for k, v in sorted(counts.items())))
    if inprog:
        print("in progress:")
        for t in inprog:
            lk = read_lock(t["id"]) or {}
            age = (time.time() - parse_time(lk.get("heartbeat_at"))) / 60 if lk else None
            state = "no lock" if not lk else (f"{lk.get('agent')}, heartbeat {age:.0f} min ago"
                                              + (" (STALE)" if lock_stale(lk) else ""))
            print(f"  {t['id']}  [{state}]")
    print("next up:")
    for t in pending[: (3 if args.brief else 10)]:
        print(f"  tier {t['tier']} d{t.get('difficulty', '?')} {t['id']}  ({t.get('upstream_category')})")
    print("recent results:")
    for rid, e in recent:
        c = e["check"]
        print(f"  {c['verdict']:<4} {rid}  ({e['claim'].get('assessment')}, {c['checked_at'][:10]})")
    if stop_requested():
        print("STOP requested (work/STOP): loops will not claim new targets (./op stop --clear).")
    if args.brief:
        print("Say 'startup' (or 'go') to run the proving loop; see AGENTS.md 'Startup'.")
    return 0


def claim(tid: str | None, agent: str, tiers=None, max_difficulty=None, dir_filter=None) -> dict | None:
    """Claim `tid` (or the best pending target) for `agent`. Returns the target, or None."""
    with flock("queue", timeout=60):
        q = load_queue()
        freed = sweep_stale(q)
        if tid is not None:
            t = find_target(q, tid)
            lk = read_lock(t["id"])
            if lk is not None:
                if lk.get("agent") == agent:
                    return t  # already ours: resume
                die(f"{tid} is claimed by {lk.get('agent')} (heartbeat {lk.get('heartbeat_at')})", 3)
            if t["status"] not in ("pending", "in-progress"):
                die(f"{tid} has status {t['status']}; not claimable", 3)
            cands = [t]
        else:
            cands = [t for t in q["targets"] if t["status"] == "pending"
                     and (tiers is None or t.get("tier") in tiers)
                     and (max_difficulty is None or t.get("difficulty", 3) <= max_difficulty)
                     and (dir_filter is None or dir_filter in t.get("ref_module", ""))
                     and t.get("ref_kind", "upstream") == "upstream"]
            cands.sort(key=sort_key)
        t = next((c for c in cands if read_lock(c["id"]) is None), None)
        if t is None:
            if freed:
                save_queue(q)
            return None
        TARGET_LOCKS.mkdir(parents=True, exist_ok=True)
        lk = {"target": t["id"], "agent": agent, "claimed_at": now(), "heartbeat_at": now(),
              "pid": os.getpid(), "host": socket.gethostname(), "file": (t.get("scaffold") or {}).get("file")}
        fd = os.open(lock_path(t["id"]), os.O_CREAT | os.O_EXCL | os.O_WRONLY)
        with os.fdopen(fd, "w") as fh:
            json.dump(lk, fh)
        t["status"] = "in-progress"
        t.setdefault("attempts", []).append({"started": now(), "agent": agent, "outcome": None, "notes": ""})
        save_queue(q)
        return t


def agent_name(args) -> str:
    return getattr(args, "agent", None) or os.environ.get("OP_AGENT") or f"agent-{os.getpid()}"


def cmd_next(args) -> int:
    agent = agent_name(args)
    t = claim(None, agent, set(args.tier.split(",")) if args.tier else None, args.max_difficulty, args.dir)
    if t is None:
        print("queue empty for these filters: run `./op refill`" if not args.json else json.dumps({"target": None}))
        return 3
    if args.json:
        print(json.dumps({"target": t, "lock": read_lock(t["id"]), "notes": read_notes(t["id"], 10)},
                         ensure_ascii=False))
        return 0
    print(f"CLAIMED {t['id']}  (tier {t['tier']}, difficulty {t.get('difficulty', '?')}, agent {agent})")
    print_brief(t)
    print(f"next: ./op scaffold '{t['id']}'   then ./op try <file>, ./op done '{t['id']}'")
    return 0


def print_brief(t: dict) -> None:
    print(f"  upstream: {t.get('ref_module')}  category: {t.get('upstream_category')}"
          f"  external formal proof: {t.get('upstream_formal_proof')}  time box: {t.get('timebox_minutes', 120)} min")
    if t.get("notes"):
        print(f"  queue notes: {t['notes']}")
    prev = read_notes(t["id"], 10)
    if prev:
        print("  previous attempts (ledger/notes; do not repeat dead ends):")
        for l in prev:
            print("    " + l)


def cmd_heartbeat(args) -> int:
    lk = read_lock(args.target)
    if lk is None:
        die(f"no claim on {args.target}")
    lk["heartbeat_at"] = now()
    lock_path(args.target).write_text(json.dumps(lk))
    print(f"heartbeat {args.target}")
    return 0


def cmd_release(args) -> int:
    with flock("queue", timeout=60):
        q = load_queue()
        t = find_target(q, args.target)
        if t.get("status") == "in-progress":
            t["status"] = "pending"
            if t.get("attempts") and t["attempts"][-1].get("outcome") is None:
                t["attempts"][-1].update({"finished": now(), "outcome": "released", "notes": args.reason or ""})
        lock_path(args.target).unlink(missing_ok=True)
        save_queue(q)
    if args.reason:
        add_note(args.target, f"released: {args.reason}")
    print(f"released {args.target}")
    return 0


ATTEMPTS = ROOT / "work" / "attempts"


def do_scaffold(tid: str, force: bool = False, fresh: bool = False) -> dict:
    q = load_queue()
    t = find_target(q, tid)
    if t.get("ref_kind", "upstream") != "upstream":
        die("scaffold handles upstream targets only; write variant statements by hand (AGENTS.md)")
    module, decl = t["ref_module"], t["ref_theorem"]
    if not olean_exists(module):
        print(f"op: building upstream module {module} (once)", flush=True)
        rc, _ = build([module])
        if rc != 0:
            die("upstream module does not build")
    u = upstream_decl(module, decl)
    path, our_mod = scaffold_paths(module, u["local_name"])
    saved = ATTEMPTS / f"{slug(tid)}.lean"
    action = "kept"
    if path.exists() and not force:
        action = "kept existing"
    elif saved.exists() and not fresh:
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(saved.read_text())
        action = f"restored previous attempt from {saved.relative_to(ROOT)}"
    else:
        ns = u["namespace"]
        opens = list(dict.fromkeys(u["opens"]))
        lines = [f"import {module}", "", "/-!", f"# `{decl}`", "",
                 f"Upstream: `{decl}` (category {u['category']}), "
                 f"`{u['path'].relative_to(UP)}` line {u['line']}.",
                 "Proof idea: (one paragraph; write it before finishing).", "-/", ""]
        lines += opens
        if ns:
            lines += [f"open {ns}", "", f"namespace OpenProofs.{ns}", ""]
        else:
            lines += ["", "namespace OpenProofs", ""]
        if u["variables"]:
            lines += u["variables"] + [""]
        lines += u["open_in"]
        stmt = u["statement"] if u["statement"].startswith((" ", "\n")) else " " + u["statement"]
        lines += [f"theorem {u['local_name']}{stmt} := by", "  sorry", "",
                  f"end OpenProofs.{ns}" if ns else "end OpenProofs", ""]
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text("\n".join(lines))
        action = "wrote fresh scaffold"
    ours = f"OpenProofs.{decl}"
    rel = str(path.relative_to(ROOT))
    with flock("queue", timeout=60):
        q = load_queue()
        tt = find_target(q, tid)
        tt["scaffold"] = {"file": rel, "module": our_mod, "theorem": ours}
        save_queue(q)
    lk = read_lock(tid)
    if lk is not None:
        lk["file"] = rel
        lk["heartbeat_at"] = now()
        lock_path(tid).write_text(json.dumps(lk))
    # Verify that the statement elaborates to exactly the upstream type (proof body ignored).
    TRYDIR.mkdir(parents=True, exist_ok=True)
    probe = TRYDIR / f"scaffold_{os.getpid()}.lean"
    probe.write_text(path.read_text() + f"\nexample : type_of% @{decl} := @{ours}\n")
    msgs, other, secs, to = run_lean(probe, CAPS["try_timeout"])
    probe.unlink(missing_ok=True)
    text_lines = path.read_text().splitlines()
    errs = [m for m in msgs if m["severity"] == "error"]
    # Statement problems: errors on the appended identity check, or inside the theorem header.
    hdr = next((i + 1 for i, l in enumerate(text_lines) if re.match(rf"^theorem\s+{re.escape(u['local_name'])}\b", l)), 0)
    body = next((i + 1 for i in range(max(hdr - 1, 0), len(text_lines)) if ":=" in text_lines[i]), hdr)
    bad = [m for m in errs if m["pos"]["line"] > len(text_lines) or hdr <= m["pos"]["line"] < body
           or (m["pos"]["line"] == body and m["pos"]["column"] < text_lines[body - 1].find(":="))]
    return {"target": t, "file": rel, "module": our_mod, "theorem": ours, "action": action, "upstream": u,
            "statement_errors": bad, "errors": errs, "seconds": secs, "timed_out": to}


def report_scaffold(r: dict) -> int:
    print(f"{r['action']}: {r['file']}  (module {r['module']}, theorem {r['theorem']})")
    u = r["upstream"]
    if r["statement_errors"] or r["timed_out"]:
        print(f"STATEMENT CHECK FAILED ({r['seconds']:.0f}s): the theorem does not elaborate to the upstream type")
        for l in format_msgs(r["errors"], r["file"])[:10]:
            print("  " + l[:800])
        if u["local_notation"]:
            print("  hint: upstream uses local notation; expand it by hand in the statement")
        print("  hint: copy any missing `open`/`variable` lines from the upstream file")
        return 1
    print(f"statement OK ({r['seconds']:.0f}s): elaborates to exactly `{r['target']['ref_theorem']}`'s type")
    other = [m for m in r["errors"]]
    if other:
        print(f"  the proof body currently has {len(other)} error(s); see ./op try {r['file']}")
    if u["formal_proof"]:
        print("  note: upstream already links an external formal proof for this statement")
    return 0


def cmd_scaffold(args) -> int:
    return report_scaffold(do_scaffold(args.target, args.force, args.fresh))


def touch_claims_for(src: Path) -> None:
    """`op try` doubles as a heartbeat for the claim whose scaffold file is being compiled."""
    if not TARGET_LOCKS.exists():
        return
    for lp in TARGET_LOCKS.glob("*.json"):
        try:
            lk = json.loads(lp.read_text())
        except (OSError, json.JSONDecodeError):
            continue
        if lk.get("file") and (ROOT / lk["file"]).resolve() == src.resolve():
            lk["heartbeat_at"] = now()
            lp.write_text(json.dumps(lk))


def cmd_try(args) -> int:
    import lint

    src = Path(args.file)
    if not src.is_absolute():
        src = (Path.cwd() / src).resolve()
    if not src.exists():
        die(f"no such file: {args.file}")
    if not args.no_build_deps:
        ensure_deps(src)
    touch_claims_for(src)
    target = goals_copy(src) if args.goals else src
    msgs, other, secs, timed_out = run_lean(target, args.timeout or CAPS["try_timeout"])
    rel = str(src.relative_to(ROOT)) if ROOT in src.parents else str(src)
    errs = [m for m in msgs if m["severity"] == "error"]
    warns = [m for m in msgs if m["severity"] == "warning"]
    sorry_w = [m for m in warns if "sorry" in m["data"]]
    if args.json:
        print(json.dumps({"file": rel, "seconds": round(secs, 1), "timed_out": timed_out,
                          "errors": len(errs), "warnings": len(warns), "messages": msgs, "stderr": other[-2000:]},
                         ensure_ascii=False))
    else:
        for l in format_msgs(msgs, rel):
            print(l if len(l) < 4000 else l[:4000] + " …")
        if other.strip():
            print(other[-2000:])
    findings = []
    if ROOT in src.parents and "OpenProofs" in src.parts:
        findings = lint.lint_file(src, lint.role_of(src, ROOT), ROOT)
    status = "TIMEOUT" if timed_out else ("FAIL" if errs else ("OK, but placeholders remain" if sorry_w else "OK"))
    if not args.json:
        print(f"== {status}: {len(errs)} error(s), {len(warns)} warning(s), {secs:.1f}s "
              f"(caps: -j{CAPS['threads']} -M{CAPS['memory_mb']}MB, timeout {args.timeout or CAPS['try_timeout']}s)")
        if findings:
            print(f"== lint: {len(findings)} finding(s) the checker will reject: "
                  + "; ".join(f"line {f.line}: {f.rule}" for f in findings[:8]))
    if args.goals:
        target.unlink(missing_ok=True)
    return 0 if not errs and not timed_out else 1


def build_index() -> None:
    import triage  # noqa: F401  (only for consistency of parsing helpers)

    INDEX.parent.mkdir(parents=True, exist_ok=True)
    decl_re = re.compile(r"^(?:@\[[^\]]*\]\s*)?(?:(?:private|protected|noncomputable|nonrec|partial|unsafe)\s+)*"
                         r"(theorem|lemma|def|abbrev|instance|structure|class|inductive|opaque)\s+([^\s:({\[]+)(.*)$")
    ns_re = re.compile(r"^(namespace|end|section)\b\s*(\S*)")
    roots = [(ROOT / ".lake" / "packages" / "mathlib" / "Mathlib", "Mathlib"),
             (UP / "FormalConjecturesForMathlib", "FCForMathlib"),
             (UP_SRC, "FormalConjectures"), (ROOT / "OpenProofs", "OpenProofs")]
    n = 0
    with open(INDEX, "w") as out:
        for base, tag in roots:
            for f in base.rglob("*.lean"):
                stack: list[tuple[str, str]] = []
                try:
                    lines = f.read_text(encoding="utf-8").splitlines()
                except (UnicodeDecodeError, OSError):
                    continue
                for i, line in enumerate(lines):
                    m = ns_re.match(line)
                    if m:
                        if m.group(1) in ("namespace", "section"):
                            stack.append((m.group(1), m.group(2)))
                        elif stack:
                            stack.pop()
                        continue
                    m = decl_re.match(line)
                    if not m:
                        continue
                    name = m.group(2)
                    ns = ".".join(a for k, a in stack if k == "namespace" and a)
                    full = name.removeprefix("_root_.") if name.startswith("_root_.") else (f"{ns}.{name}" if ns else name)
                    sig = (m.group(3) + " " + (lines[i + 1].strip() if i + 1 < len(lines) else "")).strip()
                    rel = f.relative_to(ROOT)
                    out.write(f"{full}\t{m.group(1)}\t{rel}:{i + 1}\t{sig[:240]}\n")
                    n += 1
    stamp = INDEX.with_suffix(".stamp")
    stamp.write_text(index_key())
    print(f"op: indexed {n} declarations", file=sys.stderr)


def index_key() -> str:
    man = (ROOT / "lake-manifest.json").read_text()
    lib = sorted((p.name, p.stat().st_mtime) for p in (ROOT / "OpenProofs").rglob("*.lean"))
    return hashlib.sha1((man + repr(lib)).encode()).hexdigest()


def cmd_search(args) -> int:
    if args.mode in ("name", "type"):
        stamp = INDEX.with_suffix(".stamp")
        if not INDEX.exists() or not stamp.exists() or stamp.read_text() != index_key():
            print("op: building the declaration index (one-off, ~30 s)", file=sys.stderr)
            build_index()
        rx = re.compile(args.pattern, re.I)
        hits = []
        with open(INDEX) as fh:
            for line in fh:
                name, kind, loc, sig = (line.rstrip("\n").split("\t") + ["", "", "", ""])[:4]
                hay = name if args.mode == "name" else sig
                if rx.search(hay):
                    hits.append((len(name), name, kind, loc, sig))
        hits.sort()
        for _, name, kind, loc, sig in hits[: args.limit]:
            print(f"{kind:<9} {name}  [{loc}]\n          {sig[:200]}")
        print(f"== {len(hits)} match(es){' (showing ' + str(args.limit) + ')' if len(hits) > args.limit else ''}")
        return 0
    # exact / apply / rw ... harness
    TRYDIR.mkdir(parents=True, exist_ok=True)
    imports = args.imports or ["Mathlib"]
    probe = TRYDIR / f"search_{os.getpid()}.lean"
    body = [f"import {m}" for m in imports] + [""]
    if args.open:
        body.append(f"open {args.open}")
    tactic = args.tactic or "exact?"
    body += [f"example {args.ctx or ''} : {args.pattern} := by", f"  {tactic}", ""]
    probe.write_text("\n".join(body))
    msgs, other, secs, to = run_lean(probe, args.timeout or CAPS["try_timeout"])
    sugg = [m["data"] for m in msgs if "Try this" in m["data"] or m["severity"] == "information"]
    errs = [m["data"] for m in msgs if m["severity"] == "error"]
    for s in sugg:
        print(s.strip())
    if not sugg:
        print("no suggestions" + (" (timeout)" if to else ""))
        for e in errs[:3]:
            print("  " + e.strip()[:600])
    print(f"== {tactic} on `{args.pattern}` ({secs:.0f}s)")
    probe.unlink(missing_ok=True)
    return 0 if sugg else 1


def ensure_claim(target_or_claim: str, args) -> str:
    claims = json.loads(CLAIMS.read_text())
    ids = {c["id"] for c in claims["claims"]}
    if target_or_claim in ids:
        return target_or_claim
    q = load_queue()
    t = find_target(q, target_or_claim)
    existing = next((c for c in claims["claims"] if c.get("ref_theorem") == t["ref_theorem"]
                     and c.get("ref_module") == t["ref_module"]), None)
    if existing:
        return existing["id"]
    sc = t.get("scaffold")
    if not sc and not (args.module and args.theorem):
        die("no scaffold recorded for this target; pass --module and --theorem")
    module = args.module or sc["module"]
    theorem = args.theorem or sc["theorem"]
    claim = {"id": t["id"], "module": module, "theorem": theorem, "ref_kind": t.get("ref_kind", "upstream"),
             "ref_module": t["ref_module"], "ref_theorem": t["ref_theorem"], "tier": t.get("tier", "a"),
             "assessment": args.assessment or "proved", "summary": args.summary or "",
             "notes": args.notes or ""}
    with flock("claims", timeout=60):
        claims = json.loads(CLAIMS.read_text())
        if claim["id"] not in {c["id"] for c in claims["claims"]}:
            claims["claims"].append(claim)
            CLAIMS.write_text(json.dumps(claims, indent=1, ensure_ascii=False) + "\n")
    print(f"op: added claim {claim['id']} ({module} → {t['ref_theorem']})")
    return claim["id"]


def cmd_check(args) -> int:
    cid = ensure_claim(args.target, args)
    print(f"op: waiting for the build lock, then running the full checker on {cid}", flush=True)
    with flock("build"):
        p = subprocess.run([sys.executable, "scripts/check.py", "--claim", cid, "--record"], cwd=ROOT,
                           env=lean_env(), capture_output=True, text=True, timeout=CAPS["build_timeout"])
    out = p.stdout + p.stderr
    print(out[-6000:])
    return p.returncode


def cmd_finish(args) -> int:
    import check

    with flock("queue", timeout=60):
        q = load_queue()
        t = find_target(q, args.target)
        claim = args.claim
        if args.outcome == "proved" or (args.outcome == "possible-misformalization" and claim):
            if not claim:
                claims = json.loads(CLAIMS.read_text())["claims"]
                c = next((c for c in claims if c["id"] == t["id"] or (
                    c.get("ref_theorem") == t["ref_theorem"] and c.get("ref_module") == t["ref_module"])), None)
                claim = c and c["id"]
            res = json.loads(RESULTS.read_text())["results"].get(claim or "") if RESULTS.exists() else None
            if not res or res["check"]["verdict"] != "PASS":
                die(f"refusing: no PASS verdict recorded for claim {claim!r}; run ./op check first", 3)
            if res["check"]["trusted_base_sha256"] != check.trusted_base_hash(check.ROOT):
                die("refusing: the recorded PASS predates a trusted-base change; re-run ./op check", 3)
        if not t.get("attempts") or t["attempts"][-1].get("outcome") is not None:
            t.setdefault("attempts", []).append({"started": None})
        t["attempts"][-1].update({"finished": now(), "outcome": args.outcome, "notes": args.notes, "claim": claim})
        t["status"] = "pending" if (args.outcome == "failed" and args.retry) else args.outcome
        lock_path(t["id"]).unlink(missing_ok=True)
        save_queue(q)
    add_note(t["id"], f"{args.outcome}: {args.notes}")
    print(f"{t['id']}: {t['status']}")
    return 0


def cmd_notes(args) -> int:
    if args.add:
        add_note(args.target, args.add, args.agent or "")
        print(f"noted ({notes_path(args.target).relative_to(ROOT)})")
        return 0
    p = notes_path(args.target)
    print(p.read_text() if p.exists() else f"(no notes yet for {args.target})")
    return 0


ANALYTIC = re.compile(r"atTop|Tendsto|=O\[|=o\[|~\[|=Θ\[|limsup|liminf|HasDensity|Density|∫|volume|deriv|"
                      r"Real\.log|Real\.exp|rexp|π|riemannZeta|MeasureTheory|∀ᶠ|∃ᶠ|𝓝|Measure|Hausdorff|dimH")
DEEP = re.compile(r"Cardinal|ℵ|Ordinal|Scheme|ModuleCat|CategoryTheory|NumberField|EllipticCurve|"
                  r"Manifold|Homotopy|Abelian\.Ext|IsRegularLocalRing|TuringMachine|Turing|VectorBundle|"
                  r"Sheaf|AlgebraicGeometry|HasFiniteCoproducts|Polynomial|PowerSeries|Matrix|LinearMap|"
                  r"Module\b|Ideal|Galois|Representation|ZFC|Computable|Halting|BB\b")


def difficulty(r: dict) -> int:
    """Rough 1-5 estimate from category and statement shape (no semantics; a sorting aid only)."""
    cat = r["category"]
    d = {"test": 1, "API": 1, "textbook": 2, "research solved": 3, "research open": 5}.get(cat, 4)
    s = r["statement"]
    if ANALYTIC.search(s):
        d += 1
    if DEEP.search(s) or DEEP.search(r.get("decl", "")):
        d += 1
    if len(s) > 300:
        d += 1
    return max(1, min(5, d))


def cmd_refill(args) -> int:
    import triage

    print("op: scanning upstream placeholders …", file=sys.stderr)
    erdos = triage.load_erdos_status(ROOT / "work" / "erdos-db" / "problems.yaml")
    recs = []
    for path in sorted(UP_SRC.rglob("*.lean")):
        rel = path.relative_to(UP)
        top = rel.parts[1]
        if args.dirs != "all" and top not in args.dirs.split(","):
            continue
        src = path.read_text(encoding="utf-8")
        answers = set(re.findall(r"^def\s+(\S+\.answer)\b[^\n]*:=\s*(?:by\s+)?sorry", src, re.M))
        for d in triage.parse_file(path):
            if not d["sorry"]:
                continue
            if any(a.split(".")[-2] in d["statement"] or a in d["statement"] for a in answers) and ".answer" in d["statement"]:
                continue  # value question with a placeholder answer: unprovable as stated
            d["file"] = str(rel)
            d["module"] = triage.module_name(path)
            d["dir"] = top
            if top == "ErdosProblems" and path.stem.isdigit():
                e = erdos.get(path.stem, {})
                d["erdos"] = f"{e.get('informal_status.state')}/{e.get('formal_status.state')}"
            recs.append(d)
    with flock("queue", timeout=120):
        q = load_queue()
        have = {t["id"] for t in q["targets"]}
        claimed = {c["ref_theorem"] for c in json.loads(CLAIMS.read_text())["claims"]}
        added = []
        for r in recs:
            if r["decl"] in have or r["decl"] in claimed:
                continue
            tier = "c" if r["category"] == "research open" else "a"
            diff = difficulty(r)
            # Within a difficulty, prefer statements without an external formal proof, then shorter ones.
            prio = 100 + diff * 10 + (5 if r["formal_proof"] else 0) + min(4, len(r["statement"]) // 80)
            added.append({"id": r["decl"], "tier": tier, "difficulty": diff, "priority": prio,
                          "ref_kind": "upstream", "ref_module": r["module"], "ref_theorem": r["decl"],
                          "dir": r["dir"], "upstream_category": r["category"],
                          "upstream_formal_proof": r["formal_proof"], "erdos_status": r.get("erdos"),
                          "status": "pending", "timebox_minutes": 60 * min(diff, 4), "notes": "",
                          "attempts": []})
        by: dict[str, int] = {}
        for t in added:
            k = f"{t['dir']}/tier {t['tier']}/d{t['difficulty']}"
            by[k] = by.get(k, 0) + 1
        if not args.dry_run:
            q["targets"].extend(added)
            q["targets"].sort(key=sort_key)
            save_queue(q)
    print(f"{'would add' if args.dry_run else 'added'} {len(added)} target(s)")
    tops: dict[str, int] = {}
    for t in added:
        tops[t["dir"]] = tops.get(t["dir"], 0) + 1
    for k, v in sorted(tops.items(), key=lambda kv: -kv[1]):
        print(f"  {k}: {v}")
    return 0


def cmd_build(args) -> int:
    rc, out = build(args.modules)
    print(out[-3000:] if out else "ok")
    return rc


def cmd_commit(args) -> int:
    claims = json.loads(CLAIMS.read_text())["claims"]
    res = json.loads(RESULTS.read_text())["results"] if RESULTS.exists() else {}
    import lint

    files = []
    for c in claims:
        r = res.get(c["id"])
        if r and r["check"]["verdict"] == "PASS":
            for p in lint.source_closure(ROOT, c["module"]):
                if p.exists():
                    files.append(str(p.relative_to(ROOT)))
            if c.get("ref_kind") == "variant":
                files.append(str(lint.module_path(ROOT, c["ref_module"]).relative_to(ROOT)))
    paths = ["ledger", "claims.json", "outbox", "docs"] + sorted(set(files))
    with flock("git", timeout=120):
        subprocess.run(["git", "add", "--", *[p for p in paths if (ROOT / p).exists()]], cwd=ROOT, check=True)
        st = subprocess.run(["git", "diff", "--cached", "--quiet"], cwd=ROOT)
        if st.returncode == 0:
            print("nothing to commit")
            return 0
        msg = args.message + ("\n\n" + args.trailer if args.trailer else "")
        p = subprocess.run(["git", "commit", "-q", "-m", msg], cwd=ROOT)
    if p.returncode == 0:
        print(subprocess.run(["git", "log", "--oneline", "-1"], cwd=ROOT, capture_output=True, text=True).stdout.strip())
    return p.returncode


# ----------------------------------------------------------------------------- portable loop


CONFIG = ROOT / "op.config.json"


def config() -> dict:
    """Effective configuration: op.config.json overridden by OP_* environment variables."""
    c = json.loads(CONFIG.read_text()) if CONFIG.exists() else {}
    env_map = {"OP_PROVERS": ("provers", int), "OP_PROVER_CLI": ("prover_cli", str),
               "OP_PROVER_MODEL": ("prover_model", str), "OP_MAX_TURNS": ("max_turns", int),
               "OP_BUDGET": ("budget_targets", int), "OP_WORKER_TIMEOUT_MINUTES": ("worker_timeout_minutes", int)}
    for var, (key, typ) in env_map.items():
        if os.environ.get(var):
            c[key] = typ(os.environ[var])
    return c


def cmd_config(args) -> int:
    c = config()
    if args.get:
        v = c.get(args.get, "")
        print(v if not isinstance(v, (dict, list)) else json.dumps(v))
        return 0
    print(json.dumps({k: v for k, v in c.items() if not k.startswith("_")}, indent=1))
    return 0


def current_branch() -> str:
    head = (ROOT / ".git" / "HEAD").read_text().strip()
    return head.split("refs/heads/")[-1] if head.startswith("ref:") else head[:12]


def cmd_branch(args) -> int:
    b = current_branch()
    if b in ("main", "master") or args.new:
        name = args.new or f"task/loop-{dt.date.today().isoformat()}"
        with flock("git", timeout=120):
            exists = subprocess.run(["git", "rev-parse", "--verify", "--quiet", f"refs/heads/{name}"], cwd=ROOT,
                                    capture_output=True).returncode == 0
            cmd = ["git", "switch", name] if exists else ["git", "switch", "-c", name]
            r = subprocess.run(cmd, cwd=ROOT, capture_output=True, text=True)
        if r.returncode != 0:
            die(f"could not switch to {name}: {r.stderr.strip()}")
        b = name
    print(f"on branch {b}")
    return 0


def stop_requested() -> bool:
    return (ROOT / "work" / "STOP").exists()


def cmd_stop(args) -> int:
    p = ROOT / "work" / "STOP"
    if args.clear:
        p.unlink(missing_ok=True)
        print("stop flag cleared")
    else:
        p.parent.mkdir(parents=True, exist_ok=True)
        p.write_text(now() + "\n")
        print("stop requested: loops finish their current target and exit (./op stop --clear to undo)")
    return 0


def cmd_begin(args) -> int:
    if stop_requested() and not args.target:
        print("STOP requested (work/STOP): not claiming new work. ./op stop --clear to resume.")
        return 4
    agent = agent_name(args)
    t = claim(args.target, agent, set(args.tier.split(",")) if args.tier else None, args.max_difficulty, args.dir)
    if t is None:
        print("QUEUE EMPTY: nothing to claim. Run ./op refill, or stop.")
        return 3
    print(f"== WORK ORDER for agent {agent}")
    print(f"TARGET  {t['id']}  (tier {t['tier']}, difficulty {t.get('difficulty', '?')})")
    print_brief(t)
    r = do_scaffold(t["id"], fresh=args.fresh)
    rc = report_scaffold(r)
    u = r["upstream"]
    print(f"UPSTREAM FILE  {u['path'].relative_to(ROOT)}  (read the docstring above line {u['line']})")
    print(f"EDIT    {r['file']}   (replace the placeholder after `:= by` with a proof)")
    print("LOOP    ./op try " + r["file"] + " --goals      # until it prints `== OK:` with 0 errors")
    print("SEARCH  ./op search name <regex> | ./op search exact '<goal>' --ctx '<binders>'")
    print(f"FINISH  ./op done '{t['id']}'        # full checker; on PASS it records and commits")
    print(f"GIVE UP ./op giveup '{t['id']}' --notes 'what you tried, dead ends, next idea'")
    if rc != 0:
        print("FIRST   fix the statement problem above (opens/variables/notation) before proving")
    return rc


def cmd_done(args) -> int:
    q = load_queue()
    t = find_target(q, args.target)
    cid = ensure_claim(args.target, args)
    print(f"op: running the full checker on {cid} (waits for the build lock)", flush=True)
    with flock("build"):
        p = subprocess.run([sys.executable, "scripts/check.py", "--claim", cid, "--record"], cwd=ROOT,
                           env=lean_env(), capture_output=True, text=True, timeout=CAPS["build_timeout"])
    out = p.stdout + p.stderr
    if p.returncode != 0:
        print(out[-5000:])
        print(f"== FAIL: the checker rejected {cid}. Fix the reported layer and run ./op done again "
              f"(or ./op giveup '{t['id']}' --notes ...).")
        add_note(t["id"], f"checker FAIL: {out.strip().splitlines()[0][:300] if out.strip() else ''}")
        return 1
    print(out.strip().splitlines()[0] if out.strip() else "PASS")
    outcome = "possible-misformalization" if args.assessment == "possible-misformalization" else "proved"
    fin = argparse.Namespace(target=args.target, outcome=outcome,
                             notes=args.notes or "proved; checker PASS", claim=cid, retry=False)
    cmd_finish(fin)
    if not args.no_commit:
        cmd_commit(argparse.Namespace(message=f"Prove {t['id']} (checker PASS)", trailer=None))
    print(f"== DONE: {t['id']} PASS, recorded" + ("" if args.no_commit else " and committed"))
    return 0


def cmd_giveup(args) -> int:
    q = load_queue()
    t = find_target(q, args.target)
    sc = t.get("scaffold") or {}
    if sc.get("file") and (ROOT / sc["file"]).exists():
        ATTEMPTS.mkdir(parents=True, exist_ok=True)
        saved = ATTEMPTS / f"{slug(t['id'])}.lean"
        (ROOT / sc["file"]).replace(saved)
        args.notes += f" [work saved to {saved.relative_to(ROOT)}; ./op begin restores it]"
    failures = sum(1 for a in t.get("attempts", []) if a.get("outcome") == "failed")
    retry = args.outcome == "failed" and failures < 1
    fin = argparse.Namespace(target=args.target, outcome=args.outcome, notes=args.notes, claim=None, retry=retry)
    cmd_finish(fin)
    if retry:
        with flock("queue", timeout=60):
            q = load_queue()
            tt = find_target(q, args.target)
            tt["priority"] = tt.get("priority", 100) + 50
            save_queue(q)
    if not args.no_commit:
        cmd_commit(argparse.Namespace(message=f"Attempt log: {t['id']} ({args.outcome})", trailer=None))
    return 0


def fill(template: list, values: dict) -> list:
    out = []
    for part in template:
        if part == "{model_flag}":
            out += values["model_flag"]
        else:
            out.append(part.format(**values))
    return [x for x in out if x != ""]


PROVER_PROMPT = (
    "You are a prover for the open-proofs project in this directory. Read AGENTS.md, section "
    "'Prover procedure', and follow it exactly for ONE target: {target} (already claimed for agent "
    "{agent}; start with `./op begin --target '{target}' --agent {agent}`). Finish with `./op done` "
    "(on PASS) or `./op giveup` (with notes) and then stop. Never edit the checker or anything outside "
    "your result file, OpenProofs/Lib, ledger notes and outbox drafts. Do not push or post anything."
)


def cmd_swarm(args) -> int:
    """Run N headless prover workers of a configurable agent CLI until budget/queue/STOP."""
    c = config()
    n = args.provers or c.get("provers", 3)
    cli = args.cli or c.get("prover_cli", "claude")
    model = args.model if args.model is not None else c.get("prover_model", "")
    budget = args.budget if args.budget is not None else c.get("budget_targets", 0)
    max_turns = c.get("max_turns", 120)
    timeout = 60 * c.get("worker_timeout_minutes", 120)
    tmpl = c["cli"][cli]
    mflag = [x.format(model=model) for x in c["model_flag"][cli]] if model else []
    logdir = ROOT / "work" / "swarm"
    logdir.mkdir(parents=True, exist_ok=True)
    running: dict = {}
    started = 0
    print(f"swarm: {n} worker(s), cli={cli}, model={model or '(CLI default)'}, budget={budget or 'unlimited'}")
    while True:
        for k in list(running):
            proc, tid, t0, fh = running[k]
            if proc.poll() is None and time.time() - t0 < timeout:
                continue
            if proc.poll() is None:
                proc.kill()
            fh.close()
            del running[k]
            q = load_queue()
            t = find_target(q, tid)
            if t["status"] == "in-progress":
                cmd_giveup(argparse.Namespace(target=tid, outcome="failed", no_commit=False,
                                              notes=f"worker {k} exited (code {proc.returncode}) without finishing"))
            print(f"swarm: worker {k} finished {tid}: {find_target(load_queue(), tid)['status']}", flush=True)
        can_start = not stop_requested() and (not budget or started < budget)
        while can_start and len(running) < n:
            slot = next(i for i in range(n) if f"w{i}" not in running)
            agent = f"swarm-w{slot}"
            t = claim(None, agent)
            if t is None:
                can_start = False
                break
            prompt = PROVER_PROMPT.format(target=t["id"], agent=agent)
            cmd = fill(tmpl, {"prompt": prompt, "max_turns": max_turns, "model_flag": mflag, "root": str(ROOT)})
            if args.dry_run:
                print("would run:", " ".join(cmd[:3]), "…")
                cmd_release(argparse.Namespace(target=t["id"], reason="swarm dry run"))
                return 0
            fh = open(logdir / f"{agent}-{slug(t['id'])}.log", "w")
            env = lean_env()
            env["OP_AGENT"] = agent
            proc = subprocess.Popen(cmd, cwd=ROOT, env=env, stdout=fh, stderr=subprocess.STDOUT)
            running[f"w{slot}"] = (proc, t["id"], time.time(), fh)
            started += 1
            print(f"swarm: worker w{slot} started on {t['id']} (pid {proc.pid})", flush=True)
            can_start = not budget or started < budget
        if not running:
            break
        time.sleep(10)
    print(f"swarm: done ({started} target(s) attempted)")
    return 0


def cmd_preflight(args) -> int:
    cmd = [sys.executable, "scripts/loop.py", "preflight"] + (["--full"] if args.full else [])
    with flock("build"):
        return subprocess.call(cmd, cwd=ROOT, env=lean_env())


def cmd_recheck(_args) -> int:
    with flock("build"):
        return subprocess.call([sys.executable, "scripts/check.py", "--all", "--record"], cwd=ROOT, env=lean_env())


def main() -> int:
    ap = argparse.ArgumentParser(prog="op", description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    sub = ap.add_subparsers(dest="cmd", required=True)
    p = sub.add_parser("status"); p.add_argument("--brief", action="store_true")
    p = sub.add_parser("next"); p.add_argument("--agent"); p.add_argument("--tier")
    p.add_argument("--max-difficulty", type=int); p.add_argument("--dir"); p.add_argument("--json", action="store_true")
    p = sub.add_parser("heartbeat"); p.add_argument("target")
    p = sub.add_parser("release"); p.add_argument("target"); p.add_argument("--reason")
    p = sub.add_parser("scaffold"); p.add_argument("target"); p.add_argument("--force", action="store_true")
    p.add_argument("--fresh", action="store_true")
    p = sub.add_parser("begin"); p.add_argument("--target"); p.add_argument("--agent"); p.add_argument("--tier")
    p.add_argument("--max-difficulty", type=int); p.add_argument("--dir"); p.add_argument("--fresh", action="store_true")
    p = sub.add_parser("done"); p.add_argument("target"); p.add_argument("--notes"); p.add_argument("--assessment")
    p.add_argument("--summary"); p.add_argument("--module"); p.add_argument("--theorem")
    p.add_argument("--no-commit", action="store_true")
    p = sub.add_parser("giveup"); p.add_argument("target"); p.add_argument("--notes", required=True)
    p.add_argument("--outcome", default="failed", choices=["failed", "blocked", "skipped", "possible-misformalization"])
    p.add_argument("--no-commit", action="store_true")
    p = sub.add_parser("branch"); p.add_argument("--new")
    p = sub.add_parser("config"); p.add_argument("--get")
    p = sub.add_parser("stop"); p.add_argument("--clear", action="store_true")
    p = sub.add_parser("swarm"); p.add_argument("--provers", type=int); p.add_argument("--cli")
    p.add_argument("--model"); p.add_argument("--budget", type=int); p.add_argument("--dry-run", action="store_true")
    p = sub.add_parser("try"); p.add_argument("file"); p.add_argument("--goals", action="store_true")
    p.add_argument("--timeout", type=int); p.add_argument("--json", action="store_true")
    p.add_argument("--no-build-deps", action="store_true")
    p = sub.add_parser("search"); p.add_argument("mode", choices=["name", "type", "exact"])
    p.add_argument("pattern"); p.add_argument("--limit", type=int, default=25); p.add_argument("--ctx")
    p.add_argument("--import", dest="imports", action="append"); p.add_argument("--open")
    p.add_argument("--tactic"); p.add_argument("--timeout", type=int)
    p = sub.add_parser("check"); p.add_argument("target"); p.add_argument("--assessment")
    p.add_argument("--summary"); p.add_argument("--notes"); p.add_argument("--module"); p.add_argument("--theorem")
    p = sub.add_parser("finish"); p.add_argument("target"); p.add_argument("--outcome", required=True, choices=OUTCOMES)
    p.add_argument("--notes", required=True); p.add_argument("--claim"); p.add_argument("--retry", action="store_true")
    p = sub.add_parser("notes"); p.add_argument("target"); p.add_argument("--add"); p.add_argument("--agent")
    p = sub.add_parser("refill"); p.add_argument("--dirs", default="all"); p.add_argument("--dry-run", action="store_true")
    p = sub.add_parser("build"); p.add_argument("modules", nargs="+")
    p = sub.add_parser("commit"); p.add_argument("-m", "--message", required=True); p.add_argument("--trailer")
    p = sub.add_parser("preflight"); p.add_argument("--full", action="store_true")
    sub.add_parser("recheck")
    args = ap.parse_args()
    fn = {"status": cmd_status, "next": cmd_next, "heartbeat": cmd_heartbeat, "release": cmd_release,
          "scaffold": cmd_scaffold, "try": cmd_try, "search": cmd_search, "check": cmd_check,
          "finish": cmd_finish, "notes": cmd_notes, "refill": cmd_refill, "build": cmd_build,
          "commit": cmd_commit, "preflight": cmd_preflight, "recheck": cmd_recheck, "begin": cmd_begin,
          "done": cmd_done, "giveup": cmd_giveup, "branch": cmd_branch, "config": cmd_config,
          "stop": cmd_stop, "swarm": cmd_swarm}[args.cmd]
    return fn(args)


if __name__ == "__main__":
    sys.exit(main())
