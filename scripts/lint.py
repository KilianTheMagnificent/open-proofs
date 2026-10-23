#!/usr/bin/env python3
"""Source-level lint for open-proofs Lean files (one layer of the checker).

Two roles:
  * result    -- files under OpenProofs/ except OpenProofs/Statements/: proofs.
  * statement -- files under OpenProofs/Statements/: self-recorded variant statements.

The lint is defence in depth. The Lean-level checker (opcheck) and kernel replay are the
authoritative layers; every cheat the lint bans is also caught there (see tests/adversarial).

Robustness: the lint scans comment- and string-stripped code for every rule, and also scans
the *raw* text for a critical subset, so a mis-parsed comment or string cannot hide those
tokens. The cost is that result files may not mention these words even in comments.
"""

from __future__ import annotations

import re
from dataclasses import dataclass
from pathlib import Path

# Banned anywhere in code (comments/strings stripped). Word-boundary regexes.
RESULT_CODE_RULES: list[tuple[str, str]] = [
    (r"\bsorry\b", "sorry"),
    (r"\badmit\b", "admit"),
    (r"\bstop\b", "stop tactic (admits goals)"),
    (r"\baxiom\b", "axiom declaration"),
    (r"\bopaque\b", "opaque declaration"),
    (r"\bunsafe\b", "unsafe"),
    (r"\bpartial\b", "partial def"),
    (r"\bimplemented_by\b", "implemented_by"),
    (r"\bextern\b", "extern"),
    (r"\bexport\b", "export"),
    (r"\bcsimp\b", "csimp"),
    (r"@\[\s*init\b", "init attribute"),
    (r"\bnative_decide\b", "native_decide"),
    (r"\+\s*native\b", "decide +native"),
    (r"\bofReduceBool\b|\breduceBool\b|\btrustCompiler\b", "native-evaluation axiom"),
    (r"\bmacro\b|\bmacro_rules\b", "macro"),
    (r"\bsyntax\b|\bdeclare_syntax_cat\b", "syntax extension"),
    (r"\belab\b|\belab_rules\b", "elaborator extension"),
    (r"\bnotation\b|\binfixl?\b|\binfixr\b|\bprefix\b|\bpostfix\b", "notation"),
    (r"\brun_cmd\b|\brun_elab\b|\brun_meta\b|\brun_tac\b", "meta-code execution"),
    (r"#eval\b|#exit\b|#guard_msgs\b", "#eval/#exit"),
    (r"\binitialize\b|\bbuiltin_initialize\b", "initialize"),
    (r"\bdebug\.", "debug option"),
    (r"\bskipKernelTC\b", "skipKernelTC"),
    (r"\bset_option\s+trust", "trust option"),
    (r"\baddDecl\w*\b|\bmodifyEnv\b|\bsetEnv\b|\bEnvironment\b", "environment manipulation"),
    (r"\bLean\.(Elab|Meta|Kernel|Compiler|Parser|PrettyPrinter)\b", "metaprogramming API"),
    (r"^\s*meta\b|\bmeta\s+(def|section|import)\b", "meta code"),
    (r"^\s*module\b", "module-system header (result files are plain files)"),
]

# Banned even in comments and strings: never needed in prose, and checking the raw text
# makes stripping bugs irrelevant for them.
RAW_RULES: list[tuple[str, str]] = [
    (r"\bsorry\b", "sorry (raw text)"),
    (r"\badmit\b", "admit (raw text)"),
    (r"\bnative_decide\b", "native_decide (raw text)"),
    (r"\bimplemented_by\b", "implemented_by (raw text)"),
    (r"\bskipKernelTC\b", "skipKernelTC (raw text)"),
    (r"\bofReduceBool\b|\btrustCompiler\b", "native-evaluation axiom (raw text)"),
    (r"\brun_cmd\b|\brun_tac\b|\brun_elab\b|\brun_meta\b", "meta-code execution (raw text)"),
    (r"#eval\b", "#eval (raw text)"),
    (r"\baddDecl\w*\b", "addDecl (raw text)"),
]

RESULT_IMPORT_ALLOW = re.compile(
    r"^(Mathlib|Batteries|Aesop|Plausible|FormalConjectures|FormalConjecturesUtil|"
    r"FormalConjecturesForMathlib)(\.|$)|^OpenProofs\.(Results|Lib)\."
)
STATEMENT_IMPORT_ALLOW = re.compile(
    r"^(Mathlib|FormalConjectures|FormalConjecturesUtil|FormalConjecturesForMathlib)(\.|$)"
)
MODULE_COMPONENT = re.compile(r"^[A-Za-z_][A-Za-z0-9_]*$")

STATEMENT_FORBIDDEN_DECL = re.compile(
    r"^\s*(?:@\[[^\]]*\]\s*)?(?:(?:private|protected|noncomputable|nonrec)\s+)*"
    r"(def|abbrev|instance|structure|class|inductive|opaque|axiom|example|lemma|notation|"
    r"local|scoped|attribute|macro|syntax|elab|macro_rules|elab_rules|set_option|"
    r"variable|universe|mutual|deriving|initialize|run_cmd|#eval)\b",
    re.MULTILINE,
)


@dataclass
class Finding:
    file: str
    line: int
    rule: str
    snippet: str

    def to_json(self) -> dict:
        return {"file": self.file, "line": self.line, "rule": self.rule, "snippet": self.snippet}


def strip_comments_and_strings(src: str) -> str:
    """Replace comments, string literals and char literals by spaces (newlines kept)."""
    out = []
    i, n = 0, len(src)
    depth = 0
    while i < n:
        c = src[i]
        if depth > 0:
            if src.startswith("/-", i):
                depth += 1
                out.append("  ")
                i += 2
            elif src.startswith("-/", i):
                depth -= 1
                out.append("  ")
                i += 2
            else:
                out.append("\n" if c == "\n" else " ")
                i += 1
            continue
        if src.startswith("/-", i):
            depth = 1
            out.append("  ")
            i += 2
            continue
        if src.startswith("--", i):
            j = src.find("\n", i)
            j = n if j == -1 else j
            out.append(" " * (j - i))
            i = j
            continue
        if c == "'" and (i == 0 or not (src[i - 1].isalnum() or src[i - 1] in "_'.!?")):
            m = re.match(r"'(\\.|[^\\'\n])'", src[i:])
            if m:
                out.append(" " * len(m.group(0)))
                i += len(m.group(0))
                continue
        if c == '"':
            j = i + 1
            while j < n and src[j] != '"':
                j += 2 if src[j] == "\\" else 1
            j = min(j + 1, n)
            out.append("".join("\n" if ch == "\n" else " " for ch in src[i:j]))
            i = j
            continue
        out.append(c)
        i += 1
    return "".join(out)


def _line_of(text: str, pos: int) -> int:
    return text.count("\n", 0, pos) + 1


def imports_of(src: str) -> list[str]:
    code = strip_comments_and_strings(src)
    return re.findall(r"^\s*import\s+(\S+)", code, re.MULTILINE)


def module_path(root: Path, module: str) -> Path:
    parts = [p.strip("«»") for p in module.split(".")]
    return root.joinpath(*parts).with_suffix(".lean")


def lint_file(path: Path, role: str, root: Path) -> list[Finding]:
    src = path.read_text(encoding="utf-8")
    rel = str(path.relative_to(root)) if path.is_relative_to(root) else str(path)
    code = strip_comments_and_strings(src)
    lines = src.splitlines()
    findings: list[Finding] = []

    def add(pos: int, rule: str, text: str) -> None:
        ln = _line_of(text, pos)
        findings.append(Finding(rel, ln, rule, lines[ln - 1].strip()[:160] if ln <= len(lines) else ""))

    mod_rel = path.relative_to(root / "OpenProofs") if (root / "OpenProofs") in path.parents else None
    if mod_rel is not None:
        for comp in mod_rel.with_suffix("").parts:
            if not MODULE_COMPONENT.match(comp):
                findings.append(Finding(rel, 1, f"module path component {comp!r} is not a plain identifier", ""))

    for imp in imports_of(src):
        allow = RESULT_IMPORT_ALLOW if role == "result" else STATEMENT_IMPORT_ALLOW
        if not allow.search(imp.replace("«", "").replace("»", "")):
            m = re.search(r"^\s*import\s+" + re.escape(imp), code, re.MULTILINE)
            add(m.start() if m else 0, f"import not allowed for {role} files: {imp}", code)

    if role == "result":
        for rx, rule in RESULT_CODE_RULES:
            for m in re.finditer(rx, code, re.MULTILINE):
                add(m.start(), rule, code)
        for rx, rule in RAW_RULES:
            for m in re.finditer(rx, src, re.MULTILINE):
                add(m.start(), rule, src)
    elif role == "statement":
        for m in STATEMENT_FORBIDDEN_DECL.finditer(code):
            add(m.start(), f"statement files may only contain theorem statements ({m.group(1)})", code)
        for rx, rule in RESULT_CODE_RULES:
            if rule in ("sorry", "stop tactic (admits goals)"):
                continue
            for m in re.finditer(rx, code, re.MULTILINE):
                add(m.start(), rule, code)
        thms = list(re.finditer(r"\btheorem\b", code))
        # Every theorem body must be exactly `sorry`: split at each `theorem` keyword.
        starts = [m.start() for m in thms] + [len(code)]
        for a, b in zip(starts, starts[1:]):
            chunk = code[a:b]
            ms = list(re.finditer(r":=\s*(?:by\s+)?sorry\b", chunk))
            rest = chunk[ms[-1].end():] if ms else None
            if rest is not None:
                rest = re.sub(r"\b(end|namespace)\b[ \t]*[^\s]*|\bsection\b[ \t]*[^\s]*|"
                              r"\bopen\b[^\n]*|@\[[^\]]*\]", " ", rest)
            if rest is None or rest.strip():
                add(a, "statement theorem body must be exactly `sorry`", code)
    else:
        raise ValueError(role)
    return findings


def role_of(path: Path, root: Path) -> str:
    return "statement" if (root / "OpenProofs" / "Statements") in path.parents else "result"


def source_closure(root: Path, module: str) -> list[Path]:
    """Source files of OpenProofs.* modules reachable from `module` through import lines."""
    seen: dict[str, Path] = {}
    todo = [module]
    while todo:
        m = todo.pop()
        if m in seen:
            continue
        p = module_path(root, m)
        if not p.exists():
            seen[m] = p
            continue
        seen[m] = p
        for imp in imports_of(p.read_text(encoding="utf-8")):
            if imp.startswith("OpenProofs."):
                todo.append(imp)
    return list(seen.values())
