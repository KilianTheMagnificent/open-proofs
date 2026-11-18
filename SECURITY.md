# Security Policy

## Reporting a Vulnerability or Checker Bypass

If you discover a security vulnerability in the tooling (`scripts/check.py`, `scripts/lint.py`, `OpenProofsChecker/Main.lean`) or a way to bypass the five-layer checker with an unsound or tampered Lean 4 proof, please report it privately via GitHub's [Private Vulnerability Reporting](https://github.com/KilianTheMagnificent/open-proofs/security/advisories/new) rather than opening a public issue.

Confirmed checker bypasses are added as regression cases to `tests/run_adversarial.py`.
