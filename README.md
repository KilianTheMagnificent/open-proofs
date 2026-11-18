# open-proofs

Machine-checked Lean 4 proofs of statements from
[google-deepmind/formal-conjectures](https://github.com/google-deepmind/formal-conjectures)
that upstream still leaves as `sorry`.

AI agents (Claude Code and Codex) write the proofs. A strict checker and the Lean kernel review
them. No human reads them. Trust the checker, not the authors.

## Status

142 results pass the checker:

- **131 proved targets.** Most are textbook results, test statements and solved research
  problems that had no Lean proof upstream. Examples: Hadwiger–Nelson χ(ℝ²) ≤ 7, Wolstenholme's
  theorem, R(3,5) = 14, Erdős 902's lower bound and Kaplansky's Promislow-group example.
- **11 misformalization certificates.** Each proves that a published value question is false
  for every value of its `answer` placeholder, because the answer ignores a parameter the
  theorem quantifies over. See [`outbox/`](outbox/) for the write-ups
  ([`outbox/issue-value-answers-ignore-parameter.md`](outbox/issue-value-answers-ignore-parameter.md)
  was filed upstream as [`google-deepmind/formal-conjectures#7590`](https://github.com/google-deepmind/formal-conjectures/issues/7590)).

No open problem has been solved here. [`ledger/LEDGER.md`](ledger/LEDGER.md) lists every result
with its checker verdict.

## How results are checked

`scripts/check.py` passes a claim only if all five layers pass:

1. **Integrity.** The upstream pin, toolchain and dependency checkouts match the manifest, and the
   lakefile has no options that weaken checking.
2. **Lint.** No `sorry`, `admit`, `native_decide`, `axiom`, `opaque`, `implemented_by`, `extern`,
   metaprogramming, notation or `debug.*` options. Imports come from an allowlist.
3. **Clean build** of the result's modules.
4. **opcheck.** The proved statement must be the pinned upstream statement as an elaborated term
   (or the kernel must accept the proof at the upstream type). Axioms are collected by walking
   every proof body; only `propext`, `Classical.choice` and `Quot.sound` are allowed. No upstream
   definition may be redefined or shadowed.
5. **leanchecker.** An independent kernel re-check.

`tests/run_adversarial.py` tries known ways to cheat (48 cases) and confirms that the checker
rejects each one.

## Reproduce

Requirements: [elan](https://github.com/leanprover/elan) and Python 3.

```bash
git clone https://github.com/KilianTheMagnificent/open-proofs.git && cd open-proofs
lake exe cache get
lake build
python3 scripts/check.py --all       # re-check every claim
python3 tests/run_adversarial.py     # checker self-tests
```

Pins: Lean v4.33.1, formal-conjectures `96343eeb5990ff13735e728cd0195eff0156a3bb`
(see `upstream.json` and `lake-manifest.json`).

## Running the agents

Open an agent CLI in this directory and say `startup`. [`AGENTS.md`](AGENTS.md) defines the loop
for any model or CLI. `./op swarm --provers N` runs unattended workers. Results land in
`OpenProofs/Results/` only after the checker passes them.

## License

Apache-2.0, the same as formal-conjectures and Mathlib.
