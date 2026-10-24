# Attempt log: `OpenQuantumProblem23.hasSICPOVM_three`

Append-only. Record what was tried, dead ends, and the next idea, so later sessions do not repeat them.

- 2026-10-24T05:27:12Z [swarm-w2] checker FAIL: FAIL  OpenQuantumProblem23.hasSICPOVM_three  axioms=['propext', 'Classical.choice', 'Quot.sound']  identity=syntactic  failed=['opcheck']
- 2026-10-24T05:28:12Z [swarm-w2] proved: proved; checker PASS
- 2026-10-24T05:28:19Z [swarm-w2] PASS (swarm-w2). Tooling finding: the first attempt used `simp [hesseFamily]` on concrete indices; the checker rejected it (candidate_decls) because Lean realized `hesseFamily.match_1.splitter` in our module, outside `OpenProofs.`. Workaround: `rfl` lemmas `hesseFamily k = vec3 ...` for k = 0..8 and simp with those. Proposed checker fix (needs owner approval): exempt realized `match_N.splitter`/`match_N.eq_N` of trusted definitions, the same way `f.eq_N` is exempted. Useful for the hesseFamily_pairwise and qubitSICFamily targets.
