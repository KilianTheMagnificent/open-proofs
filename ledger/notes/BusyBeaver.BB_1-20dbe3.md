# Attempt log: `BusyBeaver.BB_1`

Append-only. Record what was tried, dead ends, and the next idea, so later sessions do not repeat them.

- 2026-10-24T08:04:22Z [swarm-w2] checker FAIL: FAIL  BusyBeaver.BB_1  axioms=['propext', 'Classical.choice', 'Quot.sound']  identity=syntactic  failed=['opcheck']
- 2026-10-24T08:04:47Z [swarm-w2] checker FAIL: FAIL  BusyBeaver.BB_1  axioms=['propext', 'Classical.choice', 'Quot.sound']  identity=syntactic  failed=['opcheck']
- 2026-10-24T08:05:08Z [swarm-w2] checker FAIL: FAIL  BusyBeaver.BB_1  axioms=['propext', 'Classical.choice', 'Quot.sound']  identity=syntactic  failed=['opcheck']
- 2026-10-24T08:06:00Z [swarm-w2] proved: proved; checker PASS
- 2026-10-24T08:06:10Z [swarm-w2] PASS (swarm-w2). Pitfall for other BusyBeaver targets: `simp [Machine.step, ...]` realizes a private `Turing.BusyBeaver.Machine.step.match_5.splitter` in the result module, which opcheck candidate_decls rejects ("declared outside the OpenProofs namespace"). Compute steps with `show (M q h).map _ = _; rw [hq]; rfl` instead.
