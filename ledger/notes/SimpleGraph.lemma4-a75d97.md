# Attempt log: `SimpleGraph.lemma4`

Append-only. Record what was tried, dead ends, and the next idea, so later sessions do not repeat them.

- 2026-10-24T07:50:41Z [swarm-w1] proved: proved; checker PASS
- 2026-10-24T07:50:51Z [swarm-w1] PASS (swarm-w1, 2026-10-24). Tooling: the scaffold dropped upstream's 'open scoped Classical in' before lemma4, so the statement did not elaborate (Fintype of (Set.range i).compl), yet './op begin' printed 'statement OK'. Fix: scaffold should copy 'open ... in' prefixes, and the statement check should fail on elaboration errors. Re-adding the prefix gave identity=syntactic. h_conn is unused.
