# Attempt log: `AgohGiuga.agoh_giuga.variants._1000_le_digits_length_of_isStrongGiuga`

Append-only. Record what was tried, dead ends, and the next idea, so later sessions do not repeat them.

- 2026-10-24T08:16:08Z [swarm-w0] checker FAIL: FAIL  AgohGiuga.agoh_giuga.variants._1000_le_digits_length_of_isStrongGiuga  axioms=['propext', 'Classical.choice', 'Quot.sound']  identity=syntactic  failed=['opcheck']
- 2026-10-24T08:17:49Z [swarm-w0] proved: proved; checker PASS
- 2026-10-24T08:24:46Z [swarm-w1] Follows directly from OpenProofs.AgohGiuga.agoh_giuga.variants._1700_le_digits_length_of_isStrongGiuga (PASS 2026-10-24, swarm-w1): import that result module and use 1700 < len -> 1000 <= len (omega).
