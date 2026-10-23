# Draft note: `RamanujanTau.τ_one` rests on a placeholder (not sent anywhere)

Pinned upstream: google-deepmind/formal-conjectures `96343eeb5990ff13735e728cd0195eff0156a3bb`,
file `FormalConjectures/Wikipedia/RamanujanTau.lean`.

## Observation

`RamanujanTau.τ_one : τ 1 = 1` is written with a proof, but that proof uses the API lemma
`RamanujanTau.multipliable`, whose own proof is the placeholder. So `τ_one` is not actually
established upstream:

```
#print axioms RamanujanTau.τ_one
-- 'RamanujanTau.τ_one' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
```

The dependency matters mathematically: `Δ` is a `tprod`, and an unconditional `tprod` of a
non-multipliable family is `1`, which would make `τ 1 = 0` and `τ 2 = 0`.

## Evidence that the gap can be closed

This repository proves the placeholder verbatim:
`OpenProofs.RamanujanTau.multipliable : Multipliable fun n : ℕ+ ↦ ((1 - X ^ (n : ℕ)) ^ 24 : PowerSeries ℤ)`
in `OpenProofs/Results/Wikipedia/RamanujanTau_two.lean` (reindexing Mathlib's
`multipliable_one_sub_X_pow` along `ℕ+ ≃ ℕ`, then `Multipliable.pow`), together with
`τ 2 = -24`. Both pass all checker layers (syntactic statement identity; axioms
`propext, Classical.choice, Quot.sound`). See `ledger/LEDGER.md`, claims
`ramanujanTau.multipliable` and `ramanujanTau.two`.

## Suggested action (for the owner to decide)

Either upstream the short multipliability proof, or mark `τ_one` as conditional on
`multipliable`. Nothing has been filed.
