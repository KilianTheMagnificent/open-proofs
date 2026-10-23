# Draft: first-iteration results (for the owner; not sent anywhere)

Status: draft. Nothing here has been posted, filed or submitted. If the owner wants to offer
these upstream, the formal-conjectures convention is a `formal_proof using lean4 at "<url>"`
attribute pointing at a stable commit of a public repository; this repository is local only, so
there is no URL yet.

Pinned upstream: google-deepmind/formal-conjectures `96343eeb5990ff13735e728cd0195eff0156a3bb`,
Lean `v4.33.1`, Mathlib `0df444a360eaa60ab8c11dca51a86af692955474`. Every item below passed all
five checker layers (see `ledger/LEDGER.md`); statement identity is syntactic (`Expr`-equal to
the upstream statement) and the axioms are exactly `propext`, `Classical.choice`, `Quot.sound`.

## Upstream placeholders now proved (tier a)

| Upstream declaration | Category upstream | Proof file | Idea |
|---|---|---|---|
| `Erdos292.erdos_292.variants.two_mul` | research solved | `OpenProofs/Results/Erdos/P292_two_mul.lean` | {2} ∪ 2·S (van Doorn) |
| `Erdos292.erdos_292.variants.mul` | research solved | `OpenProofs/Results/Erdos/P292_mul.lean` | replace max m of S by m·T (Straus) |
| `Erdos292.erdos_292.variants.prime_pow` | research solved | `OpenProofs/Results/Erdos/P292_prime_pow.lean` | p-adic valuation of the largest term |
| `Erdos902.erdos_902.variants.f_two` | research solved | `OpenProofs/Results/Erdos/P902_f_two.lean` | in-neighbourhoods carry S₁, so in-degree ≥ 3 |
| `Erdos902.erdos_902.variants.erdos_lower` | research solved | `OpenProofs/Results/Erdos/P902_erdos_lower.lean` | in-neighbourhood recursion + probabilistic existence |
| `RamseyNumbers.ramsey_number_three_three` | research solved | `OpenProofs/Results/Wikipedia/RamseyNumbers_three_three.lean` | pigeonhole; C₅ |
| `RamseyNumbers.ramsey_number_three_four` | research solved | `OpenProofs/Results/Wikipedia/RamseyNumbers_three_four.lean` | degree parity; Wagner graph |
| `Erdos349.exists_finsetSum_two_pow` | textbook | `OpenProofs/Results/Erdos/P349_exists_finsetSum_two_pow.lean` | binary expansion (already has an external `formal_proof` link) |

Remark on `erdos_902.variants.erdos_lower` (not a misformalization): `f n` is an `sInf` over ℕ,
which is `0` when no tournament has property Sₙ. The statement `2 ^ (n + 1) - 1 ≤ f n` therefore
also asserts that Sₙ tournaments exist for every n (Erdős's probabilistic upper-bound argument),
not only the lower-bound recursion. Both parts are true and both are proved here. Upstream may
want the docstring to say so.

## Self-recorded special cases of open problems (tier b)

`OpenProofs/Statements/Erdos828.lean` records `type_of% (Erdos828.erdos_828 0)` and
`type_of% (Erdos828.erdos_828 (-1))` (the open statement at a = 0 and a = −1); both are proved
(powers of two; primes). These are easy, well-known cases and are not new mathematics.
