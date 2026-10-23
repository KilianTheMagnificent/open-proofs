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
| `RamseyNumbers.ramsey_number_three_five` | research solved | `OpenProofs/Results/Wikipedia/RamseyNumbers_three_five.lean` | degree ≤ 4 + R(3,4) on the non-neighbourhood; circulant on Z/13 |
| `Erdos629.erdos_629.variants.n_two` | research solved | `OpenProofs/Results/Erdos/P629_n_two.lean` | K₃,₃ not 2-choosable; ≤ 5 vertices bipartite ⇒ 2-choosable |
| `Erdos349.exists_finsetSum_two_pow` | textbook | `OpenProofs/Results/Erdos/P349_exists_finsetSum_two_pow.lean` | binary expansion (already has an external `formal_proof` link) |
| `CongruentNumber.not_congruentNumber_1` | textbook | `OpenProofs/Results/Wikipedia/CongruentNumber_not_one.lean` | Fermat descent for x⁴ − y⁴ = z² (Mathlib has only the sum form) |
| `Erdos1193.erdos_1193.parts.i`, `.parts.ii`, `.variants.upper_density_pos`, `.variants.sumRep_univ` | research solved | `OpenProofs/Results/Erdos/P1193_univ.lean` | A = ℕ, g(n) = n + 1 (trivial as recorded, as upstream notes) |
| `RamanujanTau.τ_two`, `RamanujanTau.multipliable` | test, API | `OpenProofs/Results/Wikipedia/RamanujanTau_two.lean` | finite partial products + continuity of `coeff` |
| `Erdos554.multicolourGraphRamsey_one_cycleGraph_five` | test | `OpenProofs/Results/Erdos/P554_one_colour_C5.lean` | one colour: label graph is ⊤ |
| `Erdos138.monoAPNumber_two_one`, `Erdos138.monoAPNumber_two_two` | test | `OpenProofs/Results/Erdos/P138_W_one.lean`, `P138_W_two.lean` | direct; pigeonhole (W 2 already has an external link) |
| `WrittenOnTheWallII.Test.petersen_girth`, `WrittenOnTheWallII.Test.C6_girth` | test | `OpenProofs/Results/WrittenOnTheWallII/` | explicit cycles + kernel `decide` |

See also `outbox/note-RamanujanTau-tau_one-rests-on-placeholder.md`: upstream `τ_one` is written
with a proof but depends on the placeholder `multipliable`, which this repository proves.

Remark on `erdos_902.variants.erdos_lower` (not a misformalization): `f n` is an `sInf` over ℕ,
which is `0` when no tournament has property Sₙ. The statement `2 ^ (n + 1) - 1 ≤ f n` therefore
also asserts that Sₙ tournaments exist for every n (Erdős's probabilistic upper-bound argument),
not only the lower-bound recursion. Both parts are true and both are proved here. Upstream may
want the docstring to say so.

## Self-recorded special cases of open problems (tier b)

`OpenProofs/Statements/Erdos828.lean` records `type_of% (Erdos828.erdos_828 0)` and
`type_of% (Erdos828.erdos_828 (-1))` (the open statement at a = 0 and a = −1); both are proved
(powers of two; primes). These are easy, well-known cases and are not new mathematics.

## Possible misformalizations (11 statements, 8 problems)

Open `question value` statements whose placeholder answer is a single value although the
quantity depends on a parameter the theorem quantifies over; each is false for *every* choice of
the answer. For each, the answer-free negation (`∀ a, ¬ <upstream body with a>`) is recorded in
`OpenProofs/Statements/ErdosN.lean` and proved; all pass the checker. Drafts with suggested fixes:
`outbox/misformalization-Erdos{142,319,321,361,409,450,503,552,692}-*.md`. Affected upstream
declarations: `erdos_142`, `erdos_142.variants.isTheta`, `erdos_319`, `erdos_321`, `erdos_361`,
`erdos_409.parts.i`, `erdos_409.variants.sigma`, `erdos_450`, `erdos_503`, `erdos_552.parts.i`,
`erdos_692.parts.ii`. A tenth draft (Erdős 506) has only a conditional argument.
