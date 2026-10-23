# Possible misformalization: Erdős 552 (`Erdos552.erdos_552.parts.i`)

Status: draft for the owner. Nothing has been filed or sent.

- Upstream: google-deepmind/formal-conjectures at `96343eeb5990ff13735e728cd0195eff0156a3bb`, `FormalConjectures/ErdosProblems/552.lean`
- Informal source: https://www.erdosproblems.com/552
- Pattern: a `question value` statement whose `answer` placeholder is a single constant, although the quantity asked for depends on a parameter that the theorem quantifies over. Whatever value the placeholder is given, the statement is false.

## Upstream Lean statement

```lean
def erdos_552.parts.i.answer : ℕ := sorry
theorem erdos_552.parts.i :
    ∀ (n : ℕ),
      SimpleGraph.graphRamsey (SimpleGraph.cycleGraph 4)
        (completeBipartiteGraph (Fin 1) (Fin n)) =
        erdos_552.parts.i.answer
```

## Informal statement

"Determine the Ramsey number R(C_4, S_n), where S_n = K_{1,n} is the star on n + 1 vertices." The
answer is a function of `n`.

## Why they differ

`erdos_552.parts.i.answer : ℕ` is one number for all `n`. The same file's docstring notes
`R(C₄, S_0) = 1` and `R(C₄, S_1) = 4`. In Lean: `R(C₄, K_{1,0}) = 1` (one vertex embeds the
one-vertex graph `K_{1,0}` in any complement; zero vertices embed neither graph), and
`R(C₄, K_{1,1}) ≠ 1` (on one vertex neither `C₄` nor the edge `K_{1,1}` has an injective copy; and
`sInf ∅ = 0 ≠ 1`).

## Lean evidence

- Variant statement: `OpenProofs/Statements/Erdos552.lean`,
  `OpenProofs.Statements.Erdos552.erdos_552.parts.i.no_constant_answer :
   ∀ a : ℕ, ¬ ∀ (n : ℕ), SimpleGraph.graphRamsey (SimpleGraph.cycleGraph 4)
     (completeBipartiteGraph (Fin 1) (Fin n)) = a`.
- Proof: `OpenProofs/Results/Erdos/P552_parts_i_no_constant_answer.lean`. `#print axioms`: [propext, Classical.choice, Quot.sound]
  (scratch copy `work/scratch/agentAudit/p552.lean`).
- Checker verdict: PASS on all five layers (coordinator run, 2026-10-23; see `ledger/LEDGER.md`).
- The literal negation `¬ type_of% @Erdos552.erdos_552.parts.i` follows from the answer-free form in one line (`fun h => erdos_552.parts.i.no_constant_answer _ h`, checked in scratch), but it mentions `erdos_552.parts.i.answer`, whose body is a placeholder, so its axiom list contains the placeholder axiom and this project's checker would reject it. The answer-free form is strictly stronger and is what was proved.

## Suggested fix

`def erdos_552.parts.i.answer : ℕ → ℕ := sorry` and `… = erdos_552.parts.i.answer n`, possibly for
`n ≥ 1` or eventually in `n`.
