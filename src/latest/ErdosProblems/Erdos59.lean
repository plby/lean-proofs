/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
This is a Lean formalization of a solution to Erdős Problem 59.
https://www.erdosproblems.com/forum/thread/59

Informal authors:
- Paul Erdős
- Péter Frankl
- Vojtěch Rödl
- Robert Morris
- David Saxton
- Zoltán Füredi
- Assaf Naor
- Jacques Verstraëte

Formal authors:
- Codex
- GPT-5.6 Sol

URLs:
- https://github.com/plby/lean-proofs/blob/main/ErdosProblems/Erdos59.md
-/
/-
This is a Lean formalization of the negative resolution of Erdős Problem 59.
https://www.erdosproblems.com/59

Informal authors:
- Erdős, Frankl, and Rödl (the non-bipartite positive case)
- Morris and Saxton (the C₆ counterexample)
- Füredi, Naor, and Verstraëte (the extremal graph inputs)

Formal author:
- OpenAI Codex
-/

import ErdosProblems.Erdos59.MorrisSaxtonFinal

namespace Erdos59

/-- The established negative resolution of Erdős Problem 59.

For the six-cycle there is an explicit constant `c = 1 / 100 > 0` and
infinitely many orders on which the number of labelled `C₆`-free graphs is
at least `2 ^ ((1 + c) * ex(n,C₆))`.  Consequently the proposed
`2 ^ ((1 + o(1)) * ex(n,C₆))` upper bound is false in general. -/
theorem not_erdos_59 :
    HasMorrisSaxtonLowerBound (SimpleGraph.cycleGraph 6) ∧
      ¬ HasErdos59UpperBound (SimpleGraph.cycleGraph 6) :=
  ⟨hasMorrisSaxtonLowerBound_cycleGraph_six,
    morrisSaxtonDisprovesErdos59⟩

#print axioms Erdos59.not_erdos_59

end Erdos59

alias _root_.Erdos59.erdos_59 := _root_.Erdos59.not_erdos_59
