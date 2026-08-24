/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
This is a Lean formalization of a solution to Erdős Problem 79.
https://www.erdosproblems.com/forum/thread/79

Informal authors:
- Yufei Wigderson

Formal authors:
- Codex
- GPT-5.6 Sol

URLs:
- https://github.com/plby/lean-proofs/blob/main/ErdosProblems/Erdos79.md
-/
import ErdosProblems.Erdos79.Forest
import ErdosProblems.Erdos79.HighGirth
import ErdosProblems.Erdos79.Minimal
import ErdosProblems.Erdos79.Nonlinear

/-!
# Erdős Problem 79

This file formalizes Wigderson's resolution of Erdős Problem 79: there are infinitely many,
up to isomorphism, finite graphs which are not Ramsey size linear although every proper
ordinary subgraph is Ramsey size linear.

The two quantitative ingredients used here are proved in the imported modules.  Every finite
forest is Ramsey size linear.  On the other hand, a finite first-moment argument shows that a
graph with more than five edges per vertex is not Ramsey size linear, and a second finite
first-moment argument followed by deletion produces such graphs with arbitrarily large girth.
-/

open scoped SimpleGraph

noncomputable section

namespace Erdos79

/-- The closed pair of inputs used by the representation-independent infinitude assembly. -/
theorem infinitudeInputs : InfinitudeInputs :=
  infinitudeInputs_of_dense_highGirth
    ramseySizeLinear_of_isAcyclic
    not_ramseySizeLinear_of_five_mul_vertexCount_lt_edgeCount
    exists_dense_highGirth

/-- **Resolution of Erdős Problem 79.**

There is a natural-number-indexed sequence of pairwise non-isomorphic finite graphs, every one
of which is not Ramsey size linear while each of its proper ordinary subgraphs is Ramsey size
linear.  `GraphCode` represents a finite graph on `Fin n`; `Isomorphic` is ordinary graph
isomorphism, so pairwise non-isomorphism states infinitude of isomorphism classes rather than
mere infinitude of labelled presentations. -/
theorem erdos_79 :
    ∃ f : ℕ → GraphCode,
      (∀ n, MinimallyNonRamseySizeLinear (f n)) ∧
      Pairwise fun i j ↦ ¬ Isomorphic (f i) (f j) :=
  exists_pairwise_nonisomorphic_sequence infinitudeInputs

#print axioms erdos_79

end Erdos79

alias _root_.Erdos79.erdos79 := _root_.Erdos79.erdos_79
