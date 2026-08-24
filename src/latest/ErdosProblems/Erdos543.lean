/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/- Original license: Apache 2.0. Note: This file has been modified. -/
/-
This is a Lean formalization of a solution to Erdős Problem 543.
https://www.erdosproblems.com/forum/thread/543

Informal authors:
- Q. Tang
- ChatGPT

Formal authors:
- Codex
- GPT-5.6 Sol

URLs:
- https://github.com/plby/lean-proofs/blob/main/ErdosProblems/Erdos543.md
-/
/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, ChatGPT
-/

import ErdosProblems.Erdos543.CoreObstruction

/-!
# Erdős Problem 543

For a finite abelian group `G` and a uniformly chosen `k`-element subset
`A`, let `Model.SubsetSumComplete A` mean that every element of `G` is the
sum of a subset of `A`.  The exact finite probability condition

`Model.HalfComplete G k`

is the cardinal inequality saying that at least half of the `k`-subsets are
complete.  The function `Model.universalF N` is the least `k` for which this
holds for every finite abelian group of cardinality `N`.

Erdős Problem 543 asked whether

`universalF N ≤ log N / log 2 + o(log log N)`.

The answer is no.  Following Ma and Tang, the development proves that every
candidate `o(log log N)` error term fails eventually on a cofinal sequence
of prime cyclic groups.  The proof uses growing factorial moments,
Bonferroni inequalities, rank stratification of Boolean incidence matrices,
the `3/4` Boolean-cube intersection bound, and a second-moment argument.

The detailed mathematical proof and the map from its lemmas to this Lean
development are in `tex/543.tex`.
-/

open Filter
open scoped Topology

namespace Erdos543

/-- Public spelling of subset-sum completeness in Problem 543. -/
abbrev SubsetSumComplete {G : Type*} [AddCommGroup G] [Fintype G]
    (A : Finset G) : Prop :=
  Model.SubsetSumComplete A

/-- The exact universal threshold `f(N)` from Problem 543. -/
noncomputable abbrev f (N : ℕ) : ℕ :=
  Model.universalF N

/-- The literal proposed asymptotic upper bound, with
`log₂ N = log N / log 2` and the little-oh condition written as convergence
of the quotient by `log (log N)`. -/
abbrev Problem543UpperBound : Prop :=
  FinalLogic.Problem543UpperBound

/-- Ma--Tang's prime-cyclic obstruction, in the exact form needed to refute
the proposed universal upper bound. -/
theorem ma_tang_prime_cyclic_obstruction :
    FinalLogic.EventualPrimeCyclicFailure :=
  CoreObstruction.eventualPrimeCyclicFailure

/-- Resolution of Erdős Problem 543: the proposed
`f(N) ≤ log₂ N + o(log log N)` upper bound is false. -/
theorem not_erdos_543 : ¬ ((∃ g : ℕ → ℝ,
  Erdos543.FinalLogic.IsLittleOLogLog g ∧
  ∀ᶠ N : ℕ in Filter.atTop,
    (Model.universalF N : ℝ) ≤ Erdos543.cutoffArgument g N)) :=
  FinalLogic.not_problem543UpperBound_of_eventualPrimeCyclicFailure
    ma_tang_prime_cyclic_obstruction

end Erdos543

#print axioms Erdos543.not_erdos_543

alias _root_.Erdos543.erdos_543 := _root_.Erdos543.not_erdos_543
