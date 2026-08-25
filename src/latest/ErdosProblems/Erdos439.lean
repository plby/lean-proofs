/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/- Original license: Apache 2.0. Note: This file has been modified. -/
/-
This is a Lean formalization of a solution to Erdős Problem 439.
https://www.erdosproblems.com/forum/thread/439

Informal authors:
- A. Khalfalah
- S. Lodha
- Endre Szemerédi

Formal authors:
- Codex
- GPT-5.6 Sol

URLs:
- https://github.com/plby/lean-proofs/blob/main/ErdosProblems/Erdos439.md
-/
/-
Copyright 2026.
Released under Apache 2.0 license.
-/

import ErdosProblems.Erdos439.PowerSums
import ErdosProblems.Erdos438

/-!
# Erdős Problem 439 (delegated square-sum density formulation)

The delegated statement asks for the largest cardinality of a set
`A ⊆ {1, ..., N}` whose literal sumset `A + A` contains no square.  The
current Erdős Problems database numbers this density problem as 438 and uses
439 for a different colouring problem.  The complete square-sum density
development therefore lives in `ErdosProblems.Erdos438`; this file provides
the requested problem-number-facing interface without duplicating that proof.

The predicate below includes diagonal pairs, exactly as the literal sumset
condition does.  The final theorem says that the normalized finite extremal
function converges to `11 / 32`, simultaneously expressing the Massias lower
construction and the Khalfalah--Lodha--Szemerédi asymptotic upper bound.
-/

open Filter

namespace Erdos439

noncomputable section

/-- A finite set is square-sum-free when the sum of every ordered pair of its
elements, including a repeated element, is not a natural-number square. -/
abbrev SquareSumFree (A : Finset ℕ) : Prop :=
  Erdos438.SquareSumFree A

/-- The exact family of sets considered at endpoint `N`. -/
abbrev admissible (N : ℕ) (A : Finset ℕ) : Prop :=
  Erdos438.admissible N A

/-- All square-sum-free subsets of `{1, ..., N}`. -/
abbrev candidateSets (N : ℕ) : Finset (Finset ℕ) :=
  Erdos438.candidateSets N

/-- The maximum cardinality of a square-sum-free subset of `{1, ..., N}`. -/
abbrev extremalSize (N : ℕ) : ℕ :=
  Erdos438.extremalSize N

/-- Every admissible set is bounded by the extremal value. -/
theorem card_le_extremalSize {N : ℕ} {A : Finset ℕ}
    (hA : admissible N A) : A.card ≤ extremalSize N :=
  Erdos438.card_le_extremalSize hA

/-- The finite maximum defining `extremalSize` is attained. -/
theorem exists_extremizer (N : ℕ) :
    ∃ A : Finset ℕ, admissible N A ∧ A.card = extremalSize N :=
  Erdos438.exists_extremizer N

/-- Resolution of the delegated square-sum density problem: the largest
square-sum-free subset of `{1, ..., N}` has asymptotic density `11 / 32`. -/
theorem erdos_439 :
    Tendsto (fun N : ℕ ↦ (extremalSize N : ℝ) / (N : ℝ)) atTop
      (nhds ((11 : ℝ) / 32)) := by
  exact Erdos438.erdos_438

#print axioms Erdos439.erdos_439

end

end Erdos439
