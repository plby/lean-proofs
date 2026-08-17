/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
This file formalizes Terence Tao's negative resolution of Erdős Problem 135.

The public theorem constructs, for every `n`, exactly `n` points in the
Euclidean plane such that every four determine at least five distances, while
the total number of distances is `O(n^2 / sqrt (log n))`.

Informal sources:
* T. Tao, "Planar point sets with forbidden 4-point patterns and few
  distinct distances", arXiv:2409.01343 (2024).
* A. Dumitrescu, "Distinct distances in planar point sets with forbidden
  4-point patterns", Discrete Math. 343 (2020), 111967.

The detailed mathematical reconstruction and Leanization plan are in
`tex/135.tex`.
-/

import Mathlib

open Filter Finset Real
open scoped BigOperators EuclideanGeometry Real

namespace Erdos135

set_option autoImplicit false

/-- The Euclidean plane used in the public statement. -/
abbrev Plane := EuclideanSpace ℝ (Fin 2)

/-- The nonzero distances determined by a finite point set. -/
noncomputable def distinctDistances (S : Finset Plane) : Finset ℝ :=
  S.offDiag.image fun e => dist e.1 e.2

/-- The local hypothesis in Erdős Problem 135: every four points determine
at least five distances. -/
def HasPhi45 (S : Finset Plane) : Prop :=
  ∀ Q : Finset Plane, Q ⊆ S → Q.card = 4 → 5 ≤ (distinctDistances Q).card

/-- The number of distances in a finite point set. -/
noncomputable def distanceCount (S : Finset Plane) : ℕ :=
  (distinctDistances S).card

open scoped LSeries.notation NNReal

theorem erdos_135 :
    ∃ A : ℕ → Finset Plane,
      (∀ n : ℕ, (A n).card = n ∧ HasPhi45 (A n)) ∧
      (fun n : ℕ => (distanceCount (A n) : ℝ)) =O[atTop]
        (fun n : ℕ => (n : ℝ) ^ 2 /
          Real.sqrt (Real.log (n : ℝ))) := by
  sorry

end Erdos135
