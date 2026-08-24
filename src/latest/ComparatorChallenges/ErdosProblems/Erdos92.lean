/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

open Filter
open scoped EuclideanGeometry

scoped[EuclideanGeometry] notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

namespace Erdos92

noncomputable def maxEquidistantPointsAt (x : ℝ²) (points : Finset ℝ²) : ℕ :=
  letI otherPoints := points.erase x
  letI distances := otherPoints.image (dist x)
  sSup (distances.image fun d ↦ (otherPoints.filter fun p ↦ dist x p = d).card)

def hasMinEquidistantProperty (k : ℕ) (A : Finset ℝ²) : Prop :=
  A.Nonempty ∧ ∀ x ∈ A, k ≤ maxEquidistantPointsAt x A

noncomputable def possible_f_values (n : ℕ) : Set ℕ :=
  {k | ∃ (points : Finset ℝ²) (_ : points.card = n), hasMinEquidistantProperty k points}

noncomputable def f (n : ℕ) : ℕ := sSup <| possible_f_values n

theorem erdos_92.variants.not_erdos_92 : ¬
    ∃ c > 0, ∀ᶠ n in atTop, (f n : ℝ) ≤ n ^ (c / (n : ℝ).log.log) := by
  sorry

end Erdos92
