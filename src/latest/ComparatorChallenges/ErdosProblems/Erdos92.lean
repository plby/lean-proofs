/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

scoped[EuclideanGeometry] notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

open Filter
open scoped EuclideanGeometry

namespace Erdos92

noncomputable def maxEquidistantPointsAt (x : ℝ²) (points : Finset ℝ²) : ℕ :=
  letI otherPoints := points.erase x
  letI distances := otherPoints.image (dist x)
  sSup (distances.image fun d ↦ (otherPoints.filter fun p ↦ dist x p = d).card)

def hasMinEquidistantProperty (k : ℕ) (A : Finset ℝ²) : Prop :=
  A.Nonempty ∧ ∀ x ∈ A, k ≤ maxEquidistantPointsAt x A

noncomputable def possible_f_values (n : ℕ) : Set ℕ :=
  {k | ∃ (points : Finset ℝ²) (_ : points.card = n), hasMinEquidistantProperty k points}

theorem possible_f_values_BddAbove (n : ℕ) : BddAbove (possible_f_values n) := by
  refine ⟨n, fun k hk => ?_⟩
  obtain ⟨points, hcard, ⟨x, hx⟩, hall⟩ := hk
  refine (hall x hx).trans ?_
  unfold maxEquidistantPointsAt
  refine csSup_le' fun m hm => ?_
  rw [Finset.mem_coe, Finset.mem_image] at hm
  obtain ⟨d, hd, rfl⟩ := hm
  calc ((points.erase x).filter fun p => dist x p = d).card
      ≤ (points.erase x).card := Finset.card_filter_le _ _
    _ ≤ points.card := Finset.card_erase_le
    _ = n := hcard

noncomputable def f (n : ℕ) : ℕ := sSup <| possible_f_values n

theorem erdos_92.variants.strong : ¬
    ∃ c > 0, ∀ᶠ n in atTop, (f n : ℝ) ≤ n ^ (c / (n : ℝ).log.log) := by
  sorry

end Erdos92
