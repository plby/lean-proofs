/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

namespace Erdos502

def is_s_distance_set {α : Type*} [MetricSpace α] (A : Set α) (s : ℕ) : Prop :=
  A.Finite ∧ Set.ncard {d : ℝ | ∃ x ∈ A, ∃ y ∈ A, x ≠ y ∧ dist x y = d} = s

theorem erdos_502 (d s : ℕ) (A : Set (EuclideanSpace ℝ (Fin d)))
    [Fintype A]
    (hA : is_s_distance_set A s) : Fintype.card A ≤ Nat.choose (d + s) s := by
  sorry

end Erdos502
