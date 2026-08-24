/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

open scoped RealInnerProductSpace

namespace Erdos224

variable {d : ℕ}

abbrev E (d : ℕ) := EuclideanSpace ℝ (Fin d)

def ObtuseAt {d : ℕ} (x y z : E d) : Prop :=
  ⟪y - x, z - x⟫ < 0

theorem erdos_224
  (A : Finset (E d))
  (hcard : A.card = (2 ^ d) + 1) :
  ∃ x y z : E d, x ∈ A ∧ y ∈ A ∧ z ∈ A ∧
    x ≠ y ∧ x ≠ z ∧ y ≠ z ∧
    ObtuseAt (d := d) x y z := by
  sorry

end Erdos224
