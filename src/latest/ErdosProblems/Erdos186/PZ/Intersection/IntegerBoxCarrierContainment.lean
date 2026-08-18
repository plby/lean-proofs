/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.PZ.Intersection.IntegerIntervalContainment

namespace Erdos186.PZ.Intersection

set_option autoImplicit false

/-- Coordinatewise interval containment lifts to containment of integer-box
carriers. -/
theorem integerBox_carrier_subset_of_coordinate {d : ℕ}
    (B : Erdos186.IntegerBox d) (C : CFP.IntegerBox d)
    (h : ∀ i (x : ℤ),
      B.lower i ≤ x ∧ x ≤ B.upper i →
        C.lower i ≤ x ∧ x ≤ C.upper i) :
    B.carrier ⊆ C.carrier := by
  intro x hx
  rw [Erdos186.IntegerBox.mem_carrier_iff] at hx
  rw [CFP.IntegerBox.mem_carrier_iff]
  exact fun i ↦ h i (x i) (hx i)

end Erdos186.PZ.Intersection
