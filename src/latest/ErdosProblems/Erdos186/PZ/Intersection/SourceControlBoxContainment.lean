/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.PZ.Intersection.IntegerBoxCarrierContainment

namespace Erdos186.PZ.Intersection

noncomputable section

set_option autoImplicit false

/-- The ordinary coefficient box is contained in every nontrivial symmetric
control box. -/
theorem gapCoefficientBox_subset_controlIntegerBox {ambient r : ℕ}
    (P : GAP ambient r) {m : ℕ} (hm : 1 ≤ m) :
    (gapCoefficientBox P).carrier ⊆ (controlIntegerBox P m).carrier := by
  refine integerBox_carrier_subset_of_coordinate
    (gapCoefficientBox P) (controlIntegerBox P m) ?_
  intro i x hx
  change 0 ≤ x ∧ x ≤ (P.widths i : ℤ) - 1 at hx
  change -((m * (P.widths i - 1) : ℕ) : ℤ) ≤ x ∧
    x ≤ ((m * (P.widths i - 1) : ℕ) : ℤ)
  exact nonnegativeInterval_subset_symmetricScaled
    (P.width_pos i) hm hx

end

end Erdos186.PZ.Intersection
