/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.PZ.Intersection.SourceFunctionalSlabDenseDilation

namespace Erdos186.PZ.Intersection

set_option autoImplicit false

/-- A nonnegative integral interval of length `w` lies in its symmetric
`m`-fold enlargement when `m` is nonzero. -/
theorem nonnegativeInterval_subset_symmetricScaled
    {w m : ℕ} {x : ℤ} (hw : 1 ≤ w) (hm : 1 ≤ m)
    (hx : 0 ≤ x ∧ x ≤ (w : ℤ) - 1) :
    -((m * (w - 1) : ℕ) : ℤ) ≤ x ∧
      x ≤ ((m * (w - 1) : ℕ) : ℤ) := by
  have hwidthNat : w - 1 ≤ m * (w - 1) := by
    simpa only [one_mul] using Nat.mul_le_mul_right (w - 1) hm
  have hwidthInt : ((w - 1 : ℕ) : ℤ) ≤
      ((m * (w - 1) : ℕ) : ℤ) := by
    exact_mod_cast hwidthNat
  have hupper : x ≤ ((w - 1 : ℕ) : ℤ) := by
    rw [Nat.cast_sub hw]
    exact hx.2
  exact ⟨(neg_nonpos.mpr (Int.natCast_nonneg _)).trans hx.1,
    hupper.trans hwidthInt⟩

end Erdos186.PZ.Intersection
