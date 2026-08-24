/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

open Filter Finset Set

namespace Erdos255

/-- Discrepancy of the first `N` terms in the actual interval `[0,x)`. -/
noncomputable def anchoredDiscrepancy (z : ℕ → ℝ) (N : ℕ) (x : ℝ) : ℝ :=
  (((range N).filter fun n ↦ z n ∈ Ico (0 : ℝ) x).card : ℝ) - N * x

theorem erdos_255 (z : ℕ → ℝ) (hz : ∀ n, z n ∈ Icc (0 : ℝ) 1) :
    ∃ x ∈ Icc (0 : ℝ) 1,
      Ico (0 : ℝ) x ⊆ Icc (0 : ℝ) 1 ∧
      atTop.limsup (fun N ↦ ((|anchoredDiscrepancy z N x| : ℝ) : EReal)) = ⊤ := by
  sorry

end Erdos255
