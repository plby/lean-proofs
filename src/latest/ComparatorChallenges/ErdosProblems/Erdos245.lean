/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

open Filter Set
open scoped Pointwise

namespace Erdos245

theorem erdos_245 :
    ∀ (A : Set ℕ), A.Infinite →
      atTop.Tendsto
        (fun N ↦ (A ∩ Icc 1 ⌊N⌋₊ |>.ncard : ℝ) / N) (nhds 0) →
      3 ≤ atTop.limsup
        fun N : ℝ ↦ ((A + A) ∩ Icc 1 ⌊N⌋₊ |>.ncard : EReal) /
          (A ∩ Icc 1 ⌊N⌋₊).ncard := by
  sorry

end Erdos245
