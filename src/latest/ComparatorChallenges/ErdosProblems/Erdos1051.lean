/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

namespace Erdos1051

open scoped Classical in
theorem erdos_1051_irrational
  (a : ℕ → ℕ)
  (h_mono : StrictMono a)
  (h_pos : ∀ n, 0 < a n)
  (h_liminf : 1 < Filter.atTop.liminf (fun n ↦ (a n : ℝ) ^ ((1 : ℝ) / 2 ^ n))) :
  Irrational (∑' n, 1 / ((a n : ℝ) * (a (n + 1) : ℝ))) := by
  sorry

end Erdos1051
