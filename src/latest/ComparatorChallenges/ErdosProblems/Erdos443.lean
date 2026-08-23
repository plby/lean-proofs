/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

namespace Erdos443

set_option linter.style.openClassical false
set_option linter.style.setOption false
set_option linter.style.whitespace false
set_option linter.flexible false
set_option linter.unusedVariables false

open scoped Classical

open scoped Pointwise

set_option maxHeartbeats 0
set_option linter.style.cases false
set_option linter.style.longLine false
set_option linter.style.multiGoal false
set_option linter.style.refine false

def A (k : ℕ) : Finset ℕ :=
  (Finset.Ioo 0 k).image (fun r => r * (k - r))
end Erdos443

open scoped Classical
open scoped Pointwise

namespace Erdos443

open scoped Classical in
theorem erdos_443_part_one (s : ℕ) :
  ∃ m n : ℕ, n < m ∧ s ≤ ((A n ∩ A m).card : ℝ) := by
  sorry

open scoped Classical in
theorem erdos_443_part_two (ε : ℝ) (hε : 0 < ε) :
  ∃ n₀ : ℕ, ∀ m n : ℕ, n₀ < n → n < m →
  ((A n ∩ A m).card : ℝ) < ((m : ℝ) * n) ^ (ε) := by
  sorry

end Erdos443
