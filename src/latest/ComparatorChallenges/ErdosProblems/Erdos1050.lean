/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

/-!
# Erdős Problem 1050

We prove that
`∑' n : ℕ+, 1 / ((2 : ℝ) ^ (n : ℕ) - 3)` is irrational.

-/

namespace Erdos1050

/-! ## The original series and a shifted Lambert series -/

/-- The `n`th term of the target series, with `n = 0` representing the
mathematical index `1`. -/
noncomputable def targetTerm (n : ℕ) : ℝ :=
  1 / ((2 : ℝ) ^ (n + 1) - 3)

/-- The sum in Erdős Problem 1050, indexed by positive natural numbers. -/
noncomputable def erdos1050Series : ℝ :=
  ∑' n : ℕ+, 1 / ((2 : ℝ) ^ (n : ℕ) - 3)

theorem erdos_1050 : Irrational erdos1050Series := by
  sorry

end Erdos1050
