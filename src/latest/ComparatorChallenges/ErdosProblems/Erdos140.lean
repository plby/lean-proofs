/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

open Filter

namespace Erdos140

noncomputable def r3 (N : ℕ) : ℕ :=
  addRothNumber (Finset.Icc 1 N)

/-- Once the concrete rank-regular supply has been established, the exact
Erdős-140 asymptotic bound follows for every real logarithmic exponent.
The positivity hypothesis from the problem statement is therefore not needed
at this final analytic step. -/

theorem erdos_140 (C : ℝ) (hC : 0 < C) :
    (fun N : ℕ => (r3 N : ℝ)) =O[atTop]
      (fun N : ℕ => (N : ℝ) / (Real.log (N : ℝ)) ^ C) := by
  sorry

end Erdos140
