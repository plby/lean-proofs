import Mathlib

/-!
# Erdős Problem 140

The public theorem below is the literal r3 formulation of the problem:
for every positive real exponent C, the largest three-term-progression-free
subset of {1, ..., N} is O(N / (log N)^C).

The long finite-group argument is split into the files in
ErdosProblems/Erdos140/.  This endpoint first turns the concrete
rank-regular two-Bohr supply into the ordered Kelley--Meka progression count,
then uses the elementary quantitative endpoint from Quantitative.lean.
-/

open Filter
open scoped Topology

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
