/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.FGKMTSieveCutoff

/-!
# A smooth positive extension of the linear profile denominator

On the nonnegative axis the denominator is exactly `1 + v`. The
extension below removes its negative pole without changing any sieve
profile values or derivatives on that axis.
-/

namespace Erdos4b.FGKMT

noncomputable section

open Filter
open scoped Topology

def profileDenominator (v : ℝ) : ℝ := 1 + v * Real.smoothTransition (4 * v + 3)

theorem profileDenominator_contDiff {n : ℕ∞} : ContDiff ℝ n profileDenominator := by
  unfold profileDenominator
  exact contDiff_const.add (contDiff_id.mul
    (Real.smoothTransition.contDiff.comp (by fun_prop)))

theorem quarter_le_profileDenominator (v : ℝ) : (1 / 4 : ℝ) ≤ profileDenominator v := by
  by_cases hv : v ≤ -(3 / 4)
  · rw [profileDenominator, Real.smoothTransition.zero_of_nonpos (by linarith)]
    norm_num
  · have hv' : -(3 / 4 : ℝ) < v := lt_of_not_ge hv
    by_cases hv0 : v ≤ 0
    · have hh : v ≤ v * Real.smoothTransition (4 * v + 3) := by
        simpa only [mul_one] using
          mul_le_mul_of_nonpos_left (Real.smoothTransition.le_one (4 * v + 3)) hv0
      dsimp only [profileDenominator]
      linarith
    · have hh := mul_nonneg (le_of_not_ge hv0) (Real.smoothTransition.nonneg (4 * v + 3))
      dsimp only [profileDenominator]
      linarith

theorem profileDenominator_pos (v : ℝ) : 0 < profileDenominator v :=
  lt_of_lt_of_le (by norm_num) (quarter_le_profileDenominator v)

theorem profileDenominator_eq_linear {v : ℝ} (hv : -(1 / 2 : ℝ) ≤ v) :
    profileDenominator v = 1 + v := by
  rw [profileDenominator, Real.smoothTransition.one_of_one_le (by linarith), mul_one]

theorem profileDenominator_hasDerivAt {v : ℝ} (hv : 0 ≤ v) :
    HasDerivAt profileDenominator 1 v := by
  apply ((hasDerivAt_id v).const_add 1).congr_of_eventuallyEq
  filter_upwards [lt_mem_nhds (show -(1 / 2 : ℝ) < v by linarith)] with u hu
  exact profileDenominator_eq_linear hu.le

theorem profileDenominator_deriv {v : ℝ} (hv : 0 ≤ v) : deriv profileDenominator v = 1 :=
  (profileDenominator_hasDerivAt hv).deriv

end

end Erdos4b.FGKMT

#print axioms Erdos4b.FGKMT.profileDenominator_hasDerivAt
