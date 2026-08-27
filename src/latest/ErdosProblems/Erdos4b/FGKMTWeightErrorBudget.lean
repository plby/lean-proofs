/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.FGKMTPrimeMeanLogSaving

/-! # One log-log error budget for both literal weight means -/

namespace Erdos4b.FGKMT

open Filter

theorem eventually_weightMeanErrors_loglog_saving (J : ℕ) {d e : ℝ}
    (hd : 0 < d) (he : 0 < e) :
    ∀ᶠ x : ℕ in atTop,
      3 * Real.log (x : ℝ) ^ (-1 / 4 : ℝ) ≤ e / Real.log (Real.log (x : ℝ)) ^ J ∧
      primeMeanErrorEnvelope d x ≤ e / Real.log (Real.log (x : ℝ)) ^ J := by
  filter_upwards [eventually_primeMeanErrorEnvelope_loglog_saving J hd
    (by positivity : 0 < e / 3)] with x hx
  have hquarter : Real.log (x : ℝ) ^ (-1 / 4 : ℝ) ≤ primeMeanErrorEnvelope d x :=
    le_add_of_nonneg_left (Real.exp_pos _).le
  have htotal : 3 * primeMeanErrorEnvelope d x ≤ e / Real.log (Real.log (x : ℝ)) ^ J := by
    calc
      _ ≤ 3 * ((e / 3) / Real.log (Real.log (x : ℝ)) ^ J) :=
        mul_le_mul_of_nonneg_left hx (by norm_num)
      _ = _ := by ring
  refine ⟨(mul_le_mul_of_nonneg_left hquarter (by norm_num : (0 : ℝ) ≤ 3)).trans htotal, ?_⟩
  exact (by linarith [primeMeanErrorEnvelope_pos d x] :
    primeMeanErrorEnvelope d x ≤ 3 * primeMeanErrorEnvelope d x).trans htotal

end Erdos4b.FGKMT

#print axioms Erdos4b.FGKMT.eventually_weightMeanErrors_loglog_saving
