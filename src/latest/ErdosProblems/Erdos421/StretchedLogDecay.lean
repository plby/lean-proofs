import ErdosProblems.Erdos421.PerronShiftWidth

/-! # Logarithmic decay of the stretched exponential from the zero-free region -/

namespace Erdos421

open Filter Topology

theorem stretched_log_exp_mul_rpow_tendsto {d : ℝ} (hd : 0 < d) (A : ℝ) :
    Tendsto (fun x : ℝ ↦ Real.exp (-d * (Real.log x) ^ (1 / 16 : ℝ)) * (Real.log x) ^ A)
      atTop (𝓝 0) := by
  have hroot := (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 16)).comp
    Real.tendsto_log_atTop
  have h := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (16 * A) d hd).comp hroot
  apply h.congr'
  filter_upwards [eventually_ge_atTop (2 : ℝ)] with x hx
  have hlog : 0 ≤ Real.log x := Real.log_nonneg (by linarith)
  change ((Real.log x) ^ (1 / 16 : ℝ)) ^ (16 * A) *
      Real.exp (-d * (Real.log x) ^ (1 / 16 : ℝ)) = _
  rw [← Real.rpow_mul hlog, show (1 / 16 : ℝ) * (16 * A) = A by ring, mul_comm]

theorem smoothed_log_majorant_tendsto_zero (K : ℕ) (A C : ℝ) :
    Tendsto (fun x : ℝ ↦ C *
      (Real.exp (-perronWidthCoefficient K * (Real.log x) ^ (1 / 16 : ℝ)) *
        (Real.log x) ^ (A + 2) + (Real.log x) ^ (-2 : ℝ))) atTop (𝓝 0) := by
  have hfirst := stretched_log_exp_mul_rpow_tendsto (perronWidthCoefficient_pos K) (A + 2)
  have hsecond := (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 2)).comp
    Real.tendsto_log_atTop
  simpa only [add_zero, mul_zero, Function.comp_apply] using! (hfirst.add hsecond).const_mul C

theorem logarithmic_frequency_term_bound {L T A : ℝ} (hL : 0 < L)
    (hT : L ^ (A + 4) ≤ T) : (L ^ 2 / T) * L ^ A ≤ L ^ (-2 : ℝ) := by
  have hp : 0 < L ^ (A + 4) := Real.rpow_pos_of_pos hL _
  calc
    _ ≤ (L ^ 2 / L ^ (A + 4)) * L ^ A :=
      mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_left (sq_nonneg L) hp hT)
        (Real.rpow_nonneg hL.le A)
    _ = (L ^ (2 : ℝ) / L ^ (A + 4)) * L ^ A := by rw [Real.rpow_two]
    _ = L ^ ((2 - (A + 4)) + A) := by rw [← Real.rpow_sub hL, ← Real.rpow_add hL]
    _ = _ := by congr 1; ring

end Erdos421
