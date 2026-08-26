import ErdosProblems.Erdos421.SmoothedPrimeErrorMajorant
import ErdosProblems.Erdos421.StretchedLogDecay

/-! # Arbitrary logarithmic savings for the smoothed von Mangoldt-minus-one sum -/

namespace Erdos421

open Filter Topology

theorem smoothedPrimeError_majorant_log_tendsto (D A : ℝ) :
    Tendsto (fun x : ℝ ↦ D *
      (Real.exp (-(primeContourCoefficient / 2) * (Real.log x) ^ (1 / 16 : ℝ)) *
        (Real.log x) ^ A + Real.exp (-(Real.log x) ^ (1 / 16 : ℝ)) *
          (Real.log x) ^ (A + 1))) atTop (𝓝 0) := by
  have hc : 0 < primeContourCoefficient / 2 := div_pos primeContourCoefficient_pos (by norm_num)
  have hfirst := stretched_log_exp_mul_rpow_tendsto hc A
  have hsecond := stretched_log_exp_mul_rpow_tendsto (by norm_num : (0 : ℝ) < 1) (A + 1)
  simpa only [neg_one_mul, add_zero, mul_zero] using (hfirst.add hsecond).const_mul D

theorem smoothedPrimeError_log_saving (A : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ X₀ > 1, ∀ x : ℝ, X₀ ≤ x → ‖smoothedPrimeErrorSum x‖ ≤ ε * x / (Real.log x) ^ A := by
  obtain ⟨D, _, hmajor⟩ := exists_smoothedPrimeError_majorant
  have hsmall := (smoothedPrimeError_majorant_log_tendsto D A).eventually (gt_mem_nhds hε)
  have hlarge : ∀ᶠ x : ℝ in atTop, ‖smoothedPrimeErrorSum x‖ ≤ ε * x / (Real.log x) ^ A := by
    filter_upwards [hmajor, hsmall, eventually_ge_atTop (2 : ℝ)] with x hmajor hsmall hx
    have hxp : 0 < x := by linarith
    have hlog : 0 < Real.log x := Real.log_pos (by linarith)
    have hp : 0 < (Real.log x) ^ A := Real.rpow_pos_of_pos hlog A
    have hscaled := mul_le_mul_of_nonneg_right hmajor hp.le
    have he : (Real.exp (-(primeContourCoefficient / 2) * (Real.log x) ^ (1 / 16 : ℝ)) +
        Real.log x * Real.exp (-(Real.log x) ^ (1 / 16 : ℝ))) * (Real.log x) ^ A =
        Real.exp (-(primeContourCoefficient / 2) * (Real.log x) ^ (1 / 16 : ℝ)) *
          (Real.log x) ^ A + Real.exp (-(Real.log x) ^ (1 / 16 : ℝ)) *
            (Real.log x) ^ (A + 1) := by
      rw [Real.rpow_add hlog, Real.rpow_one]
      ring
    rw [mul_assoc D, he] at hscaled
    have hratio := (le_div_iff₀ hp).mpr (hscaled.trans hsmall.le)
    have hnorm := (div_le_iff₀ hxp).mp hratio
    exact hnorm.trans_eq (by ring)
  obtain ⟨X₀, hX₀⟩ := eventually_atTop.mp hlarge
  refine ⟨max X₀ 2, lt_of_lt_of_le (by norm_num : (1 : ℝ) < 2) (le_max_right _ _), ?_⟩
  intro x hx
  exact hX₀ x ((le_max_left X₀ 2).trans hx)

end Erdos421
