import Mathlib.Analysis.Analytic.OfScalars
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Complex.Basic

/-! Uniqueness of scalar coefficients in an absolutely convergent local series. -/

namespace Erdos157.Elementary

open scoped Topology

theorem hasFPowerSeriesAt_of_scalar_hasSum (c : ℕ → ℂ) (f : ℂ → ℂ)
    (r : ℝ) (hr : 0 < r)
    (hc : Summable (fun n => ‖c n‖ * r ^ n))
    (hf : ∀ z : ℂ, ‖z‖ < r → HasSum (fun n => c n * z ^ n) (f z)) :
    HasFPowerSeriesAt f (FormalMultilinearSeries.ofScalars ℂ c) 0 := by
  refine ⟨ENNReal.ofReal r, ?_⟩
  refine ⟨?_, ENNReal.ofReal_pos.mpr hr, ?_⟩
  · have h := (FormalMultilinearSeries.ofScalars ℂ c).le_radius_of_summable_norm
      (r := ⟨r, hr.le⟩) (by
        change Summable (fun n => ‖FormalMultilinearSeries.ofScalars ℂ c n‖ * r ^ n)
        simpa only [FormalMultilinearSeries.ofScalars_norm] using hc)
    convert h using 1
    exact ENNReal.ofReal_eq_coe_nnreal hr.le
  · intro z hz
    have hznorm : ‖z‖ < r := by
      simpa only [Metric.eball_ofReal, Metric.mem_ball, dist_zero_right] using hz
    simpa only [FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul, zero_add] using hf z hznorm

theorem scalar_coefficients_eq (a b : ℕ → ℂ) (f : ℂ → ℂ) (r : ℝ) (hr : 0 < r)
    (ha : Summable (fun n => ‖a n‖ * r ^ n))
    (hb : Summable (fun n => ‖b n‖ * r ^ n))
    (hfa : ∀ z : ℂ, ‖z‖ < r → HasSum (fun n => a n * z ^ n) (f z))
    (hfb : ∀ z : ℂ, ‖z‖ < r → HasSum (fun n => b n * z ^ n) (f z)) : a = b := by
  apply FormalMultilinearSeries.ofScalars_series_injective ℂ ℂ
  exact (hasFPowerSeriesAt_of_scalar_hasSum a f r hr ha hfa).eq_formalMultilinearSeries
    (hasFPowerSeriesAt_of_scalar_hasSum b f r hr hb hfb)

end Erdos157.Elementary
