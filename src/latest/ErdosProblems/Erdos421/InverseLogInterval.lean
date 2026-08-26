import ErdosProblems.Erdos421.InverseLogPrimeWeights

/-! # Freezing the logarithmic integral on a short interval -/

namespace Erdos421

open MeasureTheory

theorem log_interval_growth {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    Real.log b - Real.log a ≤ (b - a) / a := by
  have hb : 0 < b := ha.trans_le hab
  have h := Real.log_le_sub_one_of_pos (div_pos hb ha)
  rw [Real.log_div hb.ne' ha.ne'] at h
  exact h.trans_eq (by field_simp)

theorem inverse_log_interval_difference {a b : ℝ} (ha : 1 < a) (hab : a ≤ b) :
    (Real.log a)⁻¹ - (Real.log b)⁻¹ ≤ (b - a) / (a * (Real.log a) ^ 2) := by
  have hap : 0 < a := by linarith
  have hla := Real.log_pos ha
  have hlb := Real.log_pos (ha.trans_le hab)
  have hlogab := Real.log_le_log hap hab
  calc
    _ = (Real.log b - Real.log a) / (Real.log a * Real.log b) := by field_simp
    _ ≤ ((b - a) / a) / (Real.log a * Real.log b) :=
      div_le_div_of_nonneg_right (log_interval_growth hap hab) (mul_nonneg hla.le hlb.le)
    _ ≤ ((b - a) / a) / (Real.log a) ^ 2 :=
      div_le_div_of_nonneg_left (div_nonneg (sub_nonneg.mpr hab) hap.le)
        (sq_pos_of_pos hla) (by nlinarith)
    _ = _ := by field_simp

theorem inverse_log_integral_bounds {a b : ℝ} (ha : 1 < a) (hab : a ≤ b) :
    (b - a) * (Real.log b)⁻¹ ≤ (∫ t in a..b, (Real.log t)⁻¹) ∧
      (∫ t in a..b, (Real.log t)⁻¹) ≤ (b - a) * (Real.log a)⁻¹ := by
  have hap : 0 < a := by linarith
  have hc : ContinuousOn (fun t ↦ (Real.log t)⁻¹) (Set.Icc a b) :=
    fun t ht ↦ ((inverse_log_regular (b := b) ha).1 t ht).continuousAt.continuousWithinAt
  have hi : IntervalIntegrable (fun t ↦ (Real.log t)⁻¹) volume a b :=
    ContinuousOn.intervalIntegrable_of_Icc hab hc
  constructor
  · have h := intervalIntegral.integral_mono_on (μ := volume) hab
      (intervalIntegrable_const (c := (Real.log b)⁻¹)) hi (by
        intro t ht
        exact inv_anti₀ (Real.log_pos (ha.trans_le ht.1))
          (Real.log_le_log (hap.trans_le ht.1) ht.2))
    simpa only [intervalIntegral.integral_const, smul_eq_mul] using h
  · have h := intervalIntegral.integral_mono_on (μ := volume) hab hi
      (intervalIntegrable_const (c := (Real.log a)⁻¹)) (by
        intro t ht
        exact inv_anti₀ (Real.log_pos ha) (Real.log_le_log hap ht.1))
    simpa only [intervalIntegral.integral_const, smul_eq_mul] using h

theorem inverse_log_integral_freeze {a b : ℝ} (ha : 1 < a) (hab : a ≤ b) :
    |(∫ t in a..b, (Real.log t)⁻¹) - (b - a) / Real.log b| ≤
      (b - a) ^ 2 / (a * (Real.log a) ^ 2) := by
  obtain ⟨hlo, hhi⟩ := inverse_log_integral_bounds ha hab
  rw [div_eq_mul_inv, abs_of_nonneg (sub_nonneg.mpr hlo)]
  calc
    _ ≤ (b - a) * ((Real.log a)⁻¹ - (Real.log b)⁻¹) := by linarith
    _ ≤ (b - a) * ((b - a) / (a * (Real.log a) ^ 2)) :=
      mul_le_mul_of_nonneg_left (inverse_log_interval_difference ha hab) (sub_nonneg.mpr hab)
    _ = _ := by ring

end Erdos421
