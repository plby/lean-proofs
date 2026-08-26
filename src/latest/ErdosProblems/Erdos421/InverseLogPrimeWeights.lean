import ErdosProblems.Erdos421.PrimeWeightedDiscrepancy
import Mathlib.Analysis.SpecialFunctions.Log.InvLog

/-! # The inverse-logarithm weight for unweighted prime counting -/

namespace Erdos421

open MeasureTheory

theorem inverse_log_regular {a b : ℝ} (ha : 1 < a) :
    (∀ t ∈ Set.Icc a b, DifferentiableAt ℝ (fun x ↦ (Real.log x)⁻¹) t) ∧
      ContinuousOn (deriv (fun x ↦ (Real.log x)⁻¹)) (Set.Icc a b) := by
  constructor
  · intro t ht
    have ht1 : 1 < t := ha.trans_le ht.1
    exact Real.differentiableAt_inv_log (by linarith) (by linarith) (by linarith)
  · rw [Real.deriv_inv_log]
    intro t ht
    have ht1 : 1 < t := ha.trans_le ht.1
    have ht0 : t ≠ 0 := by linarith
    have hlog : Real.log t ≠ 0 := (Real.log_pos ht1).ne'
    have hlog2 : (Real.log t) ^ 2 ≠ 0 := pow_ne_zero 2 hlog
    exact ContinuousAt.continuousWithinAt (by fun_prop)

theorem inverse_log_weighted_derivative {t : ℝ} (ht : 1 < t) :
    t * |deriv (fun x ↦ (Real.log x)⁻¹) t| = ((Real.log t) ^ 2)⁻¹ := by
  have htp : 0 < t := by linarith
  rw [Real.deriv_inv_log_apply, abs_div, abs_neg, abs_inv,
    abs_of_pos htp, abs_of_nonneg (sq_nonneg _)]
  field_simp

theorem inverse_log_prime_sum_eq_card (a b : ℝ) :
    (∑ p ∈ primesInRealInterval a b, (Real.log p)⁻¹ * Real.log p) =
      (primesInRealInterval a b).card := by
  calc
    _ = ∑ _p ∈ primesInRealInterval a b, (1 : ℝ) := by
      apply Finset.sum_congr rfl
      intro p hp
      have hpp := (Finset.mem_filter.mp hp).2
      exact inv_mul_cancel₀ (Real.log_pos (by exact_mod_cast hpp.one_lt)).ne'
    _ = _ := by simp

theorem inverse_log_weight_norm_le {a b : ℝ} (ha : 1 < a) (hab : a ≤ b)
    (hlog : 1 ≤ Real.log a) :
    b * |(Real.log b)⁻¹| + a * |(Real.log a)⁻¹| +
      (∫ t in a..b, t * |deriv (fun x ↦ (Real.log x)⁻¹) t|) ≤ 3 * b / Real.log a := by
  have hap : 0 < a := by linarith
  have hbp : 0 < b := hap.trans_le hab
  have hlap := Real.log_pos ha
  have hlbp := Real.log_pos (ha.trans_le hab)
  have hlogab := Real.log_le_log hap hab
  have hb : b * |(Real.log b)⁻¹| ≤ b * (Real.log a)⁻¹ := by
    rw [abs_of_pos (inv_pos.mpr hlbp)]
    exact mul_le_mul_of_nonneg_left (inv_anti₀ hlap hlogab) hbp.le
  have hderiv := (inverse_log_regular (b := b) ha).2
  have hi := intervalIntegral.integral_mono_on (μ := volume) hab
    (ContinuousOn.intervalIntegrable_of_Icc hab (continuousOn_id.mul hderiv.abs))
    (intervalIntegrable_const (c := (Real.log a)⁻¹)) (by
      intro t ht
      change t * |deriv (fun x ↦ (Real.log x)⁻¹) t| ≤ (Real.log a)⁻¹
      rw [inverse_log_weighted_derivative (ha.trans_le ht.1)]
      have hlt := Real.log_le_log hap ht.1
      apply inv_anti₀ hlap
      nlinarith)
  simp only [intervalIntegral.integral_const, smul_eq_mul] at hi
  dsimp only [Pi.mul_apply, id_eq] at hi
  rw [abs_of_pos (inv_pos.mpr hlap)]
  have hnonneg : 0 ≤ (Real.log a)⁻¹ := inv_nonneg.mpr hlap.le
  rw [div_eq_mul_inv]
  nlinarith

end Erdos421
