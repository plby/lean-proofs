import ErdosProblems.Erdos421.PrimeAbelSummation
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-! # Exact weighted prime discrepancy and its integrability -/

namespace Erdos421

open MeasureTheory

theorem integrableOn_deriv_mul_theta_error {f : ℝ → ℝ} {a b : ℝ} (ha : 0 ≤ a)
    (hf' : ContinuousOn (deriv f) (Set.Icc a b)) :
    IntegrableOn (fun t ↦ deriv f t * (Chebyshev.theta t - t)) (Set.Icc a b) := by
  have hi := (integrableOn_deriv_mul_theta ha hf'.integrableOn_Icc).sub
    (hf'.mul continuousOn_id).integrableOn_Icc
  change IntegrableOn (fun t ↦ deriv f t * Chebyshev.theta t - deriv f t * t)
    (Set.Icc a b) at hi
  simpa only [mul_sub] using hi

theorem prime_weighted_discrepancy_eq {f : ℝ → ℝ} {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b)
    (hf : ∀ t ∈ Set.Icc a b, DifferentiableAt ℝ f t)
    (hf' : ContinuousOn (deriv f) (Set.Icc a b)) :
    (∑ p ∈ primesInRealInterval a b, f p * Real.log p) - (∫ t in a..b, f t) =
      f b * (Chebyshev.theta b - b) - f a * (Chebyshev.theta a - a) -
        ∫ t in a..b, deriv f t * (Chebyshev.theta t - t) := by
  have hfc : ContinuousOn f (Set.Icc a b) :=
    fun t ht ↦ (hf t ht).continuousAt.continuousWithinAt
  have hfi : IntervalIntegrable f volume a b :=
    ContinuousOn.intervalIntegrable_of_Icc hab hfc
  have hfdi : IntervalIntegrable (deriv f) volume a b :=
    ContinuousOn.intervalIntegrable_of_Icc hab hf'
  have hfdti : IntervalIntegrable (fun t ↦ deriv f t * t) volume a b :=
    ContinuousOn.intervalIntegrable_of_Icc hab (hf'.mul continuousOn_id)
  have hthet : IntervalIntegrable (fun t ↦ deriv f t * Chebyshev.theta t) volume a b :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hab).mpr
      (integrableOn_deriv_mul_theta ha hf'.integrableOn_Icc)
  have hftc := intervalIntegral.integral_deriv_mul_eq_sub_of_hasDerivAt
    (u := f) (v := fun t : ℝ ↦ t) (u' := deriv f) (v' := fun _ ↦ (1 : ℝ))
    (by simpa only [Set.uIcc_of_le hab] using hfc) continuousOn_id
    (by
      intro t ht
      rw [min_eq_left hab, max_eq_right hab] at ht
      exact (hf t ⟨ht.1.le, ht.2.le⟩).hasDerivAt)
    (fun t _ ↦ hasDerivAt_id t) hfdi intervalIntegrable_const
  simp only [mul_one] at hftc
  rw [intervalIntegral.integral_add hfdti hfi] at hftc
  have hmain : (∫ t in a..b, f t) = f b * b - f a * a - ∫ t in a..b, deriv f t * t := by
    linarith only [hftc]
  have heq : (∫ t in a..b, deriv f t * (Chebyshev.theta t - t)) =
      (∫ t in a..b, deriv f t * Chebyshev.theta t) - (∫ t in a..b, deriv f t * t) := by
    simp_rw [mul_sub]
    exact intervalIntegral.integral_sub hthet hfdti
  rw [prime_log_weighted_sum_eq ha hab hf hf'.integrableOn_Icc, hmain, heq]
  ring

end Erdos421
