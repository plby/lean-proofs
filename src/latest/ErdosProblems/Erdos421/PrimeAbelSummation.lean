import ErdosProblems.Erdos421.PrimeLongIntervals
import ErdosProblems.Erdos421.PrimeLogHarmonic
import Mathlib.NumberTheory.AbelSummation

/-! # Abel summation for actual finite weighted prime sums -/

namespace Erdos421

open MeasureTheory

theorem sum_primeLogCoefficient_floor (x : ℝ) :
    (∑ n ∈ Finset.Icc 0 ⌊x⌋₊, primeLogCoefficient n) = Chebyshev.theta x := by
  rw [Chebyshev.theta_eq_sum_Icc, Finset.sum_filter]
  rfl

theorem prime_log_weighted_sum_eq {f : ℝ → ℝ} {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b)
    (hf : ∀ t ∈ Set.Icc a b, DifferentiableAt ℝ f t)
    (hf' : IntegrableOn (deriv f) (Set.Icc a b)) :
    (∑ p ∈ primesInRealInterval a b, f p * Real.log p) =
      f b * Chebyshev.theta b - f a * Chebyshev.theta a -
        ∫ t in a..b, deriv f t * Chebyshev.theta t := by
  have h := sum_mul_eq_sub_sub_integral_mul primeLogCoefficient ha hab hf hf'
  simp_rw [sum_primeLogCoefficient_floor] at h
  rw [← intervalIntegral.integral_of_le hab] at h
  simpa only [primesInRealInterval, Finset.sum_filter, primeLogCoefficient,
    mul_ite, mul_zero] using h

theorem integrableOn_deriv_mul_theta {f : ℝ → ℝ} {a b : ℝ} (ha : 0 ≤ a)
    (hf' : IntegrableOn (deriv f) (Set.Icc a b)) :
    IntegrableOn (fun t ↦ deriv f t * Chebyshev.theta t) (Set.Icc a b) := by
  have h := integrableOn_mul_sum_Icc primeLogCoefficient (m := 0) ha hf'
  simpa only [sum_primeLogCoefficient_floor] using h

end Erdos421
