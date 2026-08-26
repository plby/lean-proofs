import ErdosProblems.Erdos421.PrimeWeightedDiscrepancy

/-! # A uniform error bound for weighted prime sums -/

namespace Erdos421

open MeasureTheory

theorem prime_log_weighted_error_le {f : ℝ → ℝ} {a b E : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b)
    (hf : ∀ t ∈ Set.Icc a b, DifferentiableAt ℝ f t)
    (hf' : ContinuousOn (deriv f) (Set.Icc a b))
    (hθ : ∀ t ∈ Set.Icc a b, |Chebyshev.theta t - t| ≤ E * t) :
    |(∑ p ∈ primesInRealInterval a b, f p * Real.log p) - (∫ t in a..b, f t)| ≤
      E * (b * |f b| + a * |f a| + ∫ t in a..b, t * |deriv f t|) := by
  have hei : IntervalIntegrable (fun t ↦ deriv f t * (Chebyshev.theta t - t)) volume a b :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hab).mpr
      (integrableOn_deriv_mul_theta_error ha hf')
  have hright : ContinuousOn (fun t ↦ E * (t * |deriv f t|)) (Set.Icc a b) :=
    continuousOn_const.mul (continuousOn_id.mul hf'.abs)
  have hm := intervalIntegral.integral_mono_on (μ := volume) hab hei.abs
    (ContinuousOn.intervalIntegrable_of_Icc hab hright) (by
      intro t ht
      rw [abs_mul]
      calc
        _ ≤ |deriv f t| * (E * t) := mul_le_mul_of_nonneg_left (hθ t ht) (abs_nonneg _)
        _ = _ := by ring)
  rw [intervalIntegral.integral_const_mul] at hm
  have hi : |∫ t in a..b, deriv f t * (Chebyshev.theta t - t)| ≤
      E * ∫ t in a..b, t * |deriv f t| :=
    (intervalIntegral.abs_integral_le_integral_abs hab).trans hm
  have hb := mul_le_mul_of_nonneg_left (hθ b ⟨hab, le_rfl⟩) (abs_nonneg (f b))
  have ha' := mul_le_mul_of_nonneg_left (hθ a ⟨le_rfl, hab⟩) (abs_nonneg (f a))
  rw [prime_weighted_discrepancy_eq ha hab hf hf']
  calc
    _ ≤ |f b * (Chebyshev.theta b - b)| + |f a * (Chebyshev.theta a - a)| +
        |∫ t in a..b, deriv f t * (Chebyshev.theta t - t)| :=
      (abs_sub _ _).trans (add_le_add (abs_sub _ _) le_rfl)
    _ ≤ |f b| * (E * b) + |f a| * (E * a) + E * ∫ t in a..b, t * |deriv f t| := by
      rw [abs_mul, abs_mul]
      exact add_le_add (add_le_add hb ha') hi
    _ = _ := by ring

end Erdos421
