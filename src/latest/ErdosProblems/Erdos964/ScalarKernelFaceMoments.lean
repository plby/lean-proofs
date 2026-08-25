import ErdosProblems.Erdos964.ScalarKernelFaceSums

/-!
# The polynomial kernel in terms of logarithmic moments
-/

namespace Erdos964

open BoundedGaps.Maynard

noncomputable def scalarLargeLogMoment (M R Q : ℕ) : ℝ :=
  9 * scalarLogMoment M 2 R Q 4 - 42 * scalarLogMoment M 2 R Q 3 +
    73 * scalarLogMoment M 2 R Q 2 - 56 * scalarLogMoment M 2 R Q 1 +
    16 * scalarLogMoment M 2 R Q 0

noncomputable def scalarSmallLogMoment (M R Q : ℕ) (z : ℝ) : ℝ :=
  (36 * z ^ 2) * scalarLogMoment M 2 R Q 2 +
    (36 * z ^ 3 - 84 * z ^ 2) * scalarLogMoment M 2 R Q 1 +
    (9 * z ^ 4 - 42 * z ^ 3 + 49 * z ^ 2) * scalarLogMoment M 2 R Q 0

theorem sum_largeKernelPolynomial_eq_log_moments (M R Q : ℕ) :
    (∑ r ∈ Finset.Icc 0 Q, scalarMomentAF M 2 r *
      scalarLargeKernelPolynomial (Real.log r / Real.log R)) = scalarLargeLogMoment M R Q := by
  unfold scalarLargeLogMoment scalarLogMoment
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro r hr
  rw [scalarLargeKernelPolynomial_expand]
  simp only [normalizedLogMonomial_eq, pow_zero, pow_one]
  ring

theorem sum_smallKernelPolynomial_eq_log_moments (M R Q : ℕ) (z : ℝ) :
    (∑ r ∈ Finset.Icc 0 Q, scalarMomentAF M 2 r *
      scalarSmallKernelPolynomial z (Real.log r / Real.log R)) = scalarSmallLogMoment M R Q z := by
  unfold scalarSmallLogMoment scalarLogMoment
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro r hr
  rw [scalarSmallKernelPolynomial_expand]
  simp only [normalizedLogMonomial_eq, pow_zero, pow_one]
  ring

theorem scalarPolynomialPrimeKernel_eq_log_moments (M R p : ℕ) (hR : 1 ≤ R) (hp : 0 < p) :
    scalarPolynomialPrimeKernel M R p = coprimeHarmonicDensity M ^ 2 * (Real.log R) ^ 2 *
      (scalarLargeLogMoment M R (R - 1) +
        scalarSmallLogMoment M R ((R - 1) / p) (Real.log p / Real.log R) -
        scalarLargeLogMoment M R ((R - 1) / p)) := by
  have hdiff (Q : ℕ) :
      (∑ r ∈ Finset.Icc 0 Q, scalarMomentAF M 2 r *
        (scalarSmallKernelPolynomial (Real.log p / Real.log R) (Real.log r / Real.log R) -
          scalarLargeKernelPolynomial (Real.log r / Real.log R))) =
        scalarSmallLogMoment M R Q (Real.log p / Real.log R) - scalarLargeLogMoment M R Q := by
    simp_rw [mul_sub]
    rw [Finset.sum_sub_distrib, sum_smallKernelPolynomial_eq_log_moments,
      sum_largeKernelPolynomial_eq_log_moments]
  rw [scalarPolynomialPrimeKernel_eq_face_sums M R p hR hp,
    sum_largeKernelPolynomial_eq_log_moments, hdiff]
  ring

theorem scalarLogMoment_zero (M κ R j : ℕ) : scalarLogMoment M κ R 0 j = 0 := by
  simp only [scalarLogMoment, Finset.Icc_self, Finset.sum_singleton,
    ArithmeticFunction.map_zero, mul_zero]

theorem scalarPolynomialPrimeKernel_eq_large_of_radius (M R p : ℕ)
    (hR : 1 ≤ R) (hRp : R ≤ p) :
    scalarPolynomialPrimeKernel M R p = coprimeHarmonicDensity M ^ 2 * (Real.log R) ^ 2 *
      scalarLargeLogMoment M R (R - 1) := by
  have hp : 0 < p := hR.trans hRp
  rw [scalarPolynomialPrimeKernel_eq_log_moments M R p hR hp,
    Nat.div_eq_of_lt (show R - 1 < p by omega)]
  simp only [scalarSmallLogMoment, scalarLargeLogMoment, scalarLogMoment_zero,
    mul_zero, sub_zero, add_zero]

end Erdos964
