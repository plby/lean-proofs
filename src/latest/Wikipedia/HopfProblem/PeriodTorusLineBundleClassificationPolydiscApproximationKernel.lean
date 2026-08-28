import Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationPolydiscApproximationPolynomial
import Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationPolydiscApproximationGeometricProduct

/-!
# Uniform error of the actual finite boundary kernels

The finite monomial formula is identified pointwise with the two finite
geometric series.  Their proved scalar error estimate gives a supremum-norm
estimate in the actual Banach space of continuous boundary functions.
-/

noncomputable section

open Set Metric

namespace Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationPolydiscApproximation

open CuspNormalization.Germs.NormalIntegral

theorem partialBoundaryKernel_apply {R : ℝ} (hR : 0 < R)
    (u : C(BoundaryTorus R R, ℂ)) (N : ℕ) (z : ℂ × ℂ) (w : BoundaryTorus R R) :
    partialBoundaryKernel R u N z w =
      cauchyPartial N (w.1.1 : ℂ) z.1 * cauchyPartial N (w.2.1 : ℂ) z.2 * u w := by
  simp only [partialBoundaryKernel, ContinuousMap.sum_apply, ContinuousMap.smul_apply,
    coefficientBoundary_apply hR, smul_eq_mul, cauchyPartial,
    Finset.mul_sum, Finset.sum_mul]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  simp only [div_eq_mul_inv, mul_pow, pow_succ]
  ring

theorem closedBidisc_subset_openBidisc {r R : ℝ} (hrR : r < R) :
    closedBall (0 : ℂ) r ×ˢ closedBall (0 : ℂ) r ⊆
      ball (0 : ℂ) R ×ˢ ball (0 : ℂ) R := by
  intro z hz
  exact ⟨closedBall_subset_ball hrR hz.1, closedBall_subset_ball hrR hz.2⟩

/-- Uniform convergence of the geometric kernels in the actual supremum
norm, with one explicit bound valid for every point of the inner bidisc. -/
theorem partialBoundaryKernel_error_norm_le {r R : ℝ} (hr : 0 ≤ r) (hrR : r < R)
    (u : C(BoundaryTorus R R, ℂ)) (N : ℕ)
    {z : ℂ × ℂ} (hz : z ∈ closedBall 0 r ×ˢ closedBall 0 r) :
    ‖partialBoundaryKernel R u N z - boundaryKernel R R u z‖ ≤
      (3 * (r / R) ^ N / (R - r) ^ 2) * ‖u‖ := by
  have hR : 0 < R := lt_of_le_of_lt hr hrR
  have hz₁ : ‖z.1‖ ≤ r := by simpa only [mem_closedBall, dist_zero_right] using hz.1
  have hz₂ : ‖z.2‖ ≤ r := by simpa only [mem_closedBall, dist_zero_right] using hz.2
  have hbound : 0 ≤ 3 * (r / R) ^ N / (R - r) ^ 2 := by positivity
  apply (ContinuousMap.norm_le _ (mul_nonneg hbound (norm_nonneg u))).mpr
  intro w
  rw [ContinuousMap.sub_apply, partialBoundaryKernel_apply hR,
    boundaryKernel_apply u (closedBidisc_subset_openBidisc hrR hz), ← sub_mul, norm_mul,
    norm_sub_rev]
  apply mul_le_mul
    (cauchyProduct_error_norm_le N hr hrR (boundaryFirst_norm R w)
      (boundarySecond_norm R w) hz₁ hz₂)
    (u.norm_coe_le_norm w) (norm_nonneg _) hbound

end Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationPolydiscApproximation
