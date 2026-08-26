import ErdosProblems.Erdos4.ProjectionNormals

/-!
# A summable local comparison of the two projections

The exact divisor factors turn the difference of the true and ideal local
matrices into an `O(k^2 / ell^2)` error. This estimate is specific to the
coefficient slices and does not assert a false unweighted operator bound.
-/

open scoped BigOperators

namespace Erdos4.LocalProjectionComparison

open ProjectionNormals LocalFourier

theorem weightedSize_nonneg {A : Type*} [Fintype A] (c u : A → ℝ) (hc : ∀ a, 0 ≤ c a) :
    0 ≤ weightedSize c u :=
  Finset.sum_nonneg (fun a _ha => mul_nonneg (abs_nonneg _) (hc a))

theorem weighted_cross_eq {A : Type*} [Fintype A] (c u v : A → ℝ) :
    (∑ a, ∑ b, |u a| * |v b| * c a * c b) = weightedSize c u * weightedSize c v := by
  unfold weightedSize
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro a _ha
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl (fun b _hb => by ring)

theorem kernel_difference_weighted_le {A : Type*} [Fintype A] [DecidableEq A]
    (c u v : A → ℝ) (hc : ∀ a, 0 ≤ c a) :
    weightedMatrixNorm c (fun a b =>
      ((ProjectionKernel.kernel u a b - ProjectionKernel.kernel v a b : ℝ) : ℂ)) ≤
        weightedSize c (fun a => u a - v a) * (weightedSize c u + weightedSize c v) := by
  have hpoint (a b : A) : |ProjectionKernel.kernel u a b - ProjectionKernel.kernel v a b| ≤
      |u a - v a| * |u b| + |v a| * |u b - v b| := by
    have heq : ProjectionKernel.kernel u a b - ProjectionKernel.kernel v a b =
        -((u a - v a) * u b + v a * (u b - v b)) := by
      unfold ProjectionKernel.kernel
      ring
    rw [heq, abs_neg]
    simpa only [abs_mul] using abs_add_le ((u a - v a) * u b) (v a * (u b - v b))
  unfold weightedMatrixNorm
  simp only [Complex.norm_real, Real.norm_eq_abs]
  calc
    (∑ a, ∑ b, |ProjectionKernel.kernel u a b - ProjectionKernel.kernel v a b| * c a * c b) ≤
        ∑ a, ∑ b, (|u a - v a| * |u b| + |v a| * |u b - v b|) * c a * c b := by
      apply Finset.sum_le_sum
      intro a _ha
      apply Finset.sum_le_sum
      intro b _hb
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (hpoint a b) (hc a)) (hc b)
    _ = weightedSize c (fun a => u a - v a) * weightedSize c u +
        weightedSize c v * weightedSize c (fun a => u a - v a) := by
      simp only [add_mul, Finset.sum_add_distrib]
      rw [weighted_cross_eq, weighted_cross_eq]
    _ = _ := by ring

/-- A bound with a convergent reciprocal-square prime tail. -/
theorem local_comparison_le {k ell : ℕ} (hell : k + 2 ≤ ell) (j : Fin k) :
    weightedMatrixNorm (DivisorCoefficients.localWeight ell) (fun a b =>
      ((ProjectionKernel.kernel (trueNormal (ell : ℝ) j) a b - IdealProjection.kernel (ell : ℝ) j a b : ℝ) : ℂ)) ≤
        10 * (k : ℝ) ^ 2 / (ell : ℝ) ^ 2 := by
  have hk : (1 : ℝ) ≤ k := by
    have hn : 1 ≤ k := by have := j.isLt; omega
    exact_mod_cast hn
  have he : 0 < (ell : ℝ) := by exact_mod_cast (show 0 < ell by omega)
  have hs : 0 < Real.sqrt (ell : ℝ) := Real.sqrt_pos.mpr he
  have hsum : weightedSize (DivisorCoefficients.localWeight ell) (trueNormal (ell : ℝ) j) +
      weightedSize (DivisorCoefficients.localWeight ell) (IdealProjection.normal (ell : ℝ) j) ≤
        5 * k / Real.sqrt (ell : ℝ) := by
    rw [idealNormal_weightedSize (by omega) j]
    have hh := add_le_add (trueNormal_weightedSize_le hell j)
      (le_refl (2 / Real.sqrt (ell : ℝ)))
    have hnum : (1 + 2 * (k : ℝ)) / Real.sqrt (ell : ℝ) + 2 / Real.sqrt (ell : ℝ) ≤
        5 * k / Real.sqrt (ell : ℝ) := by
      rw [← add_div]
      exact div_le_div_of_nonneg_right (by linarith) hs.le
    exact hh.trans hnum
  have hprod := mul_le_mul (normal_difference_weightedSize_le hell j) hsum
    (add_nonneg (weightedSize_nonneg _ _ (DivisorCoefficients.localWeight_nonneg ell))
      (weightedSize_nonneg _ _ (DivisorCoefficients.localWeight_nonneg ell)))
    (show (0 : ℝ) ≤ 2 * k / ((ell : ℝ) * Real.sqrt (ell : ℝ)) by positivity)
  have hscalar : (2 * (k : ℝ) / ((ell : ℝ) * Real.sqrt (ell : ℝ))) *
      (5 * k / Real.sqrt (ell : ℝ)) = 10 * (k : ℝ) ^ 2 / (ell : ℝ) ^ 2 := by
    calc
      _ = 10 * (k : ℝ) ^ 2 / ((ell : ℝ) * (Real.sqrt (ell : ℝ) * Real.sqrt (ell : ℝ))) := by ring
      _ = _ := by rw [Real.mul_self_sqrt he.le]; ring
  rw [hscalar] at hprod
  exact (kernel_difference_weighted_le (DivisorCoefficients.localWeight ell)
    (trueNormal (ell : ℝ) j) (IdealProjection.normal (ell : ℝ) j)
    (DivisorCoefficients.localWeight_nonneg ell)).trans hprod

end Erdos4.LocalProjectionComparison
