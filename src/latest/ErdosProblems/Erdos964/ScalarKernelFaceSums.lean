import ErdosProblems.Erdos964.ScalarKernelFaces

/-!
# Exact full-prefix decomposition of the polynomial kernel

The large face is summed up to `R-1`; the small-minus-large correction is
summed up to `(R-1)/p`. Both sums include zero with zero arithmetic weight.
-/

namespace Erdos964

open BoundedGaps.Maynard

theorem sum_Ico_eq_Icc_pred_of_zero (R : ℕ) (hR : 1 ≤ R) (F : ℕ → ℝ) (hF : F 0 = 0) :
    (∑ r ∈ Finset.Ico 1 R, F r) = ∑ r ∈ Finset.Icc 0 (R - 1), F r := by
  have h := sum_Ico_if_mul_lt_radius R 1 hR (by decide) F hF
  have heq : (∑ r ∈ Finset.Ico 1 R, if 1 * r < R then F r else 0) =
      ∑ r ∈ Finset.Ico 1 R, F r := by
    apply Finset.sum_congr rfl
    intro r hr
    rw [one_mul, if_pos (Finset.mem_Ico.mp hr).2]
  simpa only [heq, Nat.div_one] using h

theorem scalarPolynomialPrimeKernel_eq_face_sums (M R p : ℕ) (hR : 1 ≤ R) (hp : 0 < p) :
    scalarPolynomialPrimeKernel M R p =
      coprimeHarmonicDensity M ^ 2 * (Real.log R) ^ 2 *
        ((∑ r ∈ Finset.Icc 0 (R - 1), scalarMomentAF M 2 r *
            scalarLargeKernelPolynomial (Real.log r / Real.log R)) +
          ∑ r ∈ Finset.Icc 0 ((R - 1) / p), scalarMomentAF M 2 r *
            (scalarSmallKernelPolynomial (Real.log p / Real.log R) (Real.log r / Real.log R) -
              scalarLargeKernelPolynomial (Real.log r / Real.log R))) := by
  let δ := coprimeHarmonicDensity M
  let L := Real.log R
  let z := Real.log p / L
  let v : ℕ → ℝ := fun r => Real.log r / L
  let K := δ ^ 2 * L ^ 2
  let F : ℕ → ℝ := fun r => scalarMomentAF M 2 r * scalarLargeKernelPolynomial (v r)
  let G : ℕ → ℝ := fun r => scalarMomentAF M 2 r *
    (scalarSmallKernelPolynomial z (v r) - scalarLargeKernelPolynomial (v r))
  have hF : F 0 = 0 := by dsimp only [F]; rw [ArithmeticFunction.map_zero, zero_mul]
  have hG : G 0 = 0 := by dsimp only [G]; rw [ArithmeticFunction.map_zero, zero_mul]
  have hpoint (r : ℕ) (hr : r ∈ Finset.Ico 1 R) :
      scalarMomentAF M 2 r *
        (δ * (scalarTransformPolynomial R r - scalarTransformPolynomial R (p * r))) ^ 2 =
        K * (F r + if p * r < R then G r else 0) := by
    obtain ⟨hr0, hrR⟩ := Finset.mem_Ico.mp hr
    by_cases hpr : p * r < R
    · rw [if_pos hpr, scalarTransformPolynomial_difference_small R p r hp hr0 hrR hpr]
      dsimp only [K, F, G, v, z, L, scalarSmallKernelPolynomial, scalarLargeKernelPolynomial]
      ring
    · rw [if_neg hpr, add_zero,
        scalarTransformPolynomial_difference_large R p r hr0 hrR (Nat.le_of_not_gt hpr)]
      dsimp only [K, F, v, L, scalarLargeKernelPolynomial]
      ring
  unfold scalarPolynomialPrimeKernel
  calc
    _ = ∑ r ∈ Finset.Ico 1 R, K * (F r + if p * r < R then G r else 0) :=
      Finset.sum_congr rfl hpoint
    _ = K * ((∑ r ∈ Finset.Ico 1 R, F r) +
        (∑ r ∈ Finset.Ico 1 R, if p * r < R then G r else 0)) := by
      rw [← Finset.mul_sum, Finset.sum_add_distrib]
    _ = K * ((∑ r ∈ Finset.Icc 0 (R - 1), F r) +
        ∑ r ∈ Finset.Icc 0 ((R - 1) / p), G r) := by
      rw [sum_Ico_eq_Icc_pred_of_zero R hR F hF, sum_Ico_if_mul_lt_radius R p hR hp G hG]
    _ = _ := rfl

end Erdos964
