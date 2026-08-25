import ErdosProblems.Erdos964.ScalarCandidateSecondMain
import ErdosProblems.Erdos964.ScalarMomentBounds
import ErdosProblems.Erdos964.ScalarTransformPolynomial

/-!
# The polynomial model of the second scalar kernel
-/

namespace Erdos964

open BoundedGaps.Maynard

noncomputable def scalarPolynomialPrimeKernel (M R p : ℕ) : ℝ :=
  ∑ r ∈ Finset.Ico 1 R, scalarMomentAF M 2 r *
    (coprimeHarmonicDensity M *
      (scalarTransformPolynomial R r - scalarTransformPolynomial R (p * r))) ^ 2

theorem scalarCandidatePrimeKernel_eq_moment_sum (M R p : ℕ) :
    scalarCandidatePrimeKernel M R p =
      ∑ r ∈ Finset.Ico 1 R, if p ∣ r then 0 else scalarMomentAF M 2 r *
        (scalarSemiprimeTransform (scalarSievePrimeProduct M R) (scalarLinearY R) r -
          scalarSemiprimeTransform (scalarSievePrimeProduct M R)
            (scalarLinearY R) (p * r)) ^ 2 := by
  classical
  rw [scalarCandidatePrimeKernel, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro r hr
  rw [scalarMomentAF_two]
  by_cases h : Squarefree r ∧ r.Coprime M
  · simp only [if_pos h]
  · simp only [if_neg h, zero_mul, ite_self]

theorem scalarPolynomialPrimeKernel_nonneg (M R p : ℕ) (h2M : 2 ∣ M) (h3M : 3 ∣ M) :
    0 ≤ scalarPolynomialPrimeKernel M R p :=
  Finset.sum_nonneg (fun r _ => mul_nonneg (scalarMomentAF_nonneg M 2 r h2M h3M) (sq_nonneg _))

theorem scalarTransformPolynomial_difference_sq_le (M R r s : ℕ) (hR : 0 < Real.log R) :
    (coprimeHarmonicDensity M *
      (scalarTransformPolynomial R r - scalarTransformPolynomial R s)) ^ 2 ≤
      64 * coprimeHarmonicDensity M ^ 2 * (Real.log R) ^ 2 := by
  let δ := coprimeHarmonicDensity M
  have hδ : 0 ≤ δ := by dsimp [δ, coprimeHarmonicDensity]; positivity
  have hr := scalarTransformPolynomial_bounds R r hR
  have hs := scalarTransformPolynomial_bounds R s hR
  have hdiff : |scalarTransformPolynomial R r - scalarTransformPolynomial R s| ≤
      8 * Real.log R := by
    have h := abs_sub (scalarTransformPolynomial R r) (scalarTransformPolynomial R s)
    rw [abs_of_nonneg hr.1, abs_of_nonneg hs.1] at h
    linarith
  have hscaled : |δ * (scalarTransformPolynomial R r - scalarTransformPolynomial R s)| ≤
      8 * δ * Real.log R := by
    rw [abs_mul, abs_of_nonneg hδ]
    nlinarith [mul_le_mul_of_nonneg_left hdiff hδ]
  calc
    _ = |δ * (scalarTransformPolynomial R r - scalarTransformPolynomial R s)| ^ 2 := (sq_abs _).symm
    _ ≤ (8 * δ * Real.log R) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hscaled 2
    _ = _ := by dsimp only [δ]; ring

end Erdos964
