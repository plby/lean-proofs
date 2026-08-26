import ErdosProblems.Erdos67b.MRGSA10SecondSecondaryPrimeChebyshev

/-!
# Distinguished-prime estimate with an arbitrary low coefficient

The finite Chebyshev convolution argument does not require any special
form of the low arithmetic function. Its actual finite mass is retained.
-/

open scoped BigOperators

namespace Erdos67b

open MRHalaszBands

noncomputable section

theorem mrCast_div_rpow_le_mul_rpow_neg
    {X d : ℕ} (hd : 0 < d) {sigma : ℝ} (hsigma : 0 ≤ sigma) :
    ((X / d : ℕ) : ℝ) ^ sigma ≤ (X : ℝ) ^ sigma * (d : ℝ) ^ (-sigma) := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  calc
    _ ≤ ((X : ℝ) / (d : ℝ)) ^ sigma :=
      Real.rpow_le_rpow (by positivity) Nat.cast_div_le hsigma
    _ = (X : ℝ) ^ sigma / (d : ℝ) ^ sigma := by
      rw [Real.div_rpow (Nat.cast_nonneg X) hdR.le]
    _ = _ := by rw [Real.rpow_neg hdR.le]; ring

theorem mrNorm_positivePrefix_secondSecondaryPrimeIntegrand_le
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
    (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    (low : ArithmeticFunction ℂ)
    {y X : ℕ}
    {eta alpha : ℝ} (halpha0 : 0 ≤ alpha)
    (halphaHalf : alpha ≤ 1 / 2) (halphaOne : alpha ≤ 1) :
    ‖positivePrefixSum
        (fun n ↦ ((low *
            gsRealShift alpha
              (gsPrimePart (gsA9HighGeneralizedMangoldt hmul y))) *
          gsRealShift (2 * eta + alpha) (gsA9HighArithmetic f y)) n) X‖ ≤
      12 * (Real.log 4 + 4) * (X : ℝ) ^ (1 - alpha) *
        gsFiniteNormDirichletMass
          (low) X (1 - alpha) *
        gsFiniteNormDirichletMass
          (gsA9HighArithmetic f y) X (1 + 2 * eta) := by
  let lambda := gsPrimePart (gsA9HighGeneralizedMangoldt hmul y)
  let high := gsA9HighArithmetic f y
  let lambdaShift := gsRealShift alpha lambda
  let highShift := gsRealShift (2 * eta + alpha) high
  let C : ℝ := 12 * (Real.log 4 + 4)
  have hsigma : 0 ≤ 1 - alpha := sub_nonneg.mpr halphaOne
  have hreorder : (low * lambdaShift) * highShift =
      (low * highShift) * lambdaShift := by ring
  rw [show (fun n ↦ ((low * lambdaShift) * highShift) n) =
      (fun n ↦ ((low * highShift) * lambdaShift) n) by rw [hreorder]]
  have hcut := norm_positivePrefixSum_mul_le_cutoff
    (low * highShift) lambdaShift X
  refine hcut.trans ?_
  calc
    (∑ d ∈ Finset.Icc 1 X, ‖(low * highShift) d‖ *
        ∑ k ∈ Finset.Icc 1 (X / d), ‖lambdaShift k‖) ≤
        ∑ d ∈ Finset.Icc 1 X, ‖(low * highShift) d‖ *
          (C * ((X / d : ℕ) : ℝ) ^ (1 - alpha)) := by
      apply Finset.sum_le_sum
      intro d hd
      apply mul_le_mul_of_nonneg_left
      · exact sum_norm_gsRealShift_primePart_highGeneralizedMangoldt_le
          hmul hbound y (X / d) halpha0 halphaHalf
      · exact norm_nonneg _
    _ ≤ ∑ d ∈ Finset.Icc 1 X, ‖(low * highShift) d‖ *
          (C * ((X : ℝ) ^ (1 - alpha) *
            (d : ℝ) ^ (-(1 - alpha)))) := by
      apply Finset.sum_le_sum
      intro d hd
      apply mul_le_mul_of_nonneg_left
      apply mul_le_mul_of_nonneg_left
      · exact mrCast_div_rpow_le_mul_rpow_neg
          (Finset.mem_Icc.mp hd).1 hsigma
      · positivity
      · exact norm_nonneg _
    _ = C * (X : ℝ) ^ (1 - alpha) *
        gsFiniteNormDirichletMass (low * highShift) X (1 - alpha) := by
      unfold gsFiniteNormDirichletMass
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro d hd
      ring
    _ ≤ C * (X : ℝ) ^ (1 - alpha) *
        (gsFiniteNormDirichletMass low X (1 - alpha) *
          gsFiniteNormDirichletMass highShift X (1 - alpha)) := by
      apply mul_le_mul_of_nonneg_left
      · exact gsFiniteNormDirichletMass_mul_le low highShift X hsigma
      · positivity
    _ = C * (X : ℝ) ^ (1 - alpha) *
        gsFiniteNormDirichletMass low X (1 - alpha) *
          gsFiniteNormDirichletMass high X (1 + 2 * eta) := by
      rw [gsFiniteNormDirichletMass_gsRealShift]
      rw [show 1 - alpha + (2 * eta + alpha) = 1 + 2 * eta by ring]
      ring


end

end Erdos67b
