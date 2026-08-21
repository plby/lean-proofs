import ErdosProblems.Erdos239.External.Erdos67.MRGSA10SecondSecondaryChebyshevReduction
import ErdosProblems.Erdos239.External.Erdos67.MRGSA10GeneralizedMangoldtSplit

/-!
# Weighted-Chebyshev reduction for the prime part of the second A.10 secondary

The earlier weighted-Chebyshev reduction was phrased for a completely
multiplicative coefficient.  For an ordinary multiplicative coefficient,
the generalized Mangoldt coefficient still agrees with the expected
`a(p) log p` at primes.  We therefore apply weighted Chebyshev to that exact
prime part only.  The higher-prime-power part is handled separately by
`MRGSA10SecondSecondaryHigherPrimePower`.

The final theorem below preserves the source-critical factor
`X ^ (1 - alpha)` and leaves the two finite norm-Dirichlet masses explicit.
-/

namespace Erdos67.MRHalaszBands

noncomputable section

/-- The prime part of the actual high generalized Mangoldt coefficient is
pointwise dominated by the ordinary von Mangoldt function. -/
theorem norm_gsPrimePart_highGeneralizedMangoldt_le_vonMangoldt
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
    (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    (y n : ℕ) :
    ‖gsPrimePart (gsA9HighGeneralizedMangoldt hmul y) n‖ ≤
      ArithmeticFunction.vonMangoldt n := by
  rw [gsPrimePart_apply]
  split_ifs with hp
  · rw [gsA9HighGeneralizedMangoldt_apply_prime hmul y hp,
      norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.log_nonneg (by exact_mod_cast hp.one_lt.le)),
      ArithmeticFunction.vonMangoldt_apply_prime hp]
    apply mul_le_of_le_one_left
    · exact Real.log_nonneg (by exact_mod_cast hp.one_lt.le)
    · rw [gsA9HighArithmetic_apply_of_ne_zero f y hp.ne_zero]
      unfold gsA9High primeBandCoefficient
      split
      · exact hbound n hp.pos
      · simp
  · rw [norm_zero]
    exact ArithmeticFunction.vonMangoldt_nonneg

/-- Weighted Chebyshev for the exact prime part, valid for merely ordinary
multiplicative one-bounded coefficients. -/
theorem sum_norm_gsRealShift_primePart_highGeneralizedMangoldt_le
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
    (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    (y K : ℕ) {alpha : ℝ} (halpha0 : 0 ≤ alpha)
    (halphaHalf : alpha ≤ 1 / 2) :
    (∑ k ∈ Finset.Icc 1 K,
      ‖gsRealShift alpha
        (gsPrimePart (gsA9HighGeneralizedMangoldt hmul y)) k‖) ≤
      12 * (Real.log 4 + 4) * (K : ℝ) ^ (1 - alpha) := by
  by_cases hK : 2 ≤ K
  · calc
      _ ≤ ∑ k ∈ Finset.Icc 1 K,
            ArithmeticFunction.vonMangoldt k * (k : ℝ) ^ (-alpha) := by
        apply Finset.sum_le_sum
        intro k hk
        have hkpos : 0 < k := (Finset.mem_Icc.mp hk).1
        rw [gsRealShift_apply_of_ne_zero alpha _ hkpos.ne', norm_mul,
          Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (Real.exp_nonneg _)]
        have hexp : Real.exp (-alpha * Real.log (k : ℝ)) =
            (k : ℝ) ^ (-alpha) := by
          rw [Real.rpow_def_of_pos (by exact_mod_cast hkpos)]
          congr 1
          ring
        rw [hexp]
        simpa [mul_comm] using mul_le_mul_of_nonneg_right
          (norm_gsPrimePart_highGeneralizedMangoldt_le_vonMangoldt
            hmul hbound y k)
          (Real.rpow_nonneg (by positivity) (-alpha))
      _ ≤ _ := sum_vonMangoldt_mul_rpow_neg_le hK halpha0 halphaHalf
  · have hKle : K ≤ 1 := by omega
    have hzero : ∀ k ∈ Finset.Icc 1 K,
        ‖gsRealShift alpha
          (gsPrimePart (gsA9HighGeneralizedMangoldt hmul y)) k‖ = 0 := by
      intro k hk
      have hki := Finset.mem_Icc.mp hk
      have hk1 : k = 1 := by omega
      subst k
      simp [gsRealShift, gsPrimePart, gsA9HighGeneralizedMangoldt,
        gsGeneralizedMangoldt_one]
    rw [Finset.sum_eq_zero hzero]
    positivity

private theorem cast_div_rpow_le_mul_rpow_neg_prime
    {X d : ℕ} (hd : 0 < d) {sigma : ℝ} (hsigma : 0 ≤ sigma) :
    ((X / d : ℕ) : ℝ) ^ sigma ≤
      (X : ℝ) ^ sigma * (d : ℝ) ^ (-sigma) := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hcast : ((X / d : ℕ) : ℝ) ≤ (X : ℝ) / (d : ℝ) :=
    Nat.cast_div_le
  calc
    ((X / d : ℕ) : ℝ) ^ sigma ≤
        ((X : ℝ) / (d : ℝ)) ^ sigma :=
      Real.rpow_le_rpow (by positivity) hcast hsigma
    _ = (X : ℝ) ^ sigma / (d : ℝ) ^ sigma := by
      rw [Real.div_rpow (Nat.cast_nonneg X) hdR.le]
    _ = (X : ℝ) ^ sigma * (d : ℝ) ^ (-sigma) := by
      rw [Real.rpow_neg hdR.le]
      ring

/-- Source-shaped pointwise estimate for the prime part of the second A.10
secondary integrand.  It is the ordinary-multiplicative replacement for
`norm_positivePrefixSum_secondSecondaryIntegrand_le`. -/
theorem norm_positivePrefixSum_secondSecondaryPrimeIntegrand_le
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
    (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    (P₁ P₂ : ℕ → Prop) [DecidablePred P₁] [DecidablePred P₂]
    {y X : ℕ}
    {eta alpha : ℝ} (halpha0 : 0 ≤ alpha)
    (halphaHalf : alpha ≤ 1 / 2) (halphaOne : alpha ≤ 1) :
    ‖positivePrefixSum
        (fun n ↦ ((gsA10TwoBlockAlternatingLow f P₁ P₂ y *
            gsRealShift alpha
              (gsPrimePart (gsA9HighGeneralizedMangoldt hmul y))) *
          gsRealShift (2 * eta + alpha) (gsA9HighArithmetic f y)) n) X‖ ≤
      12 * (Real.log 4 + 4) * (X : ℝ) ^ (1 - alpha) *
        gsFiniteNormDirichletMass
          (gsA10TwoBlockAlternatingLow f P₁ P₂ y) X (1 - alpha) *
        gsFiniteNormDirichletMass
          (gsA9HighArithmetic f y) X (1 + 2 * eta) := by
  let low := gsA10TwoBlockAlternatingLow f P₁ P₂ y
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
      · exact cast_div_rpow_le_mul_rpow_neg_prime
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

end Erdos67.MRHalaszBands
