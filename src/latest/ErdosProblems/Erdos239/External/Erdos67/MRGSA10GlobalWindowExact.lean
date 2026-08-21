import ErdosProblems.Erdos239.External.Erdos67.MRGSA10LambdaWindowExact
import ErdosProblems.Erdos239.External.Erdos67.MRGSA10GlobalSecondary

/-!
# Exactness of the global-to-windowed A.10 coefficient

The full A.10 coefficient contains two copies of the high generalized
Mangoldt factor.  Since every nonzero index of that factor is strictly
larger than `y`, a product contributing below `X` forces both indices into
the finite window `y < n < X / y`.  Thus the third term in the packaged
global secondary error vanishes exactly.
-/

namespace Erdos67.MRHalaszBands

noncomputable section

/-- Two factors strictly above `y` whose product is at most `X` both lie
strictly below `X / y`. -/
theorem lt_div_of_both_gt_of_mul_le
    {y a b X : ℕ} (hy : 0 < y) (ha : y < a) (hb : y < b)
    (hab : a * b ≤ X) :
    a < X / y ∧ b < X / y := by
  constructor
  · rw [Nat.lt_iff_add_one_le, Nat.le_div_iff_mul_le hy]
    calc
      (a + 1) * y = a * y + y := by simp [Nat.add_mul]
      _ ≤ a * y + a := Nat.add_le_add_left ha.le _
      _ = a * (y + 1) := by simp [Nat.mul_add]
      _ ≤ a * b := Nat.mul_le_mul_left a (Nat.succ_le_iff.2 hb)
      _ ≤ X := hab
  · rw [Nat.lt_iff_add_one_le, Nat.le_div_iff_mul_le hy]
    calc
      (b + 1) * y = b * y + y := by simp [Nat.add_mul]
      _ ≤ b * y + b := Nat.add_le_add_left hb.le _
      _ = b * (y + 1) := by simp [Nat.mul_add]
      _ ≤ b * a := Nat.mul_le_mul_left b (Nat.succ_le_iff.2 ha)
      _ = a * b := Nat.mul_comm _ _
      _ ≤ X := hab

/-- At every coefficient below `X`, the full and tailored four-factor A.10
coefficients agree whenever the generalized-Mangoldt factor is supported
strictly above `y`. -/
theorem gsA10FullCoefficient_apply_eq_tailored_of_lambda_support
    (low high lambda : ArithmeticFunction ℂ)
    {y X n : ℕ} (hy : 0 < y) (hn : 0 < n) (hnX : n ≤ X)
    (hlambda : ∀ k, lambda k ≠ 0 → y < k)
    (alpha beta : ℝ) :
    gsA10FullCoefficient low high lambda alpha beta n =
      gsA10TailoredCoefficient low high lambda y X alpha beta n := by
  rw [gsA10FullCoefficient, gsA10TailoredCoefficient,
    ArithmeticFunction.mul_apply, ArithmeticFunction.mul_apply]
  apply Finset.sum_congr rfl
  intro uv huv
  congr 1
  rw [ArithmeticFunction.mul_apply, ArithmeticFunction.mul_apply]
  apply Finset.sum_congr rfl
  intro cd hcd
  have hcdprod := (Nat.mem_divisorsAntidiagonal.mp hcd).1
  have hcd1 : cd.1 ≠ 0 :=
    (Nat.ne_zero_of_mem_divisorsAntidiagonal hcd).1
  have hcd2 : cd.2 ≠ 0 :=
    (Nat.ne_zero_of_mem_divisorsAntidiagonal hcd).2
  rw [gsRealShift_apply_of_ne_zero alpha lambda hcd1,
    gsRealShift_apply_of_ne_zero (alpha + 2 * beta) lambda hcd2,
    gsRealShift_apply_of_ne_zero alpha (gsA10LambdaWindow lambda y X) hcd1,
    gsRealShift_apply_of_ne_zero (alpha + 2 * beta)
      (gsA10LambdaWindow lambda y X) hcd2]
  by_cases hc : lambda cd.1 = 0
  · simp [gsA10LambdaWindow, hc]
  by_cases hd : lambda cd.2 = 0
  · simp [gsA10LambdaWindow, hd]
  have hcgt : y < cd.1 := hlambda cd.1 hc
  have hdgt : y < cd.2 := hlambda cd.2 hd
  have huv2le : uv.2 ≤ n := divisorsAntidiagonal_snd_le hn huv
  have hprodle : cd.1 * cd.2 ≤ X := by
    rw [hcdprod]
    exact huv2le.trans hnX
  obtain ⟨hclt, hdlt⟩ :=
    lt_div_of_both_gt_of_mul_le hy hcgt hdgt hprodle
  simp [gsA10LambdaWindow, hcgt, hdgt, hclt, hdlt]

/-- The corresponding positive prefixes agree exactly. -/
theorem positivePrefixSum_gsA10FullCoefficient_eq_tailored_of_lambda_support
    (low high lambda : ArithmeticFunction ℂ)
    {y X : ℕ} (hy : 0 < y)
    (hlambda : ∀ k, lambda k ≠ 0 → y < k)
    (alpha beta : ℝ) :
    positivePrefixSum
        (gsA10FullCoefficient low high lambda alpha beta) X =
      positivePrefixSum
        (gsA10TailoredCoefficient low high lambda y X alpha beta) X := by
  unfold positivePrefixSum
  simp only [ArithmeticFunction.map_zero, sub_zero]
  apply Finset.sum_congr rfl
  intro n hnmem
  have hnle : n ≤ X := by
    simpa only [Finset.mem_range, Nat.lt_succ_iff] using hnmem
  by_cases hn0 : n = 0
  · subst n
    simp
  exact gsA10FullCoefficient_apply_eq_tailored_of_lambda_support
    low high lambda hy (Nat.pos_of_ne_zero hn0) hnle hlambda alpha beta

/-- Hence the full and tailored rectangular auxiliary averages agree. -/
theorem gsA10FullIntegratedPrefix_eq_tailored_of_lambda_support
    (low high lambda : ArithmeticFunction ℂ)
    {y X : ℕ} (hy : 0 < y)
    (hlambda : ∀ k, lambda k ≠ 0 → y < k)
    (eta : ℝ) :
    gsA10FullIntegratedPrefix low high lambda X eta =
      gsA10TailoredIntegratedPrefix low high lambda y X eta := by
  unfold gsA10FullIntegratedPrefix gsA10TailoredIntegratedPrefix
  apply congrArg (fun z : ℂ ↦ 2 * z)
  apply intervalIntegral.integral_congr
  intro alpha _halpha
  apply intervalIntegral.integral_congr
  intro beta _hbeta
  exact positivePrefixSum_gsA10FullCoefficient_eq_tailored_of_lambda_support
    low high lambda hy hlambda alpha beta

/-- Specialization to the actual high generalized-Mangoldt coefficient. -/
theorem gsA10TwoBlockFullIntegratedPrefix_eq_tailored
    {f : ℕ → ℂ}
    (hmul : IsMultiplicativeOnPositiveNat f)
    (P₁ P₂ : ℕ → Prop) [DecidablePred P₁] [DecidablePred P₂]
    {y X : ℕ} (hy : 0 < y) (eta : ℝ) :
    gsA10FullIntegratedPrefix
        (gsA10TwoBlockAlternatingLow f P₁ P₂ y)
        (gsA9HighArithmetic f y)
        (gsA9HighGeneralizedMangoldt hmul y) X eta =
      gsA10TwoBlockTailoredIntegratedPrefix
        f hmul P₁ P₂ y X eta := by
  apply gsA10FullIntegratedPrefix_eq_tailored_of_lambda_support
  · exact hy
  · intro k hk
    by_contra hky
    exact hk (gsA9HighGeneralizedMangoldt_eq_zero_of_le
      hmul y (not_lt.mp hky))

/-- The full-to-windowed summand in the specialized global secondary error
is exactly zero. -/
theorem norm_gsA10TwoBlock_full_sub_tailored_eq_zero
    {f : ℕ → ℂ}
    (hmul : IsMultiplicativeOnPositiveNat f)
    (P₁ P₂ : ℕ → Prop) [DecidablePred P₁] [DecidablePred P₂]
    {y X : ℕ} (hy : 0 < y) (eta : ℝ) :
    ‖gsA10FullIntegratedPrefix
          (gsA10TwoBlockAlternatingLow f P₁ P₂ y)
          (gsA9HighArithmetic f y)
          (gsA9HighGeneralizedMangoldt hmul y) X eta -
        gsA10TwoBlockTailoredIntegratedPrefix
          f hmul P₁ P₂ y X eta‖ = 0 := by
  rw [gsA10TwoBlockFullIntegratedPrefix_eq_tailored
    hmul P₁ P₂ hy eta, sub_self, norm_zero]

/-- After exact windowing, the packaged global secondary error consists
only of the two genuine source secondary prefixes. -/
theorem gsA10TwoBlockGlobalSecondaryError_eq_two_secondaries
    {f : ℕ → ℂ}
    (hmul : IsMultiplicativeOnPositiveNat f)
    (P₁ P₂ : ℕ → Prop) [DecidablePred P₁] [DecidablePred P₂]
    {y X : ℕ} (hy : 0 < y) (eta : ℝ) :
    gsA10TwoBlockGlobalSecondaryError f hmul P₁ P₂ y X eta =
      ‖gsA10FirstSecondaryPrefix
          (gsA10TwoBlockAlternatingLow f P₁ P₂ y)
          (gsA9HighArithmetic f y) X eta‖ +
      ‖gsA10SecondSecondaryPrefix
          (gsA10TwoBlockAlternatingLow f P₁ P₂ y)
          (gsA9HighArithmetic f y)
          (gsA9HighGeneralizedMangoldt hmul y) X eta‖ := by
  have htail :
      gsA10FullIntegratedPrefix
          (gsA10TwoBlockAlternatingLow f P₁ P₂ y)
          (gsA9HighArithmetic f y)
          (gsA9HighGeneralizedMangoldt hmul y) X eta =
        gsA10TailoredIntegratedPrefix
          (gsA10TwoBlockAlternatingLow f P₁ P₂ y)
          (gsA9HighArithmetic f y)
          (gsA9HighGeneralizedMangoldt hmul y) y X eta := by
    apply gsA10FullIntegratedPrefix_eq_tailored_of_lambda_support
    · exact hy
    · intro k hk
      by_contra hky
      exact hk (gsA9HighGeneralizedMangoldt_eq_zero_of_le
        hmul y (not_lt.mp hky))
  unfold gsA10TwoBlockGlobalSecondaryError gsA10GlobalSecondaryError
  rw [htail, sub_self, norm_zero]
  ring

/-- Source-ready reconstruction with the full-to-window term eliminated
exactly; only the two finite secondary prefixes remain to estimate. -/
theorem norm_positivePrefixSum_gsA10TwoBlockReconstructed_sub_tailored_le_two_secondaries
    {f : ℕ → ℂ}
    (hmul : IsMultiplicativeOnPositiveNat f)
    (P₁ P₂ : ℕ → Prop) [DecidablePred P₁] [DecidablePred P₂]
    {y X : ℕ} (hy : 0 < y) (eta : ℝ) :
    ‖positivePrefixSum
          (gsA10TwoBlockReconstructedCoefficient f P₁ P₂ y) X -
        gsA10TwoBlockTailoredIntegratedPrefix
          f hmul P₁ P₂ y X eta‖ ≤
      ‖gsA10FirstSecondaryPrefix
          (gsA10TwoBlockAlternatingLow f P₁ P₂ y)
          (gsA9HighArithmetic f y) X eta‖ +
        ‖gsA10SecondSecondaryPrefix
          (gsA10TwoBlockAlternatingLow f P₁ P₂ y)
          (gsA9HighArithmetic f y)
          (gsA9HighGeneralizedMangoldt hmul y) X eta‖ := by
  rw [← gsA10TwoBlockGlobalSecondaryError_eq_two_secondaries
    hmul P₁ P₂ hy eta]
  exact norm_positivePrefixSum_gsA10TwoBlockReconstructed_sub_tailored_le
    hmul P₁ P₂ y X eta

end

end Erdos67.MRHalaszBands
