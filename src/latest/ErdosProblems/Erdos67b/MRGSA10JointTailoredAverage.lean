import ErdosProblems.Erdos67b.MRGSA10JointHighAverage

/-!
# The actual tailored coefficient is controlled by the joint high average

The alternating low coefficient is kept intact.  Complementary prime
support extracts it at the low part of `n`; the remaining three high
factors are bounded by `gsA10JointHighMajorant` at the high part of `n`.
-/

open scoped BigOperators
open Finset MeasureTheory Set

namespace Erdos67b.MRHalaszBands

noncomputable section

private theorem arithmetic_mul_eq_zero_of_not_primeSupported
    (P : ℕ → Prop) [DecidablePred P]
    (a b : ArithmeticFunction ℂ)
    (ha : ∀ n, n ≠ 0 → ¬ PrimeSupported P n → a n = 0)
    (hb : ∀ n, n ≠ 0 → ¬ PrimeSupported P n → b n = 0)
    {n : ℕ} (hn : n ≠ 0) (hnot : ¬ PrimeSupported P n) :
    (a * b) n = 0 := by
  rw [ArithmeticFunction.mul_apply]
  apply Finset.sum_eq_zero
  intro xy hxy
  have hx : xy.1 ≠ 0 :=
    (Nat.ne_zero_of_mem_divisorsAntidiagonal hxy).1
  have hy : xy.2 ≠ 0 :=
    (Nat.ne_zero_of_mem_divisorsAntidiagonal hxy).2
  have hprod := (Nat.mem_divisorsAntidiagonal.mp hxy).1
  by_cases hxs : PrimeSupported P xy.1
  · have hys : ¬ PrimeSupported P xy.2 := by
      intro h
      apply hnot
      rw [← hprod]
      exact (primeSupported_mul_iff P hx hy).2 ⟨hxs, h⟩
    rw [hb xy.2 hy hys, mul_zero]
  · rw [ha xy.1 hx hxs, zero_mul]

private theorem arithmetic_low_mul_high_apply_eq_parts
    (P : ℕ → Prop) [DecidablePred P]
    (low high : ArithmeticFunction ℂ)
    (hlow : ∀ n, n ≠ 0 → ¬ PrimeSupported P n → low n = 0)
    (hhigh : ∀ n, n ≠ 0 →
      ¬ PrimeSupported (fun p ↦ ¬ P p) n → high n = 0)
    {n : ℕ} (hn : 0 < n) :
    (low * high) n =
      low (primeBandPart P n) *
        high (primeBandPart (fun p ↦ ¬ P p) n) := by
  let d := primeBandPart P n
  let e := primeBandPart (fun p ↦ ¬ P p) n
  have hde : d * e = n := primeBandPart_mul_compl P hn.ne'
  have hd : PrimeSupported P d := primeSupported_primeBandPart P n
  have he : PrimeSupported (fun p ↦ ¬ P p) e :=
    primeSupported_primeBandPart (fun p ↦ ¬ P p) n
  have hmem : (d, e) ∈ n.divisorsAntidiagonal :=
    Nat.mem_divisorsAntidiagonal.mpr ⟨hde, hn.ne'⟩
  rw [ArithmeticFunction.mul_apply]
  rw [Finset.sum_eq_single (d, e)]
  · intro q hq hqne
    have hq1 : q.1 ≠ 0 :=
      (Nat.ne_zero_of_mem_divisorsAntidiagonal hq).1
    have hq2 : q.2 ≠ 0 :=
      (Nat.ne_zero_of_mem_divisorsAntidiagonal hq).2
    by_cases hqLow : PrimeSupported P q.1
    · by_cases hqHigh : PrimeSupported (fun p ↦ ¬ P p) q.2
      · have hu := eq_primeBandParts_of_mul_eq P
          (Nat.mem_divisorsAntidiagonal.mp hq).1 hqLow hqHigh
        exact (hqne (Prod.ext hu.1 hu.2)).elim
      · rw [hhigh q.2 hq2 hqHigh, mul_zero]
    · rw [hlow q.1 hq1 hqLow, zero_mul]
  · exact fun h ↦ (h hmem).elim

private theorem gsRealShift_high_eq_zero_of_not_supported
    (f : ℕ → ℂ) (y : ℕ) (rho : ℝ)
    {n : ℕ} (hn : n ≠ 0)
    (hnot : ¬ PrimeSupported (fun p ↦ ¬ p ≤ y) n) :
    gsRealShift rho (gsA9HighArithmetic f y) n = 0 := by
  rw [gsRealShift_apply_of_ne_zero rho _ hn,
    gsA9HighArithmetic_apply_of_ne_zero f y hn]
  unfold gsA9High primeBandCoefficient
  rw [if_neg hnot, mul_zero]

private theorem gsRealShift_highLambdaWindow_eq_zero_of_not_supported
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
    (hcomp : IsCompletelyMultiplicativeOnPositive f)
    (y X : ℕ) (rho : ℝ)
    {n : ℕ} (hn : n ≠ 0)
    (hnot : ¬ PrimeSupported (fun p ↦ ¬ p ≤ y) n) :
    gsRealShift rho
        (gsA10LambdaWindow (gsA9HighGeneralizedMangoldt hmul y) y X) n = 0 := by
  rw [gsRealShift_apply_of_ne_zero rho _ hn, gsA10LambdaWindow_apply]
  split_ifs
  · rw [gsA9HighGeneralizedMangoldt_apply hmul hcomp y n,
      gsA9HighArithmetic_apply_of_ne_zero f y hn]
    unfold gsA9High primeBandCoefficient
    rw [if_neg hnot, zero_mul, mul_zero]
  · rw [mul_zero]

private theorem norm_gsRealShift_high_le_exp
    {f : ℕ → ℂ} (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    (y : ℕ) (rho : ℝ) {n : ℕ} (hn : 0 < n) :
    ‖gsRealShift rho (gsA9HighArithmetic f y) n‖ ≤
      Real.exp (-rho * Real.log (n : ℝ)) := by
  rw [gsRealShift_apply_of_ne_zero rho _ hn.ne', norm_mul,
    Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.exp_nonneg _)]
  apply mul_le_of_le_one_right (Real.exp_nonneg _)
  rw [gsA9HighArithmetic_apply_of_ne_zero f y hn.ne']
  exact norm_primeBandCoefficient_le_one hbound _ hn

private theorem norm_gsRealShift_highLambdaWindow_le_exp_mul_vonMangoldt
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
    (hcomp : IsCompletelyMultiplicativeOnPositive f)
    (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    (y X : ℕ) (rho : ℝ) {n : ℕ} (hn : 0 < n) :
    ‖gsRealShift rho
        (gsA10LambdaWindow (gsA9HighGeneralizedMangoldt hmul y) y X) n‖ ≤
      Real.exp (-rho * Real.log (n : ℝ)) *
        ArithmeticFunction.vonMangoldt n := by
  rw [gsRealShift_apply_of_ne_zero rho _ hn.ne', norm_mul,
    Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.exp_nonneg _)]
  apply mul_le_mul_of_nonneg_left _ (Real.exp_nonneg _)
  rw [gsA10LambdaWindow_apply]
  split_ifs
  · exact norm_gsA9HighGeneralizedMangoldt_le_vonMangoldt
      hmul hcomp hbound y n
  · simp only [norm_zero]
    exact ArithmeticFunction.vonMangoldt_nonneg

/-- Pointwise majorization of the actual tailored coefficient by the joint
high majorant at the complementary high-prime part of `n`. -/
theorem norm_gsA10TwoBlockTailoredCoefficient_le_jointHighMajorant
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
    (hcomp : IsCompletelyMultiplicativeOnPositive f)
    (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    (P₁ P₂ : ℕ → Prop) [DecidablePred P₁] [DecidablePred P₂]
    (y X : ℕ)
    (hQ₂ : ∀ p, (¬ P₁ p ∧ P₂ p) → p ≤ y)
    (hQ₃ : ∀ p, (¬ P₁ p ∧ ¬ P₂ p) → p ≤ y)
    {n : ℕ} (hn : 0 < n) {alpha beta : ℝ} :
    ‖gsA10TwoBlockTailoredCoefficient
        f hmul P₁ P₂ y X alpha beta n‖ ≤
      gsA10JointHighMajorant
        (primeBandPart (fun p ↦ ¬ p ≤ y) n) alpha beta := by
  let low := gsA10TwoBlockAlternatingLow f P₁ P₂ y
  let high := gsRealShift (alpha + 2 * beta) (gsA9HighArithmetic f y)
  let W₁ := gsRealShift alpha
    (gsA10LambdaWindow (gsA9HighGeneralizedMangoldt hmul y) y X)
  let W₂ := gsRealShift (alpha + 2 * beta)
    (gsA10LambdaWindow (gsA9HighGeneralizedMangoldt hmul y) y X)
  let tail := W₁ * (W₂ * high)
  have hcoeff :
      gsA10TwoBlockTailoredCoefficient f hmul P₁ P₂ y X alpha beta =
        low * tail := by
    dsimp only [gsA10TwoBlockTailoredCoefficient, gsA10TailoredCoefficient,
      low, high, W₁, W₂, tail]
    ring
  rw [hcoeff, arithmetic_low_mul_high_apply_eq_parts
    (fun p ↦ p ≤ y) low tail]
  · rw [norm_mul]
    calc
      ‖low (primeBandPart (fun p ↦ p ≤ y) n)‖ *
          ‖tail (primeBandPart (fun p ↦ ¬p ≤ y) n)‖ ≤
          ‖low (primeBandPart (fun p ↦ p ≤ y) n)‖ *
            gsA10JointHighMajorant
              (primeBandPart (fun p ↦ ¬p ≤ y) n) alpha beta := by
        apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
        dsimp only [tail]
        rw [ArithmeticFunction.mul_apply]
        refine (norm_sum_le _ _).trans ?_
        unfold gsA10JointHighMajorant
        apply Finset.sum_le_sum
        intro aq haq
        rw [norm_mul, ArithmeticFunction.mul_apply]
        refine (mul_le_mul_of_nonneg_left (norm_sum_le _ _)
          (norm_nonneg _)).trans ?_
        rw [Finset.mul_sum]
        apply Finset.sum_le_sum
        intro be hbe
        rw [norm_mul]
        have ha : 0 < aq.1 := Nat.pos_of_ne_zero
          (Nat.ne_zero_of_mem_divisorsAntidiagonal haq).1
        have hb : 0 < be.1 := Nat.pos_of_ne_zero
          (Nat.ne_zero_of_mem_divisorsAntidiagonal hbe).1
        have he : 0 < be.2 := Nat.pos_of_ne_zero
          (Nat.ne_zero_of_mem_divisorsAntidiagonal hbe).2
        calc
          ‖W₁ aq.1‖ * (‖W₂ be.1‖ * ‖high be.2‖) ≤
              (Real.exp (-alpha * Real.log (aq.1 : ℝ)) *
                ArithmeticFunction.vonMangoldt aq.1) *
              ((Real.exp (-(alpha + 2 * beta) * Real.log (be.1 : ℝ)) *
                ArithmeticFunction.vonMangoldt be.1) *
                Real.exp (-(alpha + 2 * beta) * Real.log (be.2 : ℝ))) := by
            exact mul_le_mul
              (norm_gsRealShift_highLambdaWindow_le_exp_mul_vonMangoldt
                hmul hcomp hbound y X alpha ha)
              (mul_le_mul
                (norm_gsRealShift_highLambdaWindow_le_exp_mul_vonMangoldt
                  hmul hcomp hbound y X (alpha + 2 * beta) hb)
                (norm_gsRealShift_high_le_exp hbound y (alpha + 2 * beta) he)
                (norm_nonneg _) (by positivity))
              (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (by positivity)
          _ = Real.exp (-alpha * Real.log (aq.1 : ℝ)) *
                  ArithmeticFunction.vonMangoldt aq.1 *
                (Real.exp (-(alpha + 2 * beta) * Real.log (be.1 : ℝ)) *
                  ArithmeticFunction.vonMangoldt be.1) *
                Real.exp (-(alpha + 2 * beta) * Real.log (be.2 : ℝ)) := by
            ring
      _ ≤ gsA10JointHighMajorant
              (primeBandPart (fun p ↦ ¬p ≤ y) n) alpha beta := by
        apply mul_le_of_le_one_left (gsA10JointHighMajorant_nonneg _ _ _)
        apply norm_gsA10TwoBlockAlternatingLow_le_one
          hmul hbound P₁ P₂ y hQ₂ hQ₃
        exact Nat.pos_of_ne_zero
          (primeBandPart_ne_zero (fun p ↦ p ≤ y) n)
  · intro d hd hnot
    exact gsA10TwoBlockAlternatingLow_eq_zero_of_not_lowSupported
      f P₁ P₂ y hd hnot
  · intro e he hnot
    dsimp only [tail]
    apply arithmetic_mul_eq_zero_of_not_primeSupported
      (fun p ↦ ¬ p ≤ y) W₁ (W₂ * high)
    · exact fun k hk ↦
        gsRealShift_highLambdaWindow_eq_zero_of_not_supported
          hmul hcomp y X alpha hk
    · intro k hk hknot
      apply arithmetic_mul_eq_zero_of_not_primeSupported
        (fun p ↦ ¬ p ≤ y) W₂ high
      · exact fun j hj ↦
          gsRealShift_highLambdaWindow_eq_zero_of_not_supported
            hmul hcomp y X (alpha + 2 * beta) hj
      · exact fun j hj ↦
          gsRealShift_high_eq_zero_of_not_supported
            f y (alpha + 2 * beta) hj
      · exact hk
      · exact hknot
    · exact he
    · exact hnot
  · exact hn

/-- Continuity of the fixed-index norm over the auxiliary rectangle. -/
theorem continuous_uncurry_norm_gsA10TwoBlockTailoredCoefficient
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
    (P₁ P₂ : ℕ → Prop) [DecidablePred P₁] [DecidablePred P₂]
    (y X n : ℕ) :
    Continuous (Function.uncurry fun alpha beta : ℝ ↦
      ‖gsA10TwoBlockTailoredCoefficient
        f hmul P₁ P₂ y X alpha beta n‖) := by
  have hshift (a : ArithmeticFunction ℂ) (k : ℕ)
      (rho : ℝ × ℝ → ℝ) (hrho : Continuous rho) :
      Continuous (fun z : ℝ × ℝ ↦ gsRealShift (rho z) a k) := by
    by_cases hk : k = 0
    · subst k
      simp
      exact continuous_const
    simp_rw [gsRealShift_apply_of_ne_zero _ _ hk]
    fun_prop
  dsimp only [gsA10TwoBlockTailoredCoefficient, gsA10TailoredCoefficient]
  simp_rw [ArithmeticFunction.mul_apply]
  apply continuous_norm.comp
  apply continuous_finset_sum
  intro uv huv
  apply Continuous.mul
  · apply continuous_finset_sum
    intro de hde
    exact continuous_const.mul
      (hshift (gsA9HighArithmetic f y) de.2
        (fun z ↦ z.1 + 2 * z.2) (by fun_prop))
  · apply continuous_finset_sum
    intro ab hab
    exact (hshift
      (gsA10LambdaWindow (gsA9HighGeneralizedMangoldt hmul y) y X)
      ab.1 (fun z ↦ z.1) (by fun_prop)).mul
      (hshift
        (gsA10LambdaWindow (gsA9HighGeneralizedMangoldt hmul y) y X)
        ab.2 (fun z ↦ z.1 + 2 * z.2) (by fun_prop))

/-- The actual tailored coefficient inherits the uniform joint `1/2`
rectangle average, with no dependence on the divisor count of `n`. -/
theorem doubleIntervalIntegral_norm_gsA10TwoBlockTailoredCoefficient_le_half
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
    (hcomp : IsCompletelyMultiplicativeOnPositive f)
    (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    (P₁ P₂ : ℕ → Prop) [DecidablePred P₁] [DecidablePred P₂]
    (y X : ℕ)
    (hQ₂ : ∀ p, (¬ P₁ p ∧ P₂ p) → p ≤ y)
    (hQ₃ : ∀ p, (¬ P₁ p ∧ ¬ P₂ p) → p ≤ y)
    {n : ℕ} (hn : 0 < n) {eta : ℝ} (heta : 0 ≤ eta) :
    (∫ alpha : ℝ in 0..eta,
      ∫ beta : ℝ in 0..eta,
        ‖gsA10TwoBlockTailoredCoefficient
          f hmul P₁ P₂ y X alpha beta n‖) ≤ 1 / 2 := by
  have hmajor : ∀ alpha ∈ Set.Icc (0 : ℝ) eta,
      ∀ beta ∈ Set.Icc (0 : ℝ) eta,
      ‖gsA10TwoBlockTailoredCoefficient
        f hmul P₁ P₂ y X alpha beta n‖ ≤
        gsA10JointHighMajorant
          (primeBandPart (fun p ↦ ¬ p ≤ y) n) alpha beta := by
    intro alpha _ beta _
    exact norm_gsA10TwoBlockTailoredCoefficient_le_jointHighMajorant
      hmul hcomp hbound P₁ P₂ y X hQ₂ hQ₃ hn
  let F : ℝ → ℝ → ℝ := fun alpha beta ↦
    ‖gsA10TwoBlockTailoredCoefficient
      f hmul P₁ P₂ y X alpha beta n‖
  let G : ℝ → ℝ → ℝ := fun alpha beta ↦
    gsA10JointHighMajorant
      (primeBandPart (fun p ↦ ¬ p ≤ y) n) alpha beta
  have hshift (a : ArithmeticFunction ℂ) (k : ℕ)
      (rho : ℝ × ℝ → ℝ) (hrho : Continuous rho) :
      Continuous (fun z : ℝ × ℝ ↦ gsRealShift (rho z) a k) := by
    by_cases hk : k = 0
    · subst k
      simp
      exact continuous_const
    simp_rw [gsRealShift_apply_of_ne_zero _ _ hk]
    fun_prop
  have hF : Continuous (Function.uncurry F) := by
    dsimp only [F, gsA10TwoBlockTailoredCoefficient,
      gsA10TailoredCoefficient]
    simp_rw [ArithmeticFunction.mul_apply]
    apply continuous_norm.comp
    apply continuous_finset_sum
    intro uv huv
    apply Continuous.mul
    · apply continuous_finset_sum
      intro de hde
      exact continuous_const.mul
        (hshift (gsA9HighArithmetic f y) de.2
          (fun z ↦ z.1 + 2 * z.2) (by fun_prop))
    · apply continuous_finset_sum
      intro ab hab
      exact (hshift
        (gsA10LambdaWindow (gsA9HighGeneralizedMangoldt hmul y) y X)
        ab.1 (fun z ↦ z.1) (by fun_prop)).mul
        (hshift
          (gsA10LambdaWindow (gsA9HighGeneralizedMangoldt hmul y) y X)
          ab.2 (fun z ↦ z.1 + 2 * z.2) (by fun_prop))
  have hG : Continuous (Function.uncurry G) := by
    dsimp only [G, gsA10JointHighMajorant]
    fun_prop
  have hFinner : Continuous (fun alpha : ℝ ↦
      ∫ beta : ℝ in 0..eta, F alpha beta) := by
    apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    exact hF
  have hGinner : Continuous (fun alpha : ℝ ↦
      ∫ beta : ℝ in 0..eta, G alpha beta) := by
    apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    exact hG
  have hmono :
      (∫ alpha : ℝ in 0..eta, ∫ beta : ℝ in 0..eta, F alpha beta) ≤
        ∫ alpha : ℝ in 0..eta, ∫ beta : ℝ in 0..eta, G alpha beta := by
    apply intervalIntegral.integral_mono_on (μ := volume) heta
      (hFinner.intervalIntegrable 0 eta) (hGinner.intervalIntegrable 0 eta)
    intro alpha halpha
    apply intervalIntegral.integral_mono_on (μ := volume) heta
      ((hF.comp (continuous_const.prodMk continuous_id)).intervalIntegrable 0 eta)
      ((hG.comp (continuous_const.prodMk continuous_id)).intervalIntegrable 0 eta)
    exact hmajor alpha halpha
  have hresult : (∫ alpha : ℝ in 0..eta, ∫ beta : ℝ in 0..eta,
      F alpha beta) ≤ 1 / 2 := hmono.trans
        (doubleIntervalIntegral_gsA10JointHighMajorant_le_half
          (Nat.pos_of_ne_zero
            (primeBandPart_ne_zero (fun p ↦ ¬ p ≤ y) n)) heta)
  simpa [F] using hresult

end

end Erdos67b.MRHalaszBands
