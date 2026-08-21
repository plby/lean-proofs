import ErdosProblems.Erdos239.External.Erdos67.MRGSA10HighMangoldtSupport
import ErdosProblems.Erdos239.External.Erdos67.MRGSA10TailoredCoefficient

/-!
# Exactness of the finite GS A.10 Mangoldt window

The two generalized-Mangoldt indices in the A.10 coefficient are both
strictly larger than the low/high splitting point `y`.  If their product is
at most `X` and `y^2 ≤ X`, each is automatically strictly smaller than
`X / y`.  Thus the source window `y < n < X / y` loses no coefficient in a
prefix of length `X`.
-/

namespace Erdos67.MRHalaszBands

noncomputable section

/-- Two factors strictly above `y` and with product at most `X` each lie
strictly below the complementary quotient `X / y`. -/
theorem lt_div_of_y_lt_of_mul_le
    {y X c d : ℕ} (hy : 0 < y) (hyc : y < c) (hyd : y < d)
    (hcd : c * d ≤ X) :
    c < X / y := by
  have hstep : (c + 1) * y ≤ c * d := by
    nlinarith
  have hquot : c + 1 ≤ X / y :=
    (Nat.le_div_iff_mul_le hy).2 (hstep.trans hcd)
  omega

/-- A coefficient which vanishes at and below `y` agrees with its A.10
window at every nonzero index participating in a two-factor product of size
at most `X`. -/
theorem gsA10LambdaWindow_apply_eq_of_pair
    (lambda : ArithmeticFunction ℂ) (y X c d : ℕ)
    (hy : 0 < y) (_hc : c ≠ 0) (_hd : d ≠ 0)
    (hcd : c * d ≤ X)
    (hlower : ∀ {n : ℕ}, n ≤ y → lambda n = 0)
    (hcNonzero : lambda c ≠ 0) (hdNonzero : lambda d ≠ 0) :
    gsA10LambdaWindow lambda y X c = lambda c ∧
      gsA10LambdaWindow lambda y X d = lambda d := by
  have hyc : y < c := by
    apply lt_of_not_ge
    intro hcy
    exact hcNonzero (hlower hcy)
  have hyd : y < d := by
    apply lt_of_not_ge
    intro hdy
    exact hdNonzero (hlower hdy)
  have hcUpper : c < X / y :=
    lt_div_of_y_lt_of_mul_le hy hyc hyd hcd
  have hdUpper : d < X / y := by
    rw [mul_comm] at hcd
    exact lt_div_of_y_lt_of_mul_le hy hyd hyc hcd
  constructor <;> simp [gsA10LambdaWindow, *]

/-- Exact double-Mangoldt convolution window on every coefficient `n≤X`.
This is stated after arbitrary real shifts, exactly as used in A.10. -/
theorem gsRealShift_mul_gsRealShift_lambdaWindow_eq_of_le
    (lambda : ArithmeticFunction ℂ) (y X : ℕ) (rho₁ rho₂ : ℝ)
    (hy : 0 < y)
    (hlower : ∀ {n : ℕ}, n ≤ y → lambda n = 0)
    {n : ℕ} (hn : n ≤ X) :
    (gsRealShift rho₁ (gsA10LambdaWindow lambda y X) *
        gsRealShift rho₂ (gsA10LambdaWindow lambda y X)) n =
      (gsRealShift rho₁ lambda * gsRealShift rho₂ lambda) n := by
  classical
  by_cases hn0 : n = 0
  · subst n
    simp
  rw [ArithmeticFunction.mul_apply, ArithmeticFunction.mul_apply]
  apply Finset.sum_congr rfl
  intro cd hmem
  have hprod : cd.1 * cd.2 = n :=
    (Nat.mem_divisorsAntidiagonal.mp hmem).1
  have hc0 : cd.1 ≠ 0 := by
    intro h
    rw [h, zero_mul] at hprod
    exact hn0 hprod.symm
  have hd0 : cd.2 ≠ 0 := by
    intro h
    rw [h, mul_zero] at hprod
    exact hn0 hprod.symm
  by_cases hc : lambda cd.1 = 0
  · have hcWindow : gsA10LambdaWindow lambda y X cd.1 = 0 := by
      rw [gsA10LambdaWindow_apply]
      split_ifs <;> simp_all
    rw [gsRealShift_apply_of_ne_zero rho₁ _ hc0,
      gsRealShift_apply_of_ne_zero rho₁ lambda hc0,
      hcWindow, hc]
    simp
  by_cases hd : lambda cd.2 = 0
  · have hdWindow : gsA10LambdaWindow lambda y X cd.2 = 0 := by
      rw [gsA10LambdaWindow_apply]
      split_ifs <;> simp_all
    rw [gsRealShift_apply_of_ne_zero rho₂ _ hd0,
      gsRealShift_apply_of_ne_zero rho₂ lambda hd0,
      hdWindow, hd]
    simp
  have hcdX : cd.1 * cd.2 ≤ X := by simpa [hprod] using hn
  obtain ⟨hcWindow, hdWindow⟩ :=
    gsA10LambdaWindow_apply_eq_of_pair
      lambda y X cd.1 cd.2 hy hc0 hd0 hcdX hlower hc hd
  rw [gsRealShift_apply_of_ne_zero rho₁ _ hc0,
    gsRealShift_apply_of_ne_zero rho₂ _ hd0,
    gsRealShift_apply_of_ne_zero rho₁ lambda hc0,
    gsRealShift_apply_of_ne_zero rho₂ lambda hd0,
    hcWindow, hdWindow]

/-- Actual-high-factor specialization of the exact double-Mangoldt window. -/
theorem gsRealShift_mul_gsRealShift_highLambdaWindow_eq_of_le
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
    (y X : ℕ) (rho₁ rho₂ : ℝ) (hy : 0 < y)
    {n : ℕ} (hn : n ≤ X) :
    (gsRealShift rho₁
          (gsA10LambdaWindow (gsA9HighGeneralizedMangoldt hmul y) y X) *
        gsRealShift rho₂
          (gsA10LambdaWindow (gsA9HighGeneralizedMangoldt hmul y) y X)) n =
      (gsRealShift rho₁ (gsA9HighGeneralizedMangoldt hmul y) *
        gsRealShift rho₂ (gsA9HighGeneralizedMangoldt hmul y)) n := by
  exact gsRealShift_mul_gsRealShift_lambdaWindow_eq_of_le
    (gsA9HighGeneralizedMangoldt hmul y) y X rho₁ rho₂ hy
    (fun hn ↦ gsA9HighGeneralizedMangoldt_eq_zero_of_le hmul y hn) hn

/-- The whole tailored four-fold coefficient agrees with the unwindowed
four-fold convolution at every positive index at most `X`. -/
theorem gsA10TailoredCoefficient_apply_eq_full_of_le
    (low high lambda : ArithmeticFunction ℂ)
    (y X : ℕ) (alpha beta : ℝ) (hy : 0 < y)
    (hlower : ∀ {n : ℕ}, n ≤ y → lambda n = 0)
    {n : ℕ} (hn0 : n ≠ 0) (hn : n ≤ X) :
    gsA10TailoredCoefficient low high lambda y X alpha beta n =
      ((low * gsRealShift (alpha + 2 * beta) high) *
        (gsRealShift alpha lambda *
          gsRealShift (alpha + 2 * beta) lambda)) n := by
  rw [gsA10TailoredCoefficient, ArithmeticFunction.mul_apply,
    ArithmeticFunction.mul_apply]
  apply Finset.sum_congr rfl
  intro uv huv
  have hprod : uv.1 * uv.2 = n :=
    (Nat.mem_divisorsAntidiagonal.mp huv).1
  have huv2pos : 0 < uv.2 := by
    by_contra h
    have huv20 : uv.2 = 0 := Nat.eq_zero_of_not_pos h
    rw [huv20, mul_zero] at hprod
    exact hn0 hprod.symm
  have huv2le : uv.2 ≤ X := by
    apply (Nat.le_of_dvd (Nat.pos_of_ne_zero hn0) ?_).trans hn
    exact ⟨uv.1, by rw [mul_comm, hprod]⟩
  rw [gsRealShift_mul_gsRealShift_lambdaWindow_eq_of_le
    lambda y X alpha (alpha + 2 * beta) hy hlower huv2le]

/-- Actual-high-factor form of exactness of the whole tailored coefficient. -/
theorem gsA10TwoBlockTailoredCoefficient_apply_eq_full_of_le
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
    (low : ArithmeticFunction ℂ) (y X : ℕ)
    (alpha beta : ℝ) (hy : 0 < y)
    {n : ℕ} (hn0 : n ≠ 0) (hn : n ≤ X) :
    gsA10TailoredCoefficient low (gsA9HighArithmetic f y)
        (gsA9HighGeneralizedMangoldt hmul y) y X alpha beta n =
      ((low * gsRealShift (alpha + 2 * beta)
          (gsA9HighArithmetic f y)) *
        (gsRealShift alpha (gsA9HighGeneralizedMangoldt hmul y) *
          gsRealShift (alpha + 2 * beta)
            (gsA9HighGeneralizedMangoldt hmul y))) n := by
  exact gsA10TailoredCoefficient_apply_eq_full_of_le
    low (gsA9HighArithmetic f y) (gsA9HighGeneralizedMangoldt hmul y)
    y X alpha beta hy
    (fun hn ↦ gsA9HighGeneralizedMangoldt_eq_zero_of_le hmul y hn)
    hn0 hn

end

end Erdos67.MRHalaszBands
