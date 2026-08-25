import ErdosProblems.Erdos67.MRGSA10LambdaVerticalSplit

/-!
# The actual finite A.10 Lambda-window contour bound

This module combines the prime-window weighted-Schur estimate with the exact
prime/higher-prime-power split.  The reflection `t ↦ -t` is kept explicit:
the finite `LSeries` convention produces the prime polynomials at frequency
`-t`, while the Schur theorem was stated at frequency `t`.
-/

open scoped LSeries.notation

namespace Erdos67.MRHalaszBands

noncomputable section

theorem continuous_gsA10HigherPrimePowerLambdaPolynomial
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
    (y X : ℕ) (sigma : ℝ) :
    Continuous (gsA10HigherPrimePowerLambdaPolynomial hmul y X sigma) := by
  unfold gsA10HigherPrimePowerLambdaPolynomial
    logarithmicDirichletPolynomial
  apply continuous_finsetSum
  intro n _hn
  unfold logarithmicPhase
  fun_prop

theorem continuous_LSeries_gsA10LambdaWindow
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
    (y X : ℕ) (sigma : ℝ) :
    Continuous (fun t : ℝ ↦
      LSeries
        (gsA10LambdaWindow (gsA9HighGeneralizedMangoldt hmul y) y X)
        ((sigma : ℂ) + Complex.I * (t : ℂ))) := by
  rw [show (fun t : ℝ ↦
        LSeries
          (gsA10LambdaWindow (gsA9HighGeneralizedMangoldt hmul y) y X)
          ((sigma : ℂ) + Complex.I * (t : ℂ))) =
      fun t : ℝ ↦
        gsA10PrimeLambdaPolynomial hmul y X sigma (-t) +
          gsA10HigherPrimePowerLambdaPolynomial hmul y X sigma (-t) by
    funext t
    exact LSeries_gsA10LambdaWindow_eq_prime_add_higherPrimePower
      hmul y X sigma t]
  exact
    (continuous_gsA10PrimeLambdaPolynomial hmul y X sigma).comp
        continuous_neg |>.add
      ((continuous_gsA10HigherPrimePowerLambdaPolynomial
          hmul y X sigma).comp continuous_neg)

/-- The actual two-window vertical contour bound.  The main term is the
prime-by-prime GHS/Schur estimate.  All higher prime powers are isolated in
the explicit finite correction `gsA10LambdaVerticalSplitError`; no absolute
value is taken on the prime main term before vertical Cauchy--Schwarz. -/
theorem exists_norm_intervalIntegral_mul_gsA10LambdaWindow_pair_le :
    ∃ Cβ : ℝ, 1 ≤ Cβ ∧
      ∀ {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
        (_hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
        (y X Q S : ℕ) (beta T M : ℝ) (F : ℝ → ℂ),
        2 ≤ X → 3 ≤ Q → Q ≤ y → 101 ≤ S →
        Real.log Cβ ≤ 2 * (S - 100 : ℕ) / 99 →
        0 ≤ beta → 0 < T → 0 ≤ M → Continuous F →
        (∀ t, |t| ≤ T → ‖F t‖ ≤ M) →
        ‖∫ t in -T..T,
            F t *
              LSeries
                (gsA10LambdaWindow
                  (gsA9HighGeneralizedMangoldt hmul y) y X)
                (((Erdos67.EulerResidue.taoExponent X - beta : ℝ) : ℂ) +
                  Complex.I * (t : ℂ)) *
              LSeries
                (gsA10LambdaWindow
                  (gsA9HighGeneralizedMangoldt hmul y) y X)
                (((Erdos67.EulerResidue.taoExponent X + beta : ℝ) : ℂ) +
                  Complex.I * (t : ℂ))‖ ≤
          M *
                (gsA10PrimeLambdaLeftEnergyBound Cβ Q S X y beta T) ^
                  ((1 : ℝ) / 2) *
              (gsA10PrimeLambdaRightEnergyBound Cβ Q S y X T) ^
                ((1 : ℝ) / 2) +
            2 * T * M *
              gsA10LambdaVerticalSplitError y X
                (Erdos67.EulerResidue.taoExponent X - beta)
                (Erdos67.EulerResidue.taoExponent X + beta) := by
  obtain ⟨Cβ, hCβ, hprime⟩ :=
    exists_norm_intervalIntegral_mul_gsA10PrimeLambda_pair_le
  refine ⟨Cβ, hCβ, ?_⟩
  intro f hmul hbound y X Q S beta T M F hX hQ hQy hS hlog
    hbeta hT hM hFcont hF
  let sigma₁ : ℝ := Erdos67.EulerResidue.taoExponent X - beta
  let sigma₂ : ℝ := Erdos67.EulerResidue.taoExponent X + beta
  let P₁ : ℝ → ℂ := gsA10PrimeLambdaPolynomial hmul y X sigma₁
  let P₂ : ℝ → ℂ := gsA10PrimeLambdaPolynomial hmul y X sigma₂
  let A₁ : ℝ → ℂ := fun t ↦
    LSeries
      (gsA10LambdaWindow (gsA9HighGeneralizedMangoldt hmul y) y X)
      ((sigma₁ : ℂ) + Complex.I * (t : ℂ))
  let A₂ : ℝ → ℂ := fun t ↦
    LSeries
      (gsA10LambdaWindow (gsA9HighGeneralizedMangoldt hmul y) y X)
      ((sigma₂ : ℂ) + Complex.I * (t : ℂ))
  have hFneg : ∀ t, |t| ≤ T → ‖F (-t)‖ ≤ M := by
    intro t ht
    exact hF (-t) (by simpa only [abs_neg] using ht)
  have hprimeRaw := hprime hmul hbound y X Q S beta T M
    (fun t ↦ F (-t)) hX hQ hQy hS hlog hbeta hT hM hFneg
  have hflip :
      (∫ t in -T..T, F t * P₁ (-t) * P₂ (-t)) =
        ∫ t in -T..T, F (-t) * P₁ t * P₂ t := by
    simpa only [neg_neg] using
      (intervalIntegral.integral_comp_neg (a := -T) (b := T)
        (fun t ↦ F t * P₁ (-t) * P₂ (-t))).symm
  have hprimeBound :
      ‖∫ t in -T..T, F t * P₁ (-t) * P₂ (-t)‖ ≤
        M *
            (gsA10PrimeLambdaLeftEnergyBound Cβ Q S X y beta T) ^
              ((1 : ℝ) / 2) *
          (gsA10PrimeLambdaRightEnergyBound Cβ Q S y X T) ^
            ((1 : ℝ) / 2) := by
    rw [hflip]
    simpa only [P₁, P₂, sigma₁, sigma₂] using hprimeRaw
  have herr :=
    norm_intervalIntegral_mul_LambdaWindowProduct_sub_primeProduct_le
      hmul hbound (y := y) hX sigma₁ sigma₂ hT.le hM F hF
  have hPcont : Continuous (fun t ↦ P₁ (-t) * P₂ (-t)) :=
    ((continuous_gsA10PrimeLambdaPolynomial hmul y X sigma₁).comp
        continuous_neg).mul
      ((continuous_gsA10PrimeLambdaPolynomial hmul y X sigma₂).comp
        continuous_neg)
  have hAcont : Continuous (fun t ↦ A₁ t * A₂ t) :=
    (continuous_LSeries_gsA10LambdaWindow hmul y X sigma₁).mul
      (continuous_LSeries_gsA10LambdaWindow hmul y X sigma₂)
  have hPint : IntervalIntegrable (fun t ↦ F t * P₁ (-t) * P₂ (-t))
      MeasureTheory.volume (-T) T :=
    ((hFcont.mul
        ((continuous_gsA10PrimeLambdaPolynomial hmul y X sigma₁).comp
          continuous_neg)).mul
      ((continuous_gsA10PrimeLambdaPolynomial hmul y X sigma₂).comp
        continuous_neg)).intervalIntegrable _ _
  have hEint : IntervalIntegrable
      (fun t ↦ F t * (A₁ t * A₂ t - P₁ (-t) * P₂ (-t)))
      MeasureTheory.volume (-T) T :=
    (hFcont.mul (hAcont.sub hPcont)).intervalIntegrable _ _
  have hdecomp :
      (∫ t in -T..T, F t * A₁ t * A₂ t) =
        (∫ t in -T..T, F t * P₁ (-t) * P₂ (-t)) +
          ∫ t in -T..T,
            F t * (A₁ t * A₂ t - P₁ (-t) * P₂ (-t)) := by
    rw [← intervalIntegral.integral_add hPint hEint]
    apply intervalIntegral.integral_congr
    intro t _ht
    ring
  change ‖∫ t in -T..T, F t * A₁ t * A₂ t‖ ≤ _
  rw [hdecomp]
  exact (norm_add_le _ _).trans (add_le_add hprimeBound (by
    simpa only [A₁, A₂, P₁, P₂, sigma₁, sigma₂] using herr))

end

end Erdos67.MRHalaszBands

#print axioms Erdos67.MRHalaszBands.continuous_LSeries_gsA10LambdaWindow
#print axioms Erdos67.MRHalaszBands.exists_norm_intervalIntegral_mul_gsA10LambdaWindow_pair_le
