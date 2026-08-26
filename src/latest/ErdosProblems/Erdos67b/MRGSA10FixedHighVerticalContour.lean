import ErdosProblems.Erdos67b.MRGSA10LambdaVerticalContour

/-!
# Fixed-high A.10 vertical contour

The moving-Perron reconstruction uses the two Lambda-window lines
`c₀ - 2β` and `c₀`, not the symmetric lines `c₀ - β` and `c₀ + β`.
This module specializes the generic prime mean square separately at shifts
`2β` and `0`, then adds the exact higher-prime-power correction.
-/

open scoped LSeries.notation

namespace Erdos67b.MRHalaszBands

noncomputable section

/-- Prime-window vertical Cauchy on the actual fixed-high pair
`c₀ - 2β, c₀`. -/
theorem exists_norm_intervalIntegral_mul_gsA10PrimeLambda_fixedHigh_pair_le :
    ∃ Cβ : ℝ, 1 ≤ Cβ ∧
      ∀ {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
        (_hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
        (y X Q S : ℕ) (beta T M : ℝ) (F : ℝ → ℂ),
        2 ≤ X → 3 ≤ Q → Q ≤ y → 101 ≤ S →
        Real.log Cβ ≤ 2 * (S - 100 : ℕ) / 99 →
        0 ≤ beta → 0 < T → 0 ≤ M →
        (∀ t, |t| ≤ T → ‖F t‖ ≤ M) →
        ‖∫ t in -T..T,
            F t *
              gsA10PrimeLambdaPolynomial hmul y X
                (Erdos67b.EulerResidue.taoExponent X - 2 * beta) t *
              gsA10PrimeLambdaPolynomial hmul y X
                (Erdos67b.EulerResidue.taoExponent X) t‖ ≤
          M *
              (gsA10PrimeLambdaLeftEnergyBound Cβ Q S X y
                (2 * beta) T) ^ ((1 : ℝ) / 2) *
            (gsA10PrimeLambdaRightEnergyBound Cβ Q S y X T) ^
              ((1 : ℝ) / 2) := by
  obtain ⟨Cβ, hCβ, henergy⟩ :=
    exists_two_intervalIntegral_normSq_gsA10PrimeLambda_tao_le_betaSchur
  refine ⟨Cβ, hCβ, ?_⟩
  intro f hmul hbound y X Q S beta T M F hX hQ hQy hS hlog
    hbeta hT hM hF
  obtain ⟨hleft, _hunused⟩ :=
    henergy hmul hbound y X Q S (2 * beta) T hX hQ hQy hS hlog
      (mul_nonneg (by norm_num) hbeta) hT
  obtain ⟨_hunused, hright⟩ :=
    henergy hmul hbound y X Q S 0 T hX hQ hQy hS hlog
      le_rfl hT
  apply norm_intervalIntegral_triple_le_Linfty_mul_L2_bounds
    hT.le hM
    (continuous_gsA10PrimeLambdaPolynomial hmul y X _)
    (continuous_gsA10PrimeLambdaPolynomial hmul y X _)
    hF
  · simpa only [Real.rpow_two, Complex.normSq_eq_norm_sq,
      gsA10PrimeLambdaLeftEnergyBound, mul_assoc] using hleft
  · simpa only [Real.rpow_two, Complex.normSq_eq_norm_sq,
      gsA10PrimeLambdaRightEnergyBound, add_zero] using hright

private theorem norm_intervalIntegral_mul_gsA10LambdaWindow_pair_le_of_prime
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
    (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    {y X : ℕ} (hX : 2 ≤ X) (sigma₁ sigma₂ : ℝ)
    {T M E : ℝ} (hT : 0 ≤ T) (hM : 0 ≤ M)
    (F : ℝ → ℂ) (hFcont : Continuous F)
    (hF : ∀ t, |t| ≤ T → ‖F t‖ ≤ M)
    (hprime :
      ‖∫ t in -T..T,
          F t * gsA10PrimeLambdaPolynomial hmul y X sigma₁ (-t) *
            gsA10PrimeLambdaPolynomial hmul y X sigma₂ (-t)‖ ≤ E) :
    ‖∫ t in -T..T,
        F t *
          LSeries
            (gsA10LambdaWindow
              (gsA9HighGeneralizedMangoldt hmul y) y X)
            ((sigma₁ : ℂ) + Complex.I * (t : ℂ)) *
          LSeries
            (gsA10LambdaWindow
              (gsA9HighGeneralizedMangoldt hmul y) y X)
            ((sigma₂ : ℂ) + Complex.I * (t : ℂ))‖ ≤
      E + 2 * T * M * gsA10LambdaVerticalSplitError y X sigma₁ sigma₂ := by
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
  have herr :=
    norm_intervalIntegral_mul_LambdaWindowProduct_sub_primeProduct_le
      hmul hbound (y := y) hX sigma₁ sigma₂ hT hM F hF
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
  exact (norm_add_le _ _).trans (add_le_add (by
    simpa only [P₁, P₂] using hprime) (by
      simpa only [A₁, A₂, P₁, P₂] using herr))

/-- Actual finite Lambda-window contour bound on the fixed-high moving-Perron
lines `c₀ - 2β` and `c₀`.  This is the line-compatible version needed by
the A.10 reconstruction. -/
theorem exists_norm_intervalIntegral_mul_gsA10LambdaWindow_fixedHigh_pair_le :
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
                (((Erdos67b.EulerResidue.taoExponent X - 2 * beta : ℝ) : ℂ) +
                  Complex.I * (t : ℂ)) *
              LSeries
                (gsA10LambdaWindow
                  (gsA9HighGeneralizedMangoldt hmul y) y X)
                ((Erdos67b.EulerResidue.taoExponent X : ℂ) +
                  Complex.I * (t : ℂ))‖ ≤
          M *
                (gsA10PrimeLambdaLeftEnergyBound Cβ Q S X y
                  (2 * beta) T) ^ ((1 : ℝ) / 2) *
              (gsA10PrimeLambdaRightEnergyBound Cβ Q S y X T) ^
                ((1 : ℝ) / 2) +
            2 * T * M *
              gsA10LambdaVerticalSplitError y X
                (Erdos67b.EulerResidue.taoExponent X - 2 * beta)
                (Erdos67b.EulerResidue.taoExponent X) := by
  obtain ⟨Cβ, hCβ, hprime⟩ :=
    exists_norm_intervalIntegral_mul_gsA10PrimeLambda_fixedHigh_pair_le
  refine ⟨Cβ, hCβ, ?_⟩
  intro f hmul hbound y X Q S beta T M F hX hQ hQy hS hlog
    hbeta hT hM hFcont hF
  let sigma₁ : ℝ := Erdos67b.EulerResidue.taoExponent X - 2 * beta
  let sigma₂ : ℝ := Erdos67b.EulerResidue.taoExponent X
  let P₁ : ℝ → ℂ := gsA10PrimeLambdaPolynomial hmul y X sigma₁
  let P₂ : ℝ → ℂ := gsA10PrimeLambdaPolynomial hmul y X sigma₂
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
            (gsA10PrimeLambdaLeftEnergyBound Cβ Q S X y
              (2 * beta) T) ^ ((1 : ℝ) / 2) *
          (gsA10PrimeLambdaRightEnergyBound Cβ Q S y X T) ^
            ((1 : ℝ) / 2) := by
    rw [hflip]
    simpa only [P₁, P₂, sigma₁, sigma₂] using hprimeRaw
  exact norm_intervalIntegral_mul_gsA10LambdaWindow_pair_le_of_prime
    hmul hbound (y := y) hX sigma₁ sigma₂ hT.le hM F hFcont hF
    hprimeBound

end

end Erdos67b.MRHalaszBands

#print axioms Erdos67b.MRHalaszBands.exists_norm_intervalIntegral_mul_gsA10PrimeLambda_fixedHigh_pair_le
#print axioms Erdos67b.MRHalaszBands.exists_norm_intervalIntegral_mul_gsA10LambdaWindow_fixedHigh_pair_le
