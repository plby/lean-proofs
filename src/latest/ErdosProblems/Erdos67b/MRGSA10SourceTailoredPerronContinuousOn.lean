import ErdosProblems.Erdos67b.MRGSA10SourceFullVerticalContour

/-!
# Local continuity of the source A.10 Perron integral

The source contour uses the fixed Perron parameter `c₀`.  Thus its low
line is `c₀ - alpha - beta`, while its high and Mangoldt lines are
`c₀ + beta` and `c₀ ± beta`.  The denominator may vanish outside the
source rectangle, so the correct statement is local `ContinuousOn`, not
global continuity.
-/

open scoped BigOperators LSeries.notation
open Complex Set MeasureTheory

namespace Erdos67b.MRHalaszBands

noncomputable section

/-- The actual fixed-`c₀` source A.10 Perron integral is continuous on the
source alpha--beta rectangle. -/
theorem continuousOn_uncurry_gsA10SourceTailoredPerronIntegral_sourceRectangle
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
    (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    (P₁ P₂ : ℕ → Prop) [DecidablePred P₁] [DecidablePred P₂]
    {y X : ℕ} (hX : 2 ≤ X) (hlogy : 4 ≤ Real.log (y : ℝ))
    {T : ℝ} (hT : 0 ≤ T) :
    ContinuousOn (Function.uncurry (fun alpha beta : ℝ ↦
      gsA10TailoredPerronIntegral
        (gsA10TwoBlockAlternatingLow f P₁ P₂ y)
        (gsA9HighArithmetic f y)
        (gsA9HighGeneralizedMangoldt hmul y)
        y X (Erdos67b.EulerResidue.taoExponent X) alpha beta T))
      (Set.Icc (0 : ℝ) (Real.log (y : ℝ))⁻¹ ×ˢ
        Set.Icc (0 : ℝ) (Real.log (y : ℝ))⁻¹) := by
  let eta : ℝ := (Real.log (y : ℝ))⁻¹
  let c₀ : ℝ := Erdos67b.EulerResidue.taoExponent X
  let low : ArithmeticFunction ℂ := gsA10TwoBlockAlternatingLow f P₁ P₂ y
  let high : ArithmeticFunction ℂ := gsA9HighArithmetic f y
  let lambda : ArithmeticFunction ℂ := gsA9HighGeneralizedMangoldt hmul y
  let W : ArithmeticFunction ℂ := gsA10LambdaWindow lambda y X
  let c : ℝ → ℝ := fun x ↦ (Set.projIcc (0 : ℝ) eta (by
    dsimp only [eta]
    positivity) x : ℝ)
  let C : ℝ × ℝ → ℝ × ℝ := fun z ↦ (c z.1, c z.2)
  let sLow : (ℝ × ℝ) × ℝ → ℂ := fun zt ↦
    (((c₀ - (C zt.1).1 - (C zt.1).2 : ℝ) : ℂ) +
      (zt.2 : ℂ) * Complex.I)
  let sHigh : (ℝ × ℝ) × ℝ → ℂ := fun zt ↦
    sLow zt + (((C zt.1).1 + 2 * (C zt.1).2 : ℝ) : ℂ)
  let sLambdaLeft : (ℝ × ℝ) × ℝ → ℂ := fun zt ↦
    sLow zt + (((C zt.1).1 : ℝ) : ℂ)
  let sLambdaRight : (ℝ × ℝ) × ℝ → ℂ := fun zt ↦
    sLow zt + (((C zt.1).1 + 2 * (C zt.1).2 : ℝ) : ℂ)
  let integrand : (ℝ × ℝ) → ℝ → ℂ := fun z t ↦
    ((LSeries low (sLow (z, t)) * LSeries high (sHigh (z, t))) *
      (LSeries W (sLambdaLeft (z, t)) *
        LSeries W (sLambdaRight (z, t)))) *
      (X : ℂ) ^ (sLow (z, t)) / (sLow (z, t))
  let perron : ℝ × ℝ → ℂ := fun z ↦
    (((2 * Real.pi : ℝ) : ℂ)⁻¹) *
      ∫ t in -T..T, integrand z t
  have hlogyPos : 0 < Real.log (y : ℝ) := by linarith
  have heta0 : 0 ≤ eta := by
    dsimp only [eta]
    positivity
  have hetaQuarter : eta ≤ 1 / 4 := by
    dsimp only [eta]
    simpa only [one_div] using
      inv_anti₀ (by norm_num : (0 : ℝ) < 4) hlogy
  have hc₀ : 1 < c₀ := by
    dsimp only [c₀, Erdos67b.EulerResidue.taoExponent]
    have hlogX : 0 < Real.log (X : ℝ) :=
      Real.log_pos (by exact_mod_cast (show 1 < X by omega))
    linarith [inv_pos.mpr hlogX]
  have hc : Continuous c := by
    dsimp only [c]
    exact continuous_subtype_val.comp continuous_projIcc
  have hc_mem : ∀ x, c x ∈ Set.Icc (0 : ℝ) eta := by
    intro x
    exact (Set.projIcc (0 : ℝ) eta heta0 x).property
  have hC : Continuous C := by
    dsimp only [C]
    exact (hc.comp continuous_fst).prodMk (hc.comp continuous_snd)
  have hsLow : Continuous sLow := by
    dsimp only [sLow]
    fun_prop
  have hsHigh : Continuous sHigh := by
    dsimp only [sHigh]
    exact hsLow.add (by fun_prop)
  have hsLambdaLeft : Continuous sLambdaLeft := by
    dsimp only [sLambdaLeft]
    exact hsLow.add (by fun_prop)
  have hsLambdaRight : Continuous sLambdaRight := by
    dsimp only [sLambdaRight]
    exact hsLow.add (by fun_prop)
  have hsLowHalf : ∀ zt, (1 / 2 : ℝ) ≤ (sLow zt).re := by
    intro zt
    have ha := (hc_mem zt.1.1)
    have hb := (hc_mem zt.1.2)
    dsimp only [sLow, C, c₀]
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, zero_mul, mul_zero,
      sub_zero]
    have hcOne : (1 : ℝ) ≤ Erdos67b.EulerResidue.taoExponent X := hc₀.le
    nlinarith [ha.2, hb.2, hetaQuarter]
  have hsHighRe : ∀ zt, (sHigh zt).re = c₀ + (C zt.1).2 := by
    intro zt
    dsimp only [sHigh, sLow]
    simp
    ring
  have hsLambdaLeftPos : ∀ zt, 0 < (sLambdaLeft zt).re := by
    intro zt
    have hb := (hc_mem zt.1.2)
    dsimp only [sLambdaLeft, sLow, C]
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, zero_mul, mul_zero,
      sub_zero]
    have hcOne : (1 : ℝ) ≤ c₀ := hc₀.le
    nlinarith [hb.2, hetaQuarter]
  have hsLambdaRightRe : ∀ zt,
      (sLambdaRight zt).re = c₀ + (C zt.1).2 := by
    intro zt
    dsimp only [sLambdaRight, sLow]
    simp
    ring
  have hlowSum : LSeriesSummable low (((1 / 4 : ℝ) : ℂ)) := by
    dsimp only [low]
    exact gsA10TwoBlockAlternatingLow_LSeriesSummable_of_pos_re
      hmul hbound P₁ P₂ y (by norm_num)
  have hlowAbs : LSeries.abscissaOfAbsConv low ≤ ((1 / 4 : ℝ) : EReal) := by
    simpa using hlowSum.abscissaOfAbsConv_le
  have hhighSum : LSeriesSummable high ((((c₀ + 1) / 2 : ℝ) : ℂ)) := by
    dsimp only [high]
    apply gsA9HighArithmetic_LSeriesSummable hbound y
    simpa using (show (1 : ℝ) < (c₀ + 1) / 2 by linarith)
  have hhighAbs : LSeries.abscissaOfAbsConv high ≤
      (((c₀ + 1) / 2 : ℝ) : EReal) := by
    simpa using hhighSum.abscissaOfAbsConv_le
  have hWsum : LSeriesSummable W (0 : ℂ) := by
    dsimp only [W]
    exact gsA10LambdaWindow_LSeriesSummable lambda y X 0
  have hWAbs : LSeries.abscissaOfAbsConv W ≤ (0 : EReal) := by
    simpa using hWsum.abscissaOfAbsConv_le
  have hLLow : Continuous (fun zt ↦ LSeries low (sLow zt)) := by
    exact (LSeries_differentiableOn low).continuousOn.comp_continuous
      hsLow (fun zt ↦ by
        have hquarter : (1 / 4 : ℝ) < (sLow zt).re :=
          (by norm_num : (1 / 4 : ℝ) < 1 / 2).trans_le (hsLowHalf zt)
        exact hlowAbs.trans_lt (by exact_mod_cast hquarter))
  have hLHigh : Continuous (fun zt ↦ LSeries high (sHigh zt)) := by
    exact (LSeries_differentiableOn high).continuousOn.comp_continuous
      hsHigh (fun zt ↦ by
        change LSeries.abscissaOfAbsConv high < ((sHigh zt).re : EReal)
        rw [hsHighRe zt]
        have hb0 := (hc_mem zt.1.2).1
        exact hhighAbs.trans_lt (by
          exact_mod_cast (show (c₀ + 1) / 2 < c₀ + (C zt.1).2 by
            linarith)))
  have hLLeft : Continuous (fun zt ↦ LSeries W (sLambdaLeft zt)) := by
    exact (LSeries_differentiableOn W).continuousOn.comp_continuous
      hsLambdaLeft (fun zt ↦ hWAbs.trans_lt (by
        exact_mod_cast hsLambdaLeftPos zt))
  have hLRight : Continuous (fun zt ↦ LSeries W (sLambdaRight zt)) := by
    exact (LSeries_differentiableOn W).continuousOn.comp_continuous
      hsLambdaRight (fun zt ↦ by
        change LSeries.abscissaOfAbsConv W <
          ((sLambdaRight zt).re : EReal)
        rw [hsLambdaRightRe zt]
        have hb0 := (hc_mem zt.1.2).1
        exact hWAbs.trans_lt (by
          exact_mod_cast (show 0 < c₀ + (C zt.1).2 by linarith)))
  have hsLowNe : ∀ zt, sLow zt ≠ 0 := by
    intro zt hz
    have hre := congrArg Complex.re hz
    simp only [Complex.zero_re] at hre
    linarith [hsLowHalf zt]
  have hpow : Continuous (fun zt ↦ (X : ℂ) ^ (sLow zt)) := by
    exact continuous_const.cpow hsLow (fun _ ↦ Or.inl (by
      exact_mod_cast (show 0 < X by omega)))
  have hIntegrand : Continuous (Function.uncurry integrand) := by
    change Continuous (fun zt : (ℝ × ℝ) × ℝ ↦
      ((LSeries low (sLow zt) * LSeries high (sHigh zt)) *
        (LSeries W (sLambdaLeft zt) * LSeries W (sLambdaRight zt))) *
        (X : ℂ) ^ (sLow zt) / (sLow zt))
    exact (((hLLow.mul hLHigh).mul (hLLeft.mul hLRight)).mul hpow).div
      hsLow hsLowNe
  have hPerron : Continuous perron := by
    dsimp only [perron]
    exact continuous_const.mul
      (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
        hIntegrand (-T) T)
  have hc_eq : ∀ x ∈ Set.Icc (0 : ℝ) eta, c x = x := by
    intro x hx
    dsimp only [c]
    exact congrArg Subtype.val (Set.projIcc_of_mem heta0 hx)
  apply hPerron.continuousOn.congr
  intro z hz
  rcases z with ⟨alpha, beta⟩
  have ha : alpha ∈ Set.Icc (0 : ℝ) eta := by
    simpa only [eta] using hz.1
  have hb : beta ∈ Set.Icc (0 : ℝ) eta := by
    simpa only [eta] using hz.2
  have hlowLine : ∀ t : ℝ, |t| ≤ T →
      LSeriesSummable low
        (((c₀ - alpha - beta : ℝ) : ℂ) + (t : ℂ) * I) := by
    intro t ht
    apply hlowSum.of_re_le_re
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, zero_mul, mul_zero,
      sub_zero]
    have hcOne : (1 : ℝ) ≤ c₀ := hc₀.le
    nlinarith [ha.2, hb.2, hetaQuarter]
  have hhighLine : ∀ t : ℝ, |t| ≤ T →
      LSeriesSummable high
        (((c₀ - alpha - beta : ℝ) : ℂ) + (t : ℂ) * I +
          ((alpha + 2 * beta : ℝ) : ℂ)) := by
    intro t ht
    apply hhighSum.of_re_le_re
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, zero_mul, mul_zero,
      sub_zero]
    have hb0 := hb.1
    linarith
  have heq := gsA10TailoredPerronIntegral_eq_fourFactors
    low high lambda y X c₀ alpha beta T hT hlowLine hhighLine
  dsimp only [perron, integrand, sLow, sHigh, sLambdaLeft,
    sLambdaRight, C] at heq ⊢
  rw [hc_eq alpha ha, hc_eq beta hb]
  simpa only [low, high, lambda, W, c₀,
    Function.uncurry_apply_pair] using heq

end

end Erdos67b.MRHalaszBands

#print axioms
  Erdos67b.MRHalaszBands.continuousOn_uncurry_gsA10SourceTailoredPerronIntegral_sourceRectangle
