import ErdosProblems.Erdos67b.MRTypicalCofactorProjectionMajorant
import ErdosProblems.Erdos67b.MRGSA10DoubleIntegralMajorantOn

/-!
# Parameter regularity of the actual cofactor projection

Finite prefixes are globally continuous in both source parameters. The
moving Perron transform is continuous on its actual source rectangle;
clamping supplies a continuous extension without asserting regularity
across a vanishing denominator outside that rectangle.
-/

open scoped BigOperators Classical LSeries.notation
open Complex Set MeasureTheory

namespace Erdos67b

open MRHalaszBands MRHalaszEuler EulerResidue BoundedGaps.Maynard

noncomputable section

theorem mrContinuous_tailoredCoefficient_apply
    (low high lambda : ArithmeticFunction ℂ) (y X n : ℕ) :
    Continuous (Function.uncurry (fun alpha beta : ℝ ↦
      gsA10TailoredCoefficient low high lambda y X alpha beta n)) := by
  by_cases hn : n = 0
  · subst n
    have hz : Function.uncurry (fun alpha beta : ℝ ↦
        gsA10TailoredCoefficient low high lambda y X alpha beta 0) =
        fun _ : ℝ × ℝ ↦ (0 : ℂ) := by
      funext z
      exact ArithmeticFunction.map_zero
    rw [hz]
    exact continuous_const
  have hform : (fun z : ℝ × ℝ ↦ gsA10TailoredCoefficient low high lambda y X z.1 z.2 n) =
      fun z ↦ ∑ uv ∈ n.divisorsAntidiagonal,
        ∑ ab ∈ uv.1.divisorsAntidiagonal, ∑ cd ∈ uv.2.divisorsAntidiagonal,
          (low ab.1 * high ab.2 * gsA10LambdaWindow lambda y X cd.1 *
            gsA10LambdaWindow lambda y X cd.2) *
            gsA10ThreeShiftAverageIntegrand ab.2 cd.1 cd.2 z.1 z.2 := by
    funext z
    exact gsA10TailoredCoefficient_apply_eq_nested low high lambda y X z.1 z.2 hn
  change Continuous (fun z : ℝ × ℝ ↦ gsA10TailoredCoefficient low high lambda y X z.1 z.2 n)
  rw [hform]
  apply continuous_finsetSum
  intro uv _
  apply continuous_finsetSum
  intro ab _
  apply continuous_finsetSum
  intro cd _
  unfold gsA10ThreeShiftAverageIntegrand
  fun_prop

theorem mrContinuous_positivePrefix_typicalCofactorTailored {ι : Type*}
    (A : Finset ℕ) (J : Finset ι) (B : ι → Finset ℕ)
    (f : ℕ → ℂ) (hmul : IsMultiplicativeOnPositiveNat f) (y X : ℕ) :
    Continuous (Function.uncurry (fun alpha beta : ℝ ↦
      positivePrefixSum (mrTypicalCofactorTailoredCoefficient A J B f hmul y X alpha beta) X)) := by
  unfold positivePrefixSum
  change Continuous (fun z : ℝ × ℝ ↦
    (∑ n ∈ Finset.range (X + 1), mrTypicalCofactorTailoredCoefficient A J B f hmul y X z.1 z.2 n) -
      mrTypicalCofactorTailoredCoefficient A J B f hmul y X z.1 z.2 0)
  apply Continuous.sub
  · exact continuous_finsetSum _ (fun n _ ↦ mrContinuous_tailoredCoefficient_apply _ _ _ y X n)
  · exact mrContinuous_tailoredCoefficient_apply _ _ _ y X 0

theorem mrContinuousOn_typicalCofactorMovingPerron_sourceRectangle {ι : Type*}
    (A : Finset ℕ) (J : Finset ι) (B : ι → Finset ℕ)
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
    (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1) {y X : ℕ}
    (hX : 1 < X) (hlogy : 6 ≤ Real.log (y : ℝ)) (T : ℝ) :
    ContinuousOn (Function.uncurry (fun alpha beta : ℝ ↦
      mrTypicalCofactorMovingPerronIntegral A J B f hmul y X alpha beta T))
      (Icc (0 : ℝ) (Real.log (y : ℝ))⁻¹ ×ˢ Icc (0 : ℝ) (Real.log (y : ℝ))⁻¹) := by
  let eta : ℝ := (Real.log (y : ℝ))⁻¹
  let c₀ : ℝ := taoExponent X
  let low := mrTypicalCofactorLowArithmetic A J B f y
  let high := gsA9HighArithmetic f y
  let W := gsA10LambdaWindow (gsA9HighGeneralizedMangoldt hmul y) y X
  have heta0 : 0 ≤ eta := by dsimp only [eta]; positivity
  let c : ℝ → ℝ := fun x ↦ (Set.projIcc (0 : ℝ) eta heta0 x : ℝ)
  let C : ℝ × ℝ → ℝ × ℝ := fun z ↦ (c z.1, c z.2)
  let sLow : (ℝ × ℝ) × ℝ → ℂ := fun zt ↦
    (((c₀ - (C zt.1).1 - 2 * (C zt.1).2 : ℝ) : ℂ) + I * (zt.2 : ℂ))
  let sHigh : (ℝ × ℝ) × ℝ → ℂ := fun zt ↦ halaszPoint X zt.2
  let sLeft : (ℝ × ℝ) × ℝ → ℂ := fun zt ↦
    (((c₀ - 2 * (C zt.1).2 : ℝ) : ℂ) + I * (zt.2 : ℂ))
  let integrand : (ℝ × ℝ) → ℝ → ℂ := fun z t ↦
    ((LSeries low (sLow (z, t)) * LSeries high (sHigh (z, t))) *
      ((X : ℂ) ^ (sLow (z, t)) / sLow (z, t))) *
      LSeries W (sLeft (z, t)) * LSeries W (sHigh (z, t))
  let perron : ℝ × ℝ → ℂ := fun z ↦ (((2 * Real.pi : ℝ) : ℂ)⁻¹) *
    ∫ t in -T..T, integrand z t
  have heta : eta ≤ 1 / 6 := by
    dsimp only [eta]
    simpa only [one_div] using inv_anti₀ (by norm_num : (0 : ℝ) < 6) hlogy
  have hc₀ : 1 < c₀ := one_lt_taoExponent hX
  have hc : Continuous c := continuous_subtype_val.comp continuous_projIcc
  have hc_mem : ∀ x, c x ∈ Icc (0 : ℝ) eta :=
    fun x ↦ (Set.projIcc (0 : ℝ) eta heta0 x).property
  have hC : Continuous C :=
    (hc.comp continuous_fst).prodMk (hc.comp continuous_snd)
  have hsLow : Continuous sLow := by dsimp only [sLow]; fun_prop
  have hsHigh : Continuous sHigh := by dsimp only [sHigh, halaszPoint]; fun_prop
  have hsLeft : Continuous sLeft := by dsimp only [sLeft]; fun_prop
  have hsLowHalf : ∀ zt, (1 / 2 : ℝ) ≤ (sLow zt).re := by
    intro zt
    have ha := hc_mem zt.1.1
    have hb := hc_mem zt.1.2
    dsimp only [sLow, C]
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
      Complex.I_im, Complex.ofReal_im, zero_mul, one_mul, sub_zero, add_zero]
    linarith [ha.2, hb.2]
  have hsHighRe : ∀ zt, (sHigh zt).re = c₀ := fun zt ↦ halaszPoint_re X zt.2
  have hsLeftPos : ∀ zt, 0 < (sLeft zt).re := by
    intro zt
    have hb := hc_mem zt.1.2
    dsimp only [sLeft, C]
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
      Complex.I_im, Complex.ofReal_im, zero_mul, one_mul, sub_zero, add_zero]
    linarith [hb.2]
  have hlowSum : LSeriesSummable low ((1 / 4 : ℝ) : ℂ) :=
    mrTypicalCofactorLowArithmetic_LSeriesSummable_of_pos_re A J B hbound y (by norm_num)
  have hlowAbs : LSeries.abscissaOfAbsConv low ≤ ((1 / 4 : ℝ) : EReal) := by
    simpa using hlowSum.abscissaOfAbsConv_le
  have hhighSum : LSeriesSummable high (((c₀ + 1) / 2 : ℝ) : ℂ) :=
    gsA9HighArithmetic_LSeriesSummable hbound y (by simpa using (show 1 < (c₀ + 1) / 2 by linarith))
  have hhighAbs : LSeries.abscissaOfAbsConv high ≤ (((c₀ + 1) / 2 : ℝ) : EReal) := by
    simpa using hhighSum.abscissaOfAbsConv_le
  have hWsum : LSeriesSummable W (0 : ℂ) := gsA10LambdaWindow_LSeriesSummable _ y X 0
  have hWAbs : LSeries.abscissaOfAbsConv W ≤ (0 : EReal) := by
    simpa using hWsum.abscissaOfAbsConv_le
  have hLLow : Continuous (fun zt ↦ LSeries low (sLow zt)) :=
    (LSeries_differentiableOn low).continuousOn.comp_continuous hsLow (fun zt ↦ by
      exact hlowAbs.trans_lt (by exact_mod_cast (show (1 / 4 : ℝ) < (sLow zt).re by
        linarith [hsLowHalf zt])))
  have hLHigh : Continuous (fun zt ↦ LSeries high (sHigh zt)) :=
    (LSeries_differentiableOn high).continuousOn.comp_continuous hsHigh (fun zt ↦ by
      change LSeries.abscissaOfAbsConv high < ((sHigh zt).re : EReal)
      rw [hsHighRe]
      exact hhighAbs.trans_lt (by exact_mod_cast (show (c₀ + 1) / 2 < c₀ by linarith)))
  have hLLeft : Continuous (fun zt ↦ LSeries W (sLeft zt)) :=
    (LSeries_differentiableOn W).continuousOn.comp_continuous hsLeft (fun zt ↦
      hWAbs.trans_lt (by exact_mod_cast hsLeftPos zt))
  have hLRight : Continuous (fun zt ↦ LSeries W (sHigh zt)) :=
    (LSeries_differentiableOn W).continuousOn.comp_continuous hsHigh (fun zt ↦ by
      change LSeries.abscissaOfAbsConv W < ((sHigh zt).re : EReal)
      rw [hsHighRe]
      exact hWAbs.trans_lt (by exact_mod_cast (show 0 < c₀ by linarith)))
  have hsNe : ∀ zt, sLow zt ≠ 0 := by
    intro zt hz
    have hre := congrArg Complex.re hz
    simp only [Complex.zero_re] at hre
    linarith [hsLowHalf zt]
  have hpow : Continuous (fun zt ↦ (X : ℂ) ^ (sLow zt)) :=
    continuous_const.cpow hsLow (fun _ ↦ Or.inl (by exact_mod_cast (show 0 < X by omega)))
  have hInt : Continuous (Function.uncurry integrand) :=
    (((hLLow.mul hLHigh).mul (hpow.div hsLow hsNe)).mul hLLeft).mul hLRight
  have hPerron : Continuous perron := continuous_const.mul
    (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' hInt (-T) T)
  have hc_eq : ∀ x ∈ Icc (0 : ℝ) eta, c x = x := by
    intro x hx
    exact congrArg Subtype.val (Set.projIcc_of_mem heta0 hx)
  apply hPerron.continuousOn.congr
  intro z hz
  rcases z with ⟨alpha, beta⟩
  have ha : alpha ∈ Icc (0 : ℝ) eta := hz.1
  have hb : beta ∈ Icc (0 : ℝ) eta := hz.2
  have heq := mrTypicalCofactorMovingPerronIntegral_eq_fourFactors A J B hmul hbound hX
    hlogy ha.2 hb.2 (T := T)
  dsimp only [perron, integrand, sLow, sHigh, sLeft, C]
  rw [hc_eq alpha ha, hc_eq beta hb]
  exact heq

end

end Erdos67b
