import ErdosProblems.Erdos67.MRGSA10FixedHighVerticalContour
import ErdosProblems.Erdos67.MRGSA10MovingPerronHigh

/-!
# The fixed-high vertical bound for the actual tailored A.10 coefficient

This module joins the pointwise A.9 bound for the low/high factor to the
weighted-Schur estimate for the two finite Mangoldt windows.  The two window
lines are the source-correct fixed-high lines `c₀ - 2β` and `c₀`.
-/

open scoped LSeries.notation

namespace Erdos67.MRHalaszBands

noncomputable section

/-- The uniform A.9 envelope used on the fixed-high A.10 contour. -/
def gsA10FixedHighHalaszEnvelope (A X : ℕ) : ℝ :=
  gsA9WideSourceEulerConstant * (1 + Real.log (X : ℝ)) *
    Real.exp
      ((-Real.exp (-1) * ((A / 2 : ℕ) : ℝ) +
        3 * Erdos67.EulerQuantitative.primeQuadraticConstant) / 2)

theorem gsA10FixedHighHalaszEnvelope_nonneg (A X : ℕ) (hX : 0 < X) :
    0 ≤ gsA10FixedHighHalaszEnvelope A X := by
  unfold gsA10FixedHighHalaszEnvelope
  have hlogX : 0 ≤ Real.log (X : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hX)
  have hwide : 0 ≤ gsA9WideSourceEulerConstant := by
    unfold gsA9WideSourceEulerConstant
    exact (Real.exp_pos _).le
  exact mul_nonneg (mul_nonneg hwide (by linarith)) (Real.exp_pos _).le

theorem continuous_LSeries_twoBlockAlternatingLow_vertical
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
    (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    (P₁ P₂ : ℕ → Prop) [DecidablePred P₁] [DecidablePred P₂]
    (y : ℕ) {sigma : ℝ} (hsigma : 0 < sigma) :
    Continuous (fun t : ℝ ↦
      LSeries (gsA10TwoBlockAlternatingLow f P₁ P₂ y)
        ((sigma : ℂ) + Complex.I * (t : ℂ))) := by
  have hhalf : 0 < sigma / 2 := by positivity
  have hsum := gsA10TwoBlockAlternatingLow_LSeriesSummable_of_pos_re
    hmul hbound P₁ P₂ y (s := ((sigma / 2 : ℝ) : ℂ)) (by simpa using hhalf)
  have habs :
      LSeries.abscissaOfAbsConv
          (gsA10TwoBlockAlternatingLow f P₁ P₂ y) < (sigma : EReal) := by
    calc
      LSeries.abscissaOfAbsConv
          (gsA10TwoBlockAlternatingLow f P₁ P₂ y) ≤
          ((sigma / 2 : ℝ) : EReal) := by
            simpa using hsum.abscissaOfAbsConv_le
      _ < (sigma : ℝ) := by exact_mod_cast (by linarith : sigma / 2 < sigma)
  have hline : Continuous (fun t : ℝ ↦
      (sigma : ℂ) + Complex.I * (t : ℂ)) := by fun_prop
  exact
    (LSeries_differentiableOn
      (gsA10TwoBlockAlternatingLow f P₁ P₂ y)).continuousOn.comp_continuous
        hline (fun t ↦ by simpa using habs)

theorem continuous_LSeries_gsA9HighArithmetic_vertical
    {f : ℕ → ℂ} (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    (y : ℕ) {sigma : ℝ} (hsigma : 1 < sigma) :
    Continuous (fun t : ℝ ↦
      LSeries (gsA9HighArithmetic f y)
        ((sigma : ℂ) + Complex.I * (t : ℂ))) := by
  have hmid : 1 < (sigma + 1) / 2 := by linarith
  have hsum := gsA9HighArithmetic_LSeriesSummable hbound y
    (s := (((sigma + 1) / 2 : ℝ) : ℂ)) (by simpa using hmid)
  have habs : LSeries.abscissaOfAbsConv (gsA9HighArithmetic f y) <
      (sigma : EReal) := by
    calc
      LSeries.abscissaOfAbsConv (gsA9HighArithmetic f y) ≤
          (((sigma + 1) / 2 : ℝ) : EReal) := by
            simpa using hsum.abscissaOfAbsConv_le
      _ < (sigma : ℝ) := by
        exact_mod_cast (by linarith : (sigma + 1) / 2 < sigma)
  have hline : Continuous (fun t : ℝ ↦
      (sigma : ℂ) + Complex.I * (t : ℂ)) := by fun_prop
  exact
    (LSeries_differentiableOn
      (gsA9HighArithmetic f y)).continuousOn.comp_continuous
        hline (fun t ↦ by simpa using habs)

/-- The exact source-deleted four-factor vertical integral is bounded by
the fixed-high A.9 envelope times the two weighted-Schur window energies,
plus the explicit higher-prime-power correction. -/
theorem exists_norm_intervalIntegral_LSeries_gsA10SourceTailored_fixedHigh_le :
    ∃ Cβ : ℝ, 1 ≤ Cβ ∧
      ∀ {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
        (_hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
        (P₁ P₂ : ℕ → Prop) [DecidablePred P₁] [DecidablePred P₂]
        {y A X Q S : ℕ} (_hy : 23 ≤ y) (_hX : 1 < X)
        (_hnonpret : MRArchimedeanNonpretentious f A X)
        (_hQ : 3 ≤ Q) (_hQy : Q ≤ y) (_hS : 101 ≤ S)
        (_hlogCβ : Real.log Cβ ≤ 2 * (S - 100 : ℕ) / 99)
        {alpha beta T : ℝ} (_hlogy : 6 ≤ Real.log (y : ℝ))
        (_halpha0 : 0 ≤ alpha)
        (_halpha : alpha ≤ (Real.log (y : ℝ))⁻¹)
        (_hbeta0 : 0 ≤ beta)
        (_hbeta : beta ≤ (Real.log (y : ℝ))⁻¹)
        (_hT : 0 < T) (_hTX : T ≤ X),
        ‖∫ t in -T..T,
            LSeries
              (gsA10SourceTailoredCoefficient
                f hmul P₁ P₂ y X alpha beta)
              (((Erdos67.EulerResidue.taoExponent X - alpha - 2 * beta : ℝ) : ℂ) +
                Complex.I * (t : ℂ))‖ ≤
          gsA10FixedHighHalaszEnvelope A X *
                (gsA10PrimeLambdaLeftEnergyBound Cβ Q S X y
                  (2 * beta) T) ^ ((1 : ℝ) / 2) *
              (gsA10PrimeLambdaRightEnergyBound Cβ Q S y X T) ^
                ((1 : ℝ) / 2) +
            2 * T * gsA10FixedHighHalaszEnvelope A X *
              gsA10LambdaVerticalSplitError y X
                (Erdos67.EulerResidue.taoExponent X - 2 * beta)
                (Erdos67.EulerResidue.taoExponent X) := by
  obtain ⟨Cβ, hCβ, hvertical⟩ :=
    exists_norm_intervalIntegral_mul_gsA10LambdaWindow_fixedHigh_pair_le
  refine ⟨Cβ, hCβ, ?_⟩
  intro f hmul hbound P₁ P₂ _ _ y A X Q S hy hX hnonpret hQ hQy hS
    hlogCβ alpha beta T hlogy halpha0 halpha hbeta0 hbeta hT hTX
  let g : ℕ → ℂ := gsA10SourceDeleted f
  let hmulG : IsMultiplicativeOnPositiveNat g :=
    gsDeletePrimeBand_isMultiplicativeOnPositiveNat hmul gsA9SmallPrime
  let c₀ : ℝ := Erdos67.EulerResidue.taoExponent X
  let sigmaLow : ℝ := c₀ - alpha - 2 * beta
  let M : ℝ := gsA10FixedHighHalaszEnvelope A X
  let F : ℝ → ℂ := fun t ↦
    LSeries (gsA10TwoBlockAlternatingLow g P₁ P₂ y)
        ((sigmaLow : ℂ) + Complex.I * (t : ℂ)) *
      LSeries (gsA9HighArithmetic g y)
        ((c₀ : ℂ) + Complex.I * (t : ℂ))
  have hboundG : ∀ n, 0 < n → ‖g n‖ ≤ 1 := by
    intro n hn
    exact norm_gsDeletePrimeBand_le_one hbound gsA9SmallPrime hn
  have hXtwo : 2 ≤ X := by omega
  have hlogyPos : 0 < Real.log (y : ℝ) := by linarith
  have hetaSixth : (Real.log (y : ℝ))⁻¹ ≤ 1 / 6 := by
    simpa only [one_div] using
      inv_anti₀ (by norm_num : (0 : ℝ) < 6) hlogy
  have hcOne : 1 ≤ c₀ := by
    dsimp only [c₀, Erdos67.EulerResidue.taoExponent]
    have hlogX : 0 < Real.log (X : ℝ) :=
      Real.log_pos (by exact_mod_cast hX)
    exact le_add_of_nonneg_right (inv_pos.mpr hlogX).le
  have hcStrict : 1 < c₀ := by
    dsimp only [c₀]
    exact Erdos67.EulerResidue.one_lt_taoExponent hX
  have hsigmaPos : 0 < sigmaLow := by
    dsimp only [sigmaLow]
    have hab : alpha + 2 * beta ≤
        3 * (Real.log (y : ℝ))⁻¹ := by linarith
    linarith
  have hFcont : Continuous F :=
    (continuous_LSeries_twoBlockAlternatingLow_vertical
      hmulG hboundG P₁ P₂ y hsigmaPos).mul
      (continuous_LSeries_gsA9HighArithmetic_vertical hboundG y hcStrict)
  have hM : 0 ≤ M := by
    dsimp only [M]
    exact gsA10FixedHighHalaszEnvelope_nonneg A X (by omega)
  have hFbound : ∀ t, |t| ≤ T → ‖F t‖ ≤ M := by
    intro t ht
    have htX : |t| ≤ X := ht.trans hTX
    have hpoint :=
      norm_LSeries_gsA10TwoBlockAlternatingLow_mul_high_le_fixedHalasz
        hmul hbound P₁ P₂ hy hX hnonpret hlogy halpha0 halpha
        hbeta0 hbeta htX
    simpa only [F, M, g, c₀, sigmaLow,
      gsA10FixedHighHalaszEnvelope] using hpoint
  have hraw := hvertical hmulG hboundG y X Q S beta T M F hXtwo hQ hQy hS
    hlogCβ hbeta0 hT hM hFcont hFbound
  have hident : ∀ t : ℝ,
      LSeries
          (gsA10SourceTailoredCoefficient f hmul P₁ P₂ y X alpha beta)
          ((sigmaLow : ℂ) + Complex.I * (t : ℂ)) =
        F t *
          LSeries
            (gsA10LambdaWindow
              (gsA9HighGeneralizedMangoldt hmulG y) y X)
            (((c₀ - 2 * beta : ℝ) : ℂ) + Complex.I * (t : ℂ)) *
          LSeries
            (gsA10LambdaWindow
              (gsA9HighGeneralizedMangoldt hmulG y) y X)
            ((c₀ : ℂ) + Complex.I * (t : ℂ)) := by
    intro t
    have hfour :=
      LSeries_gsA10SourceTailoredCoefficient_eq_fourFactors_fixedHalasz
        hmul hbound P₁ P₂ hX hlogy halpha hbeta0 hbeta (t := t)
    convert hfour using 1
    all_goals simp only [F, g, c₀, sigmaLow, mul_assoc]
    congr 6
  have hintegral :
      (∫ t in -T..T,
          LSeries
            (gsA10SourceTailoredCoefficient f hmul P₁ P₂ y X alpha beta)
            ((sigmaLow : ℂ) + Complex.I * (t : ℂ))) =
        ∫ t in -T..T,
          F t *
            LSeries
              (gsA10LambdaWindow
                (gsA9HighGeneralizedMangoldt hmulG y) y X)
              (((c₀ - 2 * beta : ℝ) : ℂ) + Complex.I * (t : ℂ)) *
            LSeries
              (gsA10LambdaWindow
                (gsA9HighGeneralizedMangoldt hmulG y) y X)
              ((c₀ : ℂ) + Complex.I * (t : ℂ)) := by
    apply intervalIntegral.integral_congr
    intro t _ht
    exact hident t
  rw [show Erdos67.EulerResidue.taoExponent X - alpha - 2 * beta =
      sigmaLow by rfl, hintegral]
  simpa only [M, c₀, gsA10FixedHighHalaszEnvelope] using hraw

end

end Erdos67.MRHalaszBands

#print axioms
  Erdos67.MRHalaszBands.exists_norm_intervalIntegral_LSeries_gsA10SourceTailored_fixedHigh_le
