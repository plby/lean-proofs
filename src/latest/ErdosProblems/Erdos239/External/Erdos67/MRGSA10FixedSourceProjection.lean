import ErdosProblems.Erdos239.External.Erdos67.MRGSA10JointProjectionSource
import ErdosProblems.Erdos239.External.Erdos67.MRGSA10SourceTailoredPerronContinuousOn
import ErdosProblems.Erdos239.External.Erdos67.MRGSA10CoefficientMassSourceScalar

/-!
# Joint projection onto the fixed source A.10 contour

This is the fixed-line counterpart of `MRGSA10JointProjectionSource`.
It matches the contour in `MRGSA10SourceFullVerticalContour`: the Perron
parameter is `taoExponent X`, the low line is `c-alpha-beta`, and the two
finite Mangoldt windows lie on `c-beta` and `c+beta`.
-/

open scoped BigOperators
open Finset MeasureTheory Set

namespace Erdos67.MRHalaszBands

noncomputable section

open BoundedGaps.Maynard

/-- The fixed source Perron contour averaged over the A.10 rectangle. -/
def gsA10TwoBlockSourcePerronIntegrated
    (f : ℕ → ℂ) (hmul : IsMultiplicativeOnPositiveNat f)
    (P₁ P₂ : ℕ → Prop) [DecidablePred P₁] [DecidablePred P₂]
    (y X : ℕ) (eta T : ℝ) : ℂ :=
  2 * ∫ alpha in 0..eta, ∫ beta in 0..eta,
    gsA10TailoredPerronIntegral
      (gsA10TwoBlockAlternatingLow f P₁ P₂ y)
      (gsA9HighArithmetic f y)
      (gsA9HighGeneralizedMangoldt hmul y)
      y X (Erdos67.EulerResidue.taoExponent X) alpha beta T

/-- Four-factor absolute mass on the fixed source line. -/
theorem dirichletPerronCoefficientMass_twoBlockTailored_sourceTao_le
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
    (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    (P₁ P₂ : ℕ → Prop) [DecidablePred P₁] [DecidablePred P₂]
    {y X : ℕ} (hy : 23 ≤ y) (hX : 1 < X)
    (hQ₂ : ∀ p, (¬ P₁ p ∧ P₂ p) → p ≤ y)
    (hQ₃ : ∀ p, (¬ P₁ p ∧ ¬ P₂ p) → p ≤ y)
    {alpha beta : ℝ} (hlogy : 4 ≤ Real.log (y : ℝ))
    (halpha0 : 0 ≤ alpha)
    (halpha : alpha ≤ (Real.log (y : ℝ))⁻¹)
    (hbeta0 : 0 ≤ beta)
    (hbeta : beta ≤ (Real.log (y : ℝ))⁻¹) :
    dirichletPerronCoefficientMass
        (gsA10TwoBlockTailoredCoefficient
          f hmul P₁ P₂ y X alpha beta)
        (Erdos67.EulerResidue.taoExponent X - alpha - beta) ≤
      (gsA10SourceCoefficientMassConstant *
        (1 + Real.log (X : ℝ))) *
      ((gsA10OrdinaryLambdaWindowMassBase y X) ^ 2 *
        (X : ℝ) ^
          (1 - min (Erdos67.EulerResidue.taoExponent X - beta) 1)) := by
  let c : ℝ := Erdos67.EulerResidue.taoExponent X
  let sigmaLow : ℝ := c - alpha - beta
  let sigmaHigh : ℝ := c + beta
  let low : ArithmeticFunction ℂ :=
    gsA10TwoBlockAlternatingLow f P₁ P₂ y
  let high : ArithmeticFunction ℂ := gsA9HighArithmetic f y
  have hX2 : 2 ≤ X := by omega
  have hlogX : 0 < Real.log (X : ℝ) :=
    Real.log_pos (by exact_mod_cast hX)
  have hcOne : 1 ≤ c := by
    dsimp only [c, Erdos67.EulerResidue.taoExponent]
    exact le_add_of_nonneg_right (inv_pos.mpr hlogX).le
  have hetaQuarter : (Real.log (y : ℝ))⁻¹ ≤ 1 / 4 := by
    simpa only [one_div] using
      inv_anti₀ (by norm_num : (0 : ℝ) < 4) hlogy
  have hsigmaHalf : 1 / 2 ≤ sigmaLow := by
    dsimp only [sigmaLow]
    linarith
  have hsigmaPos : 0 < sigmaLow :=
    (by norm_num : (0 : ℝ) < 1 / 2).trans_le hsigmaHalf
  have hsigmaHigh : 1 < sigmaHigh := by
    dsimp only [sigmaHigh, c, Erdos67.EulerResidue.taoExponent]
    linarith [inv_pos.mpr hlogX]
  have hsigmaLe : sigmaLow ≤ sigmaHigh := by
    dsimp only [sigmaLow, sigmaHigh]
    linarith
  have hsigmaWide : 1 - 3 / Real.log (y : ℝ) ≤ sigmaLow := by
    dsimp only [sigmaLow]
    rw [show 3 / Real.log (y : ℝ) =
      3 * (Real.log (y : ℝ))⁻¹ by field_simp]
    linarith
  have hgap : sigmaHigh - sigmaLow ≤ 3 / Real.log (y : ℝ) := by
    dsimp only [sigmaLow, sigmaHigh]
    rw [show 3 / Real.log (y : ℝ) =
      3 * (Real.log (y : ℝ))⁻¹ by field_simp]
    linarith
  have hlowSum : LSeriesSummable low ((sigmaLow : ℝ) : ℂ) := by
    dsimp only [low]
    exact gsA10TwoBlockAlternatingLow_LSeriesSummable_of_pos_re
      hmul hbound P₁ P₂ y (by simpa using hsigmaPos)
  have hhighSum : LSeriesSummable high ((sigmaHigh : ℝ) : ℂ) := by
    dsimp only [high]
    exact gsA9HighArithmetic_LSeriesSummable hbound y
      (by simpa using hsigmaHigh)
  have hfour :=
    dirichletPerronCoefficientMass_gsA10Tailored_ordinary_sourceLines_le
      hmul hbound low high hX2 hlogy hbeta0 hbeta hlowSum hhighSum
  have hfront :=
    mul_dirichletPerronCoefficientMass_twoBlockLow_high_le_source
      hmul hbound P₁ P₂ hy hQ₂ hQ₃ hsigmaHalf hsigmaHigh hsigmaLe
        hsigmaWide hgap
  have hdelta : (Real.log (X : ℝ))⁻¹ ≤ sigmaHigh - 1 := by
    dsimp only [sigmaHigh, c, Erdos67.EulerResidue.taoExponent]
    linarith
  have hinv : (sigmaHigh - 1)⁻¹ ≤ Real.log (X : ℝ) := by
    have := inv_anti₀ (inv_pos.mpr hlogX) hdelta
    simpa only [inv_inv] using this
  have hfront' :
      dirichletPerronCoefficientMass low sigmaLow *
          dirichletPerronCoefficientMass high sigmaHigh ≤
        gsA10SourceCoefficientMassConstant *
          (1 + Real.log (X : ℝ)) := by
    calc
      _ ≤ gsA10SourceCoefficientMassConstant *
          (1 + (sigmaHigh - 1)⁻¹) := hfront
      _ ≤ gsA10SourceCoefficientMassConstant *
          (1 + Real.log (X : ℝ)) :=
        mul_le_mul_of_nonneg_left (add_le_add_right hinv 1)
          gsA10SourceCoefficientMassConstant_nonneg
  have hwindow0 : 0 ≤
      (gsA10OrdinaryLambdaWindowMassBase y X) ^ 2 *
        (X : ℝ) ^ (1 - min (c - beta) 1) := by positivity
  have hfour' :
      dirichletPerronCoefficientMass
          (gsA10TwoBlockTailoredCoefficient
            f hmul P₁ P₂ y X alpha beta) sigmaLow ≤
        (dirichletPerronCoefficientMass low sigmaLow *
          dirichletPerronCoefficientMass high sigmaHigh) *
        ((gsA10OrdinaryLambdaWindowMassBase y X) ^ 2 *
          (X : ℝ) ^ (1 - min (c - beta) 1)) := by
    simpa only [low, high, c, sigmaLow, sigmaHigh,
      gsA10TwoBlockTailoredCoefficient] using hfour
  exact hfour'.trans (mul_le_mul_of_nonneg_right
    (by simpa only [low, high, c, sigmaLow, sigmaHigh] using hfront')
    hwindow0)

/-- The coefficient-mass part of the fixed source projection error. -/
def gsA10SourcePerronMassEnvelope (y X : ℕ) (alpha beta : ℝ) : ℝ :=
  (32 / (Real.log (X : ℝ)) ^ 2) *
    (gsA10MovingPerronMassConstant y X *
      ((X : ℝ) ^
          (Erdos67.EulerResidue.taoExponent X - alpha - beta) *
        (X : ℝ) ^
          (1 - min
            (Erdos67.EulerResidue.taoExponent X - beta) 1)))

theorem norm_positivePrefixSum_gsA10TwoBlockTailored_sub_sourcePerron_le_massEnvelope
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
    (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    (P₁ P₂ : ℕ → Prop) [DecidablePred P₁] [DecidablePred P₂]
    {y X : ℕ} (hy : 23 ≤ y) (hX : 2 ≤ X)
    (hlogX : 1 ≤ Real.log (X : ℝ))
    (hlogy : 4 ≤ Real.log (y : ℝ))
    (hQ₂ : ∀ p, (¬ P₁ p ∧ P₂ p) → p ≤ y)
    (hQ₃ : ∀ p, (¬ P₁ p ∧ ¬ P₂ p) → p ≤ y)
    {alpha beta : ℝ}
    (halpha0 : 0 ≤ alpha)
    (halpha : alpha ≤ (Real.log (y : ℝ))⁻¹)
    (hbeta0 : 0 ≤ beta)
    (hbeta : beta ≤ (Real.log (y : ℝ))⁻¹) :
    ‖positivePrefixSum
          (gsA10TwoBlockTailoredCoefficient
            f hmul P₁ P₂ y X alpha beta) X -
        gsA10TailoredPerronIntegral
          (gsA10TwoBlockAlternatingLow f P₁ P₂ y)
          (gsA9HighArithmetic f y)
          (gsA9HighGeneralizedMangoldt hmul y)
          y X (Erdos67.EulerResidue.taoExponent X) alpha beta
            ((Real.log (X : ℝ)) ^ 2)‖ ≤
      dirichletPerronNearMass
          (gsA10TwoBlockTailoredCoefficient
            f hmul P₁ P₂ y X alpha beta) X
          ((Real.log (X : ℝ)) ^ 2) +
        gsA10SourcePerronMassEnvelope y X alpha beta +
        (1 / 2 : ℝ) *
          ‖gsA10TwoBlockTailoredCoefficient
            f hmul P₁ P₂ y X alpha beta X‖ := by
  have hbase :=
    norm_positivePrefixSum_gsA10TwoBlockTailored_sub_perron_le_sourceWindow
      hmul hbound P₁ P₂ (show 0 < X by omega) hlogX hlogy
        halpha0 halpha hbeta0 hbeta
        (show 0 < Real.log (X : ℝ) ^ 2 by positivity)
  have hmass :=
    dirichletPerronCoefficientMass_twoBlockTailored_sourceTao_le
      hmul hbound P₁ P₂ hy (by omega : 1 < X) hQ₂ hQ₃ hlogy
        halpha0 halpha hbeta0 hbeta
  have hfactor : 0 ≤
      32 * (X : ℝ) ^
          (Erdos67.EulerResidue.taoExponent X - alpha - beta) /
        (Real.log (X : ℝ)) ^ 2 := by positivity
  apply hbase.trans
  apply add_le_add (add_le_add le_rfl ?_) le_rfl
  calc
    (32 * (X : ℝ) ^
          (Erdos67.EulerResidue.taoExponent X - alpha - beta) /
        (Real.log (X : ℝ)) ^ 2) *
        dirichletPerronCoefficientMass
          (gsA10TwoBlockTailoredCoefficient
            f hmul P₁ P₂ y X alpha beta)
          (Erdos67.EulerResidue.taoExponent X - alpha - beta) ≤
      (32 * (X : ℝ) ^
          (Erdos67.EulerResidue.taoExponent X - alpha - beta) /
        (Real.log (X : ℝ)) ^ 2) *
        ((gsA10SourceCoefficientMassConstant *
            (1 + Real.log (X : ℝ))) *
          ((gsA10OrdinaryLambdaWindowMassBase y X) ^ 2 *
            (X : ℝ) ^
              (1 - min
                (Erdos67.EulerResidue.taoExponent X - beta) 1))) :=
      mul_le_mul_of_nonneg_left hmass hfactor
    _ = gsA10SourcePerronMassEnvelope y X alpha beta := by
      unfold gsA10SourcePerronMassEnvelope gsA10MovingPerronMassConstant
      ring

theorem two_mul_doubleIntervalIntegral_gsA10SourcePerronMassEnvelope_div_le_eta
    {X y : ℕ} (hX : 2 ≤ X) (hy3 : 3 ≤ y)
    (hlogX : 1 ≤ Real.log (X : ℝ))
    (hprimeMass : Erdos67.PrimeEstimates.primeReciprocals X ≤
      Real.log (X : ℝ))
    (hy : (Real.log (X : ℝ)) ^ 4 ≤ (y : ℝ))
    {eta : ℝ} (heta : 0 ≤ eta) :
    2 * (∫ alpha : ℝ in 0..eta,
      ∫ beta : ℝ in 0..eta,
        gsA10SourcePerronMassEnvelope y X alpha beta) / (X : ℝ) ≤
      gsA10MovingPerronAveragedMassConstant * eta := by
  let K : ℝ := gsA10MovingPerronMassConstant y X
  have hlogXpos : 0 < Real.log (X : ℝ) := zero_lt_one.trans_le hlogX
  have hK0 : 0 ≤ K := by
    dsimp only [K, gsA10MovingPerronMassConstant]
    exact mul_nonneg
      (mul_nonneg gsA10SourceCoefficientMassConstant_nonneg (by positivity))
      (sq_nonneg _)
  have hbase := doubleIntervalIntegral_sourcePerron_massEnvelope_le
    (X := X) (by omega : 1 < X) heta hK0
  have hscaled :
      2 * (∫ alpha : ℝ in 0..eta,
        ∫ beta : ℝ in 0..eta,
          gsA10SourcePerronMassEnvelope y X alpha beta) / (X : ℝ) ≤
        64 * Real.exp 1 * K * eta / (Real.log (X : ℝ)) ^ 3 := by
    have hXR : (0 : ℝ) < X := by exact_mod_cast (show 0 < X by omega)
    have hscale : 0 ≤ (64 / (Real.log (X : ℝ)) ^ 2) / (X : ℝ) := by
      positivity
    have hs := mul_le_mul_of_nonneg_left hbase hscale
    change
      2 * (∫ alpha : ℝ in 0..eta,
        ∫ beta : ℝ in 0..eta,
          (32 / (Real.log (X : ℝ)) ^ 2) *
            (K * ((X : ℝ) ^
              (Erdos67.EulerResidue.taoExponent X - alpha - beta) *
              (X : ℝ) ^
                (1 - min
                  (Erdos67.EulerResidue.taoExponent X - beta) 1)))) /
          (X : ℝ) ≤ _
    rw [show (∫ alpha : ℝ in 0..eta,
        ∫ beta : ℝ in 0..eta,
          (32 / (Real.log (X : ℝ)) ^ 2) *
            (K * ((X : ℝ) ^
              (Erdos67.EulerResidue.taoExponent X - alpha - beta) *
              (X : ℝ) ^
                (1 - min
                  (Erdos67.EulerResidue.taoExponent X - beta) 1)))) =
        (32 / (Real.log (X : ℝ)) ^ 2) *
          (∫ alpha : ℝ in 0..eta,
            ∫ beta : ℝ in 0..eta,
              K * ((X : ℝ) ^
                (Erdos67.EulerResidue.taoExponent X - alpha - beta) *
                (X : ℝ) ^
                  (1 - min
                    (Erdos67.EulerResidue.taoExponent X - beta) 1))) by
      simp only [intervalIntegral.integral_const_mul]]
    calc
      2 * ((32 / (Real.log (X : ℝ)) ^ 2) * _) / (X : ℝ) =
          ((64 / (Real.log (X : ℝ)) ^ 2) / (X : ℝ)) * _ := by ring
      _ ≤ ((64 / (Real.log (X : ℝ)) ^ 2) / (X : ℝ)) *
          (K * Real.exp 1 * eta *
            ((X : ℝ) / Real.log (X : ℝ))) := hs
      _ = 64 * Real.exp 1 * K * eta /
          (Real.log (X : ℝ)) ^ 3 := by
        field_simp [hXR.ne', hlogXpos.ne']
  have hMassBase := gsA10OrdinaryLambdaWindowMassBase_le_log
    (X := X) (y := y) (by omega) hy3 hlogX hprimeMass hy
  have hmass : K ≤
      2 * gsA10SourceCoefficientMassConstant *
        gsA10OrdinaryLambdaWindowMassLogConstant ^ 2 *
        (Real.log (X : ℝ)) ^ 3 := by
    dsimp only [K, gsA10MovingPerronMassConstant]
    have hsource : 0 ≤ gsA10SourceCoefficientMassConstant :=
      gsA10SourceCoefficientMassConstant_nonneg
    have hmassBase0 : 0 ≤ gsA10OrdinaryLambdaWindowMassBase y X :=
      gsA10OrdinaryLambdaWindowMassBase_nonneg y X
    have hcoef0 : 0 ≤ gsA10OrdinaryLambdaWindowMassLogConstant :=
      gsA10OrdinaryLambdaWindowMassLogConstant_nonneg
    have hsq : (gsA10OrdinaryLambdaWindowMassBase y X) ^ 2 ≤
        (gsA10OrdinaryLambdaWindowMassLogConstant *
          Real.log (X : ℝ)) ^ 2 := by
      nlinarith [sq_nonneg
        (gsA10OrdinaryLambdaWindowMassBase y X -
          gsA10OrdinaryLambdaWindowMassLogConstant *
            Real.log (X : ℝ))]
    have hone : 1 + Real.log (X : ℝ) ≤
        2 * Real.log (X : ℝ) := by linarith
    calc
      _ ≤ (gsA10SourceCoefficientMassConstant *
          (2 * Real.log (X : ℝ))) *
          (gsA10OrdinaryLambdaWindowMassLogConstant *
            Real.log (X : ℝ)) ^ 2 :=
        mul_le_mul
          (mul_le_mul_of_nonneg_left hone hsource) hsq
          (sq_nonneg _) (mul_nonneg hsource (by positivity))
      _ = _ := by ring
  have hfactor : 0 ≤ 64 * Real.exp 1 * eta /
      (Real.log (X : ℝ)) ^ 3 := by positivity
  calc
    _ ≤ 64 * Real.exp 1 * K * eta /
        (Real.log (X : ℝ)) ^ 3 := hscaled
    _ = (64 * Real.exp 1 * eta /
        (Real.log (X : ℝ)) ^ 3) * K := by ring
    _ ≤ (64 * Real.exp 1 * eta /
        (Real.log (X : ℝ)) ^ 3) *
        (2 * gsA10SourceCoefficientMassConstant *
          gsA10OrdinaryLambdaWindowMassLogConstant ^ 2 *
          (Real.log (X : ℝ)) ^ 3) :=
      mul_le_mul_of_nonneg_left hmass hfactor
    _ = gsA10MovingPerronAveragedMassConstant * eta := by
      unfold gsA10MovingPerronAveragedMassConstant
      field_simp [hlogXpos.ne']
      ring

private theorem doubleIntervalIntegral_add_fixedSource
    {F G : ℝ → ℝ → ℝ} {eta : ℝ}
    (hF : Continuous (Function.uncurry F))
    (hG : Continuous (Function.uncurry G)) :
    (∫ alpha : ℝ in 0..eta,
      ∫ beta : ℝ in 0..eta, F alpha beta + G alpha beta) =
      (∫ alpha : ℝ in 0..eta, ∫ beta : ℝ in 0..eta, F alpha beta) +
      (∫ alpha : ℝ in 0..eta, ∫ beta : ℝ in 0..eta, G alpha beta) := by
  have hFinner : Continuous (fun alpha : ℝ ↦
      ∫ beta : ℝ in 0..eta, F alpha beta) :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      hF 0 eta
  have hGinner : Continuous (fun alpha : ℝ ↦
      ∫ beta : ℝ in 0..eta, G alpha beta) :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      hG 0 eta
  calc
    _ = ∫ alpha : ℝ in 0..eta,
        ((∫ beta : ℝ in 0..eta, F alpha beta) +
          ∫ beta : ℝ in 0..eta, G alpha beta) := by
      apply intervalIntegral.integral_congr
      intro alpha halpha
      exact intervalIntegral.integral_add
        ((hF.comp
          (continuous_const.prodMk continuous_id)).intervalIntegrable 0 eta)
        ((hG.comp
          (continuous_const.prodMk continuous_id)).intervalIntegrable 0 eta)
    _ = _ := intervalIntegral.integral_add
      (hFinner.intervalIntegrable 0 eta) (hGinner.intervalIntegrable 0 eta)

/-- The whole fixed-source projection has the same explicit joint source
budget as the moving-line projection. -/
theorem norm_gsA10TwoBlockTailoredIntegratedPrefix_sub_sourcePerronIntegrated_div_le_jointSource
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
    (hcomp : IsCompletelyMultiplicativeOnPositive f)
    (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    (P₁ P₂ : ℕ → Prop) [DecidablePred P₁] [DecidablePred P₂]
    {y X : ℕ} (hy : 23 ≤ y) (hX : 2 ≤ X)
    (hlogX : 1 ≤ Real.log (X : ℝ))
    (hlogy : 6 ≤ Real.log (y : ℝ))
    (hprimeMass : Erdos67.PrimeEstimates.primeReciprocals X ≤
      Real.log (X : ℝ))
    (hySize : (Real.log (X : ℝ)) ^ 4 ≤ (y : ℝ))
    (hQ₂ : ∀ p, (¬ P₁ p ∧ P₂ p) → p ≤ y)
    (hQ₃ : ∀ p, (¬ P₁ p ∧ ¬ P₂ p) → p ≤ y) :
    ‖gsA10TwoBlockTailoredIntegratedPrefix f hmul P₁ P₂ y X
          (Real.log (y : ℝ))⁻¹ -
        gsA10TwoBlockSourcePerronIntegrated f hmul P₁ P₂ y X
          (Real.log (y : ℝ))⁻¹ ((Real.log (X : ℝ)) ^ 2)‖ /
        (X : ℝ) ≤ gsA10JointMovingProjectionSourceBudget y X := by
  let eta : ℝ := (Real.log (y : ℝ))⁻¹
  let P : ℝ → ℝ → ℂ := fun alpha beta ↦
    positivePrefixSum
      (gsA10TwoBlockTailoredCoefficient
        f hmul P₁ P₂ y X alpha beta) X
  let Q : ℝ → ℝ → ℂ := fun alpha beta ↦
    gsA10TailoredPerronIntegral
      (gsA10TwoBlockAlternatingLow f P₁ P₂ y)
      (gsA9HighArithmetic f y)
      (gsA9HighGeneralizedMangoldt hmul y)
      y X (Erdos67.EulerResidue.taoExponent X) alpha beta
        ((Real.log (X : ℝ)) ^ 2)
  let NE : ℝ → ℝ → ℝ := fun alpha beta ↦
    dirichletPerronNearMass
        (gsA10TwoBlockTailoredCoefficient
          f hmul P₁ P₂ y X alpha beta) X
        ((Real.log (X : ℝ)) ^ 2) +
      (1 / 2 : ℝ) *
        ‖gsA10TwoBlockTailoredCoefficient
          f hmul P₁ P₂ y X alpha beta X‖
  let M : ℝ → ℝ → ℝ := fun alpha beta ↦
    gsA10SourcePerronMassEnvelope y X alpha beta
  let G : ℝ → ℝ → ℝ := fun alpha beta ↦ NE alpha beta + M alpha beta
  have hlogyPos : 0 < Real.log (y : ℝ) := by linarith
  have hetaPos : 0 < eta := by dsimp only [eta]; positivity
  have hetaOne : eta ≤ 1 := by
    dsimp only [eta]
    exact (inv_le_one₀ hlogyPos).2 (by linarith)
  have hP : Continuous (Function.uncurry P) := by
    simpa only [P] using
      continuous_positivePrefixSum_gsA10TwoBlockTailoredCoefficient
        hmul P₁ P₂ y X
  have hQ : ContinuousOn (Function.uncurry Q)
      (Set.Icc (0 : ℝ) eta ×ˢ Set.Icc (0 : ℝ) eta) := by
    simpa only [Q, eta] using
      continuousOn_uncurry_gsA10SourceTailoredPerronIntegral_sourceRectangle
        hmul hbound P₁ P₂ hX (by linarith : 4 ≤ Real.log (y : ℝ))
          (sq_nonneg _)
  have hnearCont : Continuous (Function.uncurry (fun alpha beta : ℝ ↦
      dirichletPerronNearMass
        (gsA10TwoBlockTailoredCoefficient
          f hmul P₁ P₂ y X alpha beta) X
        ((Real.log (X : ℝ)) ^ 2))) := by
    rw [show Function.uncurry (fun alpha beta : ℝ ↦
        dirichletPerronNearMass
          (gsA10TwoBlockTailoredCoefficient
            f hmul P₁ P₂ y X alpha beta) X
          ((Real.log (X : ℝ)) ^ 2)) =
        Function.uncurry (fun alpha beta : ℝ ↦
          ∑ n ∈ Finset.range (2 * X),
            ‖gsA10TwoBlockTailoredCoefficient
              f hmul P₁ P₂ y X alpha beta n‖ *
              dirichletPerronNearError X
                ((Real.log (X : ℝ)) ^ 2) n) by
      funext z
      rcases z with ⟨alpha, beta⟩
      simp only [Function.uncurry_apply_pair]
      unfold dirichletPerronNearMass
      rw [tsum_eq_sum (s := Finset.range (2 * X))]
      intro n hn
      have hnLower : 2 * X ≤ n := by simpa using hn
      have hnLowerR : (2 : ℝ) * X ≤ n := by exact_mod_cast hnLower
      rw [dirichletPerronNearError, if_neg]
      · simp
      · intro hh
        exact (not_lt_of_ge hnLowerR) hh.2.2.1]
    apply continuous_finsetSum
    intro n hn
    exact (continuous_uncurry_norm_gsA10TwoBlockTailoredCoefficient
      hmul P₁ P₂ y X n).mul continuous_const
  have hNE : Continuous (Function.uncurry NE) := by
    dsimp only [NE]
    exact hnearCont.add (continuous_const.mul
      (continuous_uncurry_norm_gsA10TwoBlockTailoredCoefficient
        hmul P₁ P₂ y X X))
  have hM : Continuous (Function.uncurry M) := by
    have hXne : (X : ℝ) ≠ 0 := by
      exact_mod_cast (show X ≠ 0 by omega)
    dsimp only [M, gsA10SourcePerronMassEnvelope,
      Function.uncurry_apply_pair]
    exact continuous_const.mul <| continuous_const.mul <|
      ((Real.continuous_const_rpow hXne).comp (by fun_prop)).mul
        ((Real.continuous_const_rpow hXne).comp (by fun_prop))
  have hG : Continuous (Function.uncurry G) := by
    change Continuous (Function.uncurry (fun alpha beta ↦
      NE alpha beta + M alpha beta))
    rw [show Function.uncurry (fun alpha beta ↦ NE alpha beta + M alpha beta) =
      Function.uncurry NE + Function.uncurry M by funext z; rfl]
    exact hNE.add hM
  have hpoint : ∀ alpha ∈ Set.Icc (0 : ℝ) eta,
      ∀ beta ∈ Set.Icc (0 : ℝ) eta,
        ‖P alpha beta - Q alpha beta‖ ≤ G alpha beta := by
    intro alpha halpha beta hbeta
    have hbase :=
      norm_positivePrefixSum_gsA10TwoBlockTailored_sub_sourcePerron_le_massEnvelope
        hmul hbound P₁ P₂ hy hX hlogX (by linarith) hQ₂ hQ₃
          halpha.1 halpha.2 hbeta.1 hbeta.2
    simpa only [P, Q, G, NE, M, eta, add_assoc, add_comm,
      add_left_comm] using hbase
  have havg :=
    norm_two_mul_doubleIntervalIntegral_sub_le_of_pointwise_continuousOn
      (P := P) (Q := Q) (G := G) hetaPos.le hP.continuousOn hQ
        hG.continuousOn hpoint
  have hX0 : (0 : ℝ) ≤ X := by positivity
  have havgDiv := div_le_div_of_nonneg_right havg hX0
  have hsplit := doubleIntervalIntegral_add_fixedSource
    (eta := eta) hNE hM
  have havg' :
      ‖gsA10TwoBlockTailoredIntegratedPrefix f hmul P₁ P₂ y X eta -
          gsA10TwoBlockSourcePerronIntegrated f hmul P₁ P₂ y X eta
            ((Real.log (X : ℝ)) ^ 2)‖ / (X : ℝ) ≤
        2 * (∫ alpha : ℝ in 0..eta,
          ∫ beta : ℝ in 0..eta, NE alpha beta) / (X : ℝ) +
        2 * (∫ alpha : ℝ in 0..eta,
          ∫ beta : ℝ in 0..eta, M alpha beta) / (X : ℝ) := by
    have hraw :
        ‖gsA10TwoBlockTailoredIntegratedPrefix f hmul P₁ P₂ y X eta -
            gsA10TwoBlockSourcePerronIntegrated f hmul P₁ P₂ y X eta
              ((Real.log (X : ℝ)) ^ 2)‖ / (X : ℝ) ≤
          2 * ((∫ alpha : ℝ in 0..eta,
            ∫ beta : ℝ in 0..eta, NE alpha beta) +
            (∫ alpha : ℝ in 0..eta,
              ∫ beta : ℝ in 0..eta, M alpha beta)) / (X : ℝ) := by
      simpa only [P, Q, G, gsA10TwoBlockTailoredIntegratedPrefix,
        gsA10TailoredIntegratedPrefix, gsA10TwoBlockTailoredCoefficient,
        gsA10TwoBlockSourcePerronIntegrated, hsplit] using havgDiv
    exact hraw.trans_eq (by ring)
  let J : ℝ :=
    4 * (harmonic X : ℝ) * Real.log (y : ℝ) /
        (Real.log (X : ℝ)) ^ 2 +
      Real.log (y : ℝ) / (2 * (X : ℝ))
  have hnear := source_doubleIntervalIntegral_tailored_near_add_half_le
    hmul hcomp hbound P₁ P₂ (show 2 ≤ y by omega) hX hQ₂ hQ₃
  have hnear' :
      (2 / (eta * (X : ℝ))) *
        (∫ alpha : ℝ in 0..eta,
          ∫ beta : ℝ in 0..eta, NE alpha beta) ≤ J := by
    simpa only [eta, NE, J] using hnear
  have hJ0 : 0 ≤ J := by
    dsimp only [J]
    have hH0 : 0 ≤ (harmonic X : ℝ) := gsA10_harmonic_cast_nonneg X
    positivity
  have hnearFinal :
      2 * (∫ alpha : ℝ in 0..eta,
        ∫ beta : ℝ in 0..eta, NE alpha beta) / (X : ℝ) ≤ J := by
    calc
      _ = eta * ((2 / (eta * (X : ℝ))) *
          (∫ alpha : ℝ in 0..eta,
            ∫ beta : ℝ in 0..eta, NE alpha beta)) := by
        field_simp [ne_of_gt hetaPos]
      _ ≤ eta * J := mul_le_mul_of_nonneg_left hnear' hetaPos.le
      _ ≤ J := by nlinarith
  have hmass :=
    two_mul_doubleIntervalIntegral_gsA10SourcePerronMassEnvelope_div_le_eta
      hX (show 3 ≤ y by omega) hlogX hprimeMass hySize hetaPos.le
  calc
    _ ≤ 2 * (∫ alpha : ℝ in 0..eta,
          ∫ beta : ℝ in 0..eta, NE alpha beta) / (X : ℝ) +
        2 * (∫ alpha : ℝ in 0..eta,
          ∫ beta : ℝ in 0..eta, M alpha beta) / (X : ℝ) := by
      simpa only [eta] using havg'
    _ ≤ J + gsA10MovingPerronAveragedMassConstant * eta :=
      add_le_add hnearFinal (by simpa only [M] using hmass)
    _ = gsA10JointMovingProjectionSourceBudget y X := by
      dsimp only [J, eta, gsA10JointMovingProjectionSourceBudget]

end


end Erdos67.MRHalaszBands

#print axioms
  Erdos67.MRHalaszBands.norm_gsA10TwoBlockTailoredIntegratedPrefix_sub_sourcePerronIntegrated_div_le_jointSource
