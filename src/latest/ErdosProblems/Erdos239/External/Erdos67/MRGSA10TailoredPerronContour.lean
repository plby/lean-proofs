import ErdosProblems.Erdos239.External.Erdos67.MRGSA10TailoredPerronWindow
import ErdosProblems.Erdos239.External.Erdos67.MRGSA10LambdaWindowMass
import ErdosProblems.Erdos239.External.Erdos67.MRGSA10LambdaWindowMassScalar
import ErdosProblems.Erdos239.External.Erdos67.MRGSA10PerronErrorSchedule

/-!
# The source A.10 tailored Perron contour

This file inserts the lossless A.9 source-window product into the truncated
Perron integral.  The only analytic input retained is the shifted high-line
charge.  The two finite generalized-Mangoldt factors are discharged by their
proved coefficient-mass bound; no contour or prefix conclusion is assumed.
-/

open scoped BigOperators LSeries.notation
open Complex Set

namespace Erdos67.MRHalaszBands

noncomputable section

open BoundedGaps.Maynard

/-- The precise beta-shifted high-line charge left after A.13--A.14. -/
def gsA10SourceShiftedHighCharge
    (f : ℕ → ℂ) (X : ℕ) (beta t : ℝ) : ℝ :=
  let c := Erdos67.EulerResidue.taoExponent X
  let s : ℂ := ((c + beta : ℝ) : ℂ) + Complex.I * (t : ℂ)
  Real.sqrt ‖LSeries (gsA10SourceDeleted f) s‖ *
    Real.sqrt ‖riemannZeta ((c + beta : ℝ) : ℂ)‖

/-- The proved finite-window coefficient-mass scalar at the two source
lines `c-beta` and `c+beta`. -/
def gsA10SourceLambdaMassScalar (y X : ℕ) : ℝ :=
  (2 * (Real.log 4 + 4) * (Nat.log 2 X : ℝ)) ^ 2 *
    (X : ℝ) ^ (Real.log (y : ℝ))⁻¹

/-- The vertical-line scalar obtained from a bound `B` for the sole shifted
high charge. -/
def gsA10SourceUniformVerticalScalar
    (y X : ℕ) (B : ℝ) : ℝ :=
  Real.exp
      (28 * Real.exp 4 *
          Erdos67.EulerQuantitative.primeQuadraticConstant +
        36 * gsA9SourceShiftConstant) *
    B * gsA10SourceLambdaMassScalar y X

/-- A uniform scalar for the truncated Perron integral after the source
power and the lower bound `sigma ≥ 1/2` have been inserted. -/
def gsA10SourceUniformPerronScalar
    (y X : ℕ) (T B : ℝ) : ℝ :=
  (2 * Real.pi)⁻¹ *
    ((gsA10SourceUniformVerticalScalar y X B *
        (Real.exp 2 * X) / (1 / 2 : ℝ)) * (2 * T))

theorem gsA10SourceWindowCoreBudget_le_of_shiftedHighCharge
    {f : ℕ → ℂ} {y X : ℕ} {beta t B : ℝ}
    (hcharge : gsA10SourceShiftedHighCharge f X beta t ≤ B) :
    gsA10SourceWindowCoreBudget f y X beta t ≤
      Real.exp
          (28 * Real.exp 4 *
              Erdos67.EulerQuantitative.primeQuadraticConstant +
            36 * gsA9SourceShiftConstant) * B := by
  have h := mul_le_mul_of_nonneg_left hcharge
    (Real.exp_pos
      (28 * Real.exp 4 *
          Erdos67.EulerQuantitative.primeQuadraticConstant +
        36 * gsA9SourceShiftConstant)).le
  simpa only [gsA10SourceWindowCoreBudget,
    gsA10SourceShiftedHighCharge, mul_assoc] using h

/-- The mass envelope for the four-factor coefficient is scalarized using
the exact finite generalized-Mangoldt window theorem. -/
theorem gsA10SourceWindowMassBudget_le_uniformVerticalScalar
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
    (hcomp : IsCompletelyMultiplicativeOnPositive f)
    (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    {y X : ℕ} (hX : 2 ≤ X)
    (hlogy : 4 ≤ Real.log (y : ℝ))
    {beta t B : ℝ} (hbeta0 : 0 ≤ beta)
    (hbeta : beta ≤ (Real.log (y : ℝ))⁻¹)
    (hB : 0 ≤ B)
    (hcharge : gsA10SourceShiftedHighCharge f X beta t ≤ B) :
    gsA10SourceWindowMassBudget f hmul y X beta t ≤
      gsA10SourceUniformVerticalScalar y X B := by
  let g : ℕ → ℂ := gsA10SourceDeleted f
  let hmulG : IsMultiplicativeOnPositiveNat g :=
    gsDeletePrimeBand_isMultiplicativeOnPositiveNat hmul gsA9SmallPrime
  let c : ℝ := Erdos67.EulerResidue.taoExponent X
  let W : ArithmeticFunction ℂ :=
    gsA10LambdaWindow (gsA9HighGeneralizedMangoldt hmulG y) y X
  have hcore := gsA10SourceWindowCoreBudget_le_of_shiftedHighCharge
    (y := y) hcharge
  have hmass :
      dirichletPerronCoefficientMass W (c - beta) *
          dirichletPerronCoefficientMass W (c + beta) ≤
        gsA10SourceLambdaMassScalar y X := by
    simpa only [g, gsA10SourceDeleted, hmulG, c, W,
      gsA10SourceLambdaMassScalar] using
      mul_dirichletPerronCoefficientMass_gsA10SourceDeleted_sourceLines_le_rpow_inv_log
        hmul hcomp hbound hX hlogy hbeta0 hbeta
  have hmass0 :
      0 ≤ dirichletPerronCoefficientMass W (c - beta) *
        dirichletPerronCoefficientMass W (c + beta) := by
    apply mul_nonneg <;> unfold dirichletPerronCoefficientMass <;> positivity
  have hconst0 :
      0 ≤ Real.exp
          (28 * Real.exp 4 *
              Erdos67.EulerQuantitative.primeQuadraticConstant +
            36 * gsA9SourceShiftConstant) * B :=
    mul_nonneg (Real.exp_pos _).le hB
  unfold gsA10SourceWindowMassBudget
  dsimp only
  rw [mul_assoc]
  calc
    gsA10SourceWindowCoreBudget f y X beta t *
          (dirichletPerronCoefficientMass W (c - beta) *
            dirichletPerronCoefficientMass W (c + beta)) ≤
        (Real.exp
            (28 * Real.exp 4 *
                Erdos67.EulerQuantitative.primeQuadraticConstant +
              36 * gsA9SourceShiftConstant) * B) *
          (dirichletPerronCoefficientMass W (c - beta) *
            dirichletPerronCoefficientMass W (c + beta)) :=
      mul_le_mul_of_nonneg_right hcore hmass0
    _ ≤ (Real.exp
            (28 * Real.exp 4 *
                Erdos67.EulerQuantitative.primeQuadraticConstant +
              36 * gsA9SourceShiftConstant) * B) *
          gsA10SourceLambdaMassScalar y X :=
      mul_le_mul_of_nonneg_left hmass hconst0
    _ = gsA10SourceUniformVerticalScalar y X B := by
      unfold gsA10SourceUniformVerticalScalar
      ring

/-- Uniform vertical control of the exact four-factor coefficient, derived
from the shifted-high charge and the finite-window mass theorem. -/
theorem norm_LSeries_gsA10SourceTailored_le_uniformVerticalScalar
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
    (hcomp : IsCompletelyMultiplicativeOnPositive f)
    (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    (P₁ P₂ : ℕ → Prop) [DecidablePred P₁] [DecidablePred P₂]
    {y X : ℕ} (hy : 23 ≤ y) (hX : 2 ≤ X)
    {alpha beta t B : ℝ} (hlogy : 4 ≤ Real.log (y : ℝ))
    (halpha0 : 0 ≤ alpha)
    (halpha : alpha ≤ (Real.log (y : ℝ))⁻¹)
    (hbeta0 : 0 ≤ beta)
    (hbeta : beta ≤ (Real.log (y : ℝ))⁻¹)
    (hB : 0 ≤ B)
    (hcharge : gsA10SourceShiftedHighCharge f X beta t ≤ B) :
    ‖LSeries (gsA10SourceTailoredCoefficient
        f hmul P₁ P₂ y X alpha beta)
        (((Erdos67.EulerResidue.taoExponent X - alpha - beta : ℝ) : ℂ) +
      Complex.I * (t : ℂ))‖ ≤
      gsA10SourceUniformVerticalScalar y X B := by
  exact (norm_LSeries_gsA10TwoBlockTailoredCoefficient_le_A10WindowMass
    hmul hbound P₁ P₂ hy (by omega) hlogy
      halpha0 halpha hbeta0 hbeta).trans
    (gsA10SourceWindowMassBudget_le_uniformVerticalScalar
      hmul hcomp hbound hX hlogy hbeta0 hbeta hB hcharge)

/-- Pointwise tailored Perron integral bound.  Every factor except the
beta-shifted high-line charge is now explicit. -/
theorem norm_gsA10SourceTailoredPerronIntegral_le_of_shiftedHighCharge
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
    (hcomp : IsCompletelyMultiplicativeOnPositive f)
    (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    (P₁ P₂ : ℕ → Prop) [DecidablePred P₁] [DecidablePred P₂]
    {y X : ℕ} (hy : 23 ≤ y) (hX : 2 ≤ X)
    (hlogX : 1 ≤ Real.log (X : ℝ))
    (hlogy : 4 ≤ Real.log (y : ℝ))
    {alpha beta T B : ℝ}
    (halpha0 : 0 ≤ alpha)
    (halpha : alpha ≤ (Real.log (y : ℝ))⁻¹)
    (hbeta0 : 0 ≤ beta)
    (hbeta : beta ≤ (Real.log (y : ℝ))⁻¹)
    (hT : 0 ≤ T) (hB : 0 ≤ B)
    (hcharge : ∀ t : ℝ, |t| ≤ T →
      gsA10SourceShiftedHighCharge f X beta t ≤ B) :
    let g := gsA10SourceDeleted f
    let hmulG := gsDeletePrimeBand_isMultiplicativeOnPositiveNat
      hmul gsA9SmallPrime
    let sigma := Erdos67.EulerResidue.taoExponent X - alpha - beta
    ‖gsA10TailoredPerronIntegral
        (gsA10TwoBlockAlternatingLow g P₁ P₂ y)
        (gsA9HighArithmetic g y)
        (gsA9HighGeneralizedMangoldt hmulG y)
        y X (Erdos67.EulerResidue.taoExponent X) alpha beta T‖ ≤
      Erdos67.MRHalaszPerron.perronVerticalMajorant
        (gsA10SourceUniformVerticalScalar y X B) X sigma T := by
  dsimp only
  let g : ℕ → ℂ := gsA10SourceDeleted f
  let hmulG : IsMultiplicativeOnPositiveNat g :=
    gsDeletePrimeBand_isMultiplicativeOnPositiveNat hmul gsA9SmallPrime
  let sigma : ℝ := Erdos67.EulerResidue.taoExponent X - alpha - beta
  have hlogyPos : 0 < Real.log (y : ℝ) := by linarith
  have hetaQuarter : (Real.log (y : ℝ))⁻¹ ≤ 1 / 4 := by
    simpa only [one_div] using
      inv_anti₀ (by norm_num : (0 : ℝ) < 4) hlogy
  have hcOne : 1 ≤ Erdos67.EulerResidue.taoExponent X := by
    unfold Erdos67.EulerResidue.taoExponent
    have hlogXPos : 0 < Real.log (X : ℝ) := zero_lt_one.trans_le hlogX
    exact le_add_of_nonneg_right (inv_pos.mpr hlogXPos).le
  have hsigma : 0 < sigma := by
    dsimp only [sigma]
    have hab : alpha + beta ≤ 2 * (Real.log (y : ℝ))⁻¹ := by linarith
    linarith
  have hM : 0 ≤ gsA10SourceUniformVerticalScalar y X B := by
    unfold gsA10SourceUniformVerticalScalar gsA10SourceLambdaMassScalar
    positivity
  unfold gsA10TailoredPerronIntegral
  apply Erdos67.MRHalaszPerron.norm_dirichletPerronIntegral_le_of_uniform
    (by exact_mod_cast (show 0 < X by omega)) hsigma hT hM
  intro t ht
  rw [mul_comm (t : ℂ) Complex.I]
  exact norm_LSeries_gsA10SourceTailored_le_uniformVerticalScalar
    hmul hcomp hbound P₁ P₂ hy hX hlogy
      halpha0 halpha hbeta0 hbeta hB (hcharge t ht)

/-- On the source rectangle, the generic vertical Perron majorant is
uniformly bounded using `X^sigma ≤ exp(2) X` and `sigma ≥ 1/2`. -/
theorem perronVerticalMajorant_le_sourceUniformPerronScalar
    {y X : ℕ} (hX : 2 ≤ X)
    (hlogX : 1 ≤ Real.log (X : ℝ))
    (hlogy : 4 ≤ Real.log (y : ℝ))
    {alpha beta T B : ℝ}
    (halpha0 : 0 ≤ alpha)
    (halpha : alpha ≤ (Real.log (y : ℝ))⁻¹)
    (hbeta0 : 0 ≤ beta)
    (hbeta : beta ≤ (Real.log (y : ℝ))⁻¹)
    (hT : 0 ≤ T) (hB : 0 ≤ B) :
    Erdos67.MRHalaszPerron.perronVerticalMajorant
        (gsA10SourceUniformVerticalScalar y X B) X
        (Erdos67.EulerResidue.taoExponent X - alpha - beta) T ≤
      gsA10SourceUniformPerronScalar y X T B := by
  let sigma : ℝ := Erdos67.EulerResidue.taoExponent X - alpha - beta
  let M : ℝ := gsA10SourceUniformVerticalScalar y X B
  have hlogyPos : 0 < Real.log (y : ℝ) := by linarith
  have hetaQuarter : (Real.log (y : ℝ))⁻¹ ≤ 1 / 4 := by
    simpa only [one_div] using
      inv_anti₀ (by norm_num : (0 : ℝ) < 4) hlogy
  have hcOne : 1 ≤ Erdos67.EulerResidue.taoExponent X := by
    unfold Erdos67.EulerResidue.taoExponent
    have hlogXPos : 0 < Real.log (X : ℝ) := zero_lt_one.trans_le hlogX
    exact le_add_of_nonneg_right (inv_pos.mpr hlogXPos).le
  have hsigmaHalf : 1 / 2 ≤ sigma := by
    dsimp only [sigma]
    have hab : alpha + beta ≤ 2 * (Real.log (y : ℝ))⁻¹ := by linarith
    linarith
  have hsigma : 0 < sigma := (by norm_num : (0 : ℝ) < 1 / 2).trans_le hsigmaHalf
  have hM : 0 ≤ M := by
    dsimp only [M]
    unfold gsA10SourceUniformVerticalScalar gsA10SourceLambdaMassScalar
    positivity
  have hpow : (X : ℝ) ^ sigma ≤ Real.exp 2 * X := by
    dsimp only [sigma]
    exact rpow_sourcePerronLine_le_exp_two_mul hX halpha0 hbeta0
  have hnum : M * (X : ℝ) ^ sigma ≤ M * (Real.exp 2 * X) :=
    mul_le_mul_of_nonneg_left hpow hM
  have hfrac : M * (X : ℝ) ^ sigma / sigma ≤
      M * (Real.exp 2 * X) / (1 / 2 : ℝ) := by
    calc
      M * (X : ℝ) ^ sigma / sigma ≤
          M * (Real.exp 2 * X) / sigma :=
        div_le_div_of_nonneg_right hnum hsigma.le
      _ ≤ M * (Real.exp 2 * X) / (1 / 2 : ℝ) :=
        div_le_div_of_nonneg_left
          (mul_nonneg hM (by positivity)) (by norm_num) hsigmaHalf
  unfold Erdos67.MRHalaszPerron.perronVerticalMajorant
  unfold gsA10SourceUniformPerronScalar
  exact mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_right hfrac (by positivity))
    (inv_nonneg.mpr (by positivity))

/-- Source-uniform form of the pointwise tailored Perron estimate. -/
theorem norm_gsA10SourceTailoredPerronIntegral_le_sourceUniform
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
    (hcomp : IsCompletelyMultiplicativeOnPositive f)
    (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    (P₁ P₂ : ℕ → Prop) [DecidablePred P₁] [DecidablePred P₂]
    {y X : ℕ} (hy : 23 ≤ y) (hX : 2 ≤ X)
    (hlogX : 1 ≤ Real.log (X : ℝ))
    (hlogy : 4 ≤ Real.log (y : ℝ))
    {alpha beta T B : ℝ}
    (halpha0 : 0 ≤ alpha)
    (halpha : alpha ≤ (Real.log (y : ℝ))⁻¹)
    (hbeta0 : 0 ≤ beta)
    (hbeta : beta ≤ (Real.log (y : ℝ))⁻¹)
    (hT : 0 ≤ T) (hB : 0 ≤ B)
    (hcharge : ∀ t : ℝ, |t| ≤ T →
      gsA10SourceShiftedHighCharge f X beta t ≤ B) :
    let g := gsA10SourceDeleted f
    let hmulG := gsDeletePrimeBand_isMultiplicativeOnPositiveNat
      hmul gsA9SmallPrime
    ‖gsA10TailoredPerronIntegral
        (gsA10TwoBlockAlternatingLow g P₁ P₂ y)
        (gsA9HighArithmetic g y)
        (gsA9HighGeneralizedMangoldt hmulG y)
        y X (Erdos67.EulerResidue.taoExponent X) alpha beta T‖ ≤
      gsA10SourceUniformPerronScalar y X T B := by
  dsimp only
  exact (norm_gsA10SourceTailoredPerronIntegral_le_of_shiftedHighCharge
    hmul hcomp hbound P₁ P₂ hy hX hlogX hlogy
      halpha0 halpha hbeta0 hbeta hT hB hcharge).trans
    (perronVerticalMajorant_le_sourceUniformPerronScalar
      hX hlogX hlogy halpha0 halpha hbeta0 hbeta hT hB)

end

end Erdos67.MRHalaszBands

#print axioms
  Erdos67.MRHalaszBands.norm_gsA10SourceTailoredPerronIntegral_le_of_shiftedHighCharge
