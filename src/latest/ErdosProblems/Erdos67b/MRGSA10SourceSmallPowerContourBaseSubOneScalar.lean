import ErdosProblems.Erdos67b.MRGSA10SourceMovingBaseSubOneScalar
import ErdosProblems.Erdos67b.MRGSA10SourceSmallPowerRowScalar
import ErdosProblems.Erdos67b.MRGSA10SmallPowerHPPScalar
import ErdosProblems.Erdos67b.MRGSA10RestoredPerronScalar

/-!
# Two-scale scalar for the fixed source contour

The minimizer dichotomy is based at `X`, while the contour is evaluated at
each `Z ∈ [X,3X]`.  This is the exact small-power contour scalar after the
one-unit distance loss at the base scale.
-/

namespace Erdos67b.MRHalaszBands

noncomputable section

def gsA10SmallPowerSourceContourBaseSubOneConstant (Cbeta : ℝ) : ℝ :=
  ((2 * Real.pi)⁻¹ * (3 * gsA9SmallPrimeEulerBound) *
      Real.exp
        (28 * Real.exp 4 *
            Erdos67b.EulerQuantitative.primeQuadraticConstant +
          36 * gsA9SourceShiftConstant) * Real.exp 1) *
    gsA10SourceMovingBaseSubOneMaximumConstant *
    (2 * gsA10SmallPowerSourceRowBound Cbeta *
        (2 * gsA10PrimeLambdaSymmetricBetaScalarConstant) +
      gsA10SourceHPPRectangleBound)

theorem gsA10SmallPowerSourceContourBaseSubOneConstant_nonneg
    {Cbeta : ℝ} (hCbeta : 1 ≤ Cbeta) :
    0 ≤ gsA10SmallPowerSourceContourBaseSubOneConstant Cbeta := by
  unfold gsA10SmallPowerSourceContourBaseSubOneConstant
  have hsmall : 0 ≤ gsA9SmallPrimeEulerBound :=
    gsA9SmallPrimeEulerBound_nonneg_restored
  have hrow := gsA10SmallPowerSourceRowBound_nonneg hCbeta
  have hdiag := gsA10PrimeLambdaSymmetricBetaScalarConstant_nonneg
  have hhpp := gsA10SourceHPPRectangleBound_nonneg
  have hmax := gsA10SourceMovingBaseSubOneMaximumConstant_pos.le
  positivity

theorem gsA10_fixedSource_normalizedBudget_smallPower_base_sub_one_le
    {Cbeta : ℝ} (hCbeta : 1 ≤ Cbeta)
    {X Z y : ℕ} (hX : 3 ≤ X) (hXZ : X ≤ Z) (hZX : Z ≤ 3 * X)
    (hZ : 4 ≤ Z) (hy : 3 ≤ y)
    (hthreshold : 1 ≤ Erdos67b.realPrefixMovingThreshold X)
    (hlog : 1 ≤ Real.log (Z : ℝ))
    (hprime : Erdos67b.PrimeEstimates.primeReciprocals Z ≤
      Real.log (Z : ℝ))
    (hlogFour : Real.log (Z : ℝ) ^ 4 ≤ (y : ℝ))
    (hlogSix : Real.log (Z : ℝ) ^ 6 ≤ (y : ℝ)) :
    ((2 * Real.pi)⁻¹ * (3 * gsA9SmallPrimeEulerBound) *
        Real.exp
          (28 * Real.exp 4 *
              Erdos67b.EulerQuantitative.primeQuadraticConstant +
            36 * gsA9SourceShiftConstant) * Real.exp 1) *
      (gsA10SourceMaximumModulusSqrtScalar
          (Erdos67b.realPrefixMovingThreshold X - 1) Z /
        Real.sqrt (Real.log (Z : ℝ))) *
      (2 *
          (Real.exp 1 * Real.sqrt Real.pi *
            (gsA10PrimeSourceAffineRowConstant Cbeta +
              gsA10PrimeSourceAffineRowSlope Cbeta y Z *
                Real.log (Z : ℝ) ^ 2)) *
          (2 * gsA10PrimeLambdaSymmetricBetaScalarConstant) +
        4 * Real.log (Z : ℝ) ^ 2 *
          (2 * gsA10PrimeLambdaHarmonicBudget Z *
                gsA10HigherPrimePowerGeometricMass y Z +
            (gsA10HigherPrimePowerGeometricMass y Z) ^ 2) *
          (Real.log (y : ℝ))⁻¹) ≤
      gsA10SmallPowerSourceContourBaseSubOneConstant Cbeta *
        (Real.log (Z : ℝ)) ^ (-(1 / 1000 : ℝ)) := by
  let P : ℝ :=
    (2 * Real.pi)⁻¹ * (3 * gsA9SmallPrimeEulerBound) *
      Real.exp
        (28 * Real.exp 4 *
            Erdos67b.EulerQuantitative.primeQuadraticConstant +
          36 * gsA9SourceShiftConstant) * Real.exp 1
  let M : ℝ := gsA10SourceMovingBaseSubOneMaximumConstant
  let R : ℝ := gsA10SmallPowerSourceRowBound Cbeta
  let D : ℝ := gsA10PrimeLambdaSymmetricBetaScalarConstant
  let H : ℝ := gsA10SourceHPPRectangleBound
  let L : ℝ := Real.log (Z : ℝ)
  have hsmall : 0 ≤ gsA9SmallPrimeEulerBound :=
    gsA9SmallPrimeEulerBound_nonneg_restored
  have hP : 0 ≤ P := by dsimp only [P]; positivity
  have hM : 0 ≤ M := by
    dsimp only [M]
    exact gsA10SourceMovingBaseSubOneMaximumConstant_pos.le
  have hR : 0 ≤ R := by
    dsimp only [R]
    exact gsA10SmallPowerSourceRowBound_nonneg hCbeta
  have hD : 0 ≤ D := by
    dsimp only [D]
    exact gsA10PrimeLambdaSymmetricBetaScalarConstant_nonneg
  have hH : 0 ≤ H := by
    dsimp only [H]
    exact gsA10SourceHPPRectangleBound_nonneg
  have hL : (1 : ℝ) ≤ L := by simpa only [L] using hlog
  have hmax :
      gsA10SourceMaximumModulusSqrtScalar
            (Erdos67b.realPrefixMovingThreshold X - 1) Z /
          Real.sqrt L ≤ M * L ^ (-(1 / 200 : ℝ)) := by
    simpa only [M, L] using
      gsA10SourceMaximumModulusSqrtScalar_moving_base_sub_one_le
        hX hXZ hZX hthreshold
  have hlog4 : Real.log 4 ≤ L := by
    dsimp only [L]
    exact Real.log_le_log (by norm_num) (by exact_mod_cast hZ)
  have hrow :
      Real.exp 1 * Real.sqrt Real.pi *
          (gsA10PrimeSourceAffineRowConstant Cbeta +
            gsA10PrimeSourceAffineRowSlope Cbeta y Z * L ^ 2) ≤ R := by
    simpa only [R, L] using
      gsA10PrimeSourceAffineRow_smallPower_mul_log_sq_le
        hCbeta (show 0 < y by omega) hlog4 hlogFour
  have hhpp :
      4 * L ^ 2 *
          (2 * gsA10PrimeLambdaHarmonicBudget Z *
                gsA10HigherPrimePowerGeometricMass y Z +
            (gsA10HigherPrimePowerGeometricMass y Z) ^ 2) *
          (Real.log (y : ℝ))⁻¹ ≤ H := by
    simpa only [H, L] using
      gsA10SourceHPPRectangleFactor_le
        (show 2 ≤ Z by omega) hy hlog hprime hlogSix
  have hdiag0 : 0 ≤ 2 * D := by positivity
  have hrowMul := mul_le_mul_of_nonneg_right hrow hdiag0
  have hbracket :
      2 *
          (Real.exp 1 * Real.sqrt Real.pi *
            (gsA10PrimeSourceAffineRowConstant Cbeta +
              gsA10PrimeSourceAffineRowSlope Cbeta y Z * L ^ 2)) *
          (2 * D) +
        4 * L ^ 2 *
          (2 * gsA10PrimeLambdaHarmonicBudget Z *
                gsA10HigherPrimePowerGeometricMass y Z +
            (gsA10HigherPrimePowerGeometricMass y Z) ^ 2) *
          (Real.log (y : ℝ))⁻¹ ≤
        2 * R * (2 * D) + H := by
    calc
      _ = 2 *
            ((Real.exp 1 * Real.sqrt Real.pi *
              (gsA10PrimeSourceAffineRowConstant Cbeta +
                gsA10PrimeSourceAffineRowSlope Cbeta y Z * L ^ 2)) *
              (2 * D)) +
          4 * L ^ 2 *
            (2 * gsA10PrimeLambdaHarmonicBudget Z *
                  gsA10HigherPrimePowerGeometricMass y Z +
              (gsA10HigherPrimePowerGeometricMass y Z) ^ 2) *
            (Real.log (y : ℝ))⁻¹ := by ring
      _ ≤ 2 * (R * (2 * D)) + H :=
        add_le_add (mul_le_mul_of_nonneg_left hrowMul (by norm_num)) hhpp
      _ = _ := by ring
  have hweak : L ^ (-(1 / 200 : ℝ)) ≤
      L ^ (-(1 / 1000 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le hL (by norm_num)
  have hrowActual0 : 0 ≤
      Real.exp 1 * Real.sqrt Real.pi *
        (gsA10PrimeSourceAffineRowConstant Cbeta +
          gsA10PrimeSourceAffineRowSlope Cbeta y Z * L ^ 2) := by
    have hA := gsA10PrimeSourceAffineRowConstant_nonneg hCbeta
    have hB := gsA10PrimeSourceAffineRowSlope_nonneg hCbeta
      (show 1 ≤ y by omega) (show 1 ≤ Z by omega)
    positivity
  have hHG0 : 0 ≤
      2 * gsA10PrimeLambdaHarmonicBudget Z *
            gsA10HigherPrimePowerGeometricMass y Z +
        (gsA10HigherPrimePowerGeometricMass y Z) ^ 2 := by
    have hHarm : 0 ≤ gsA10PrimeLambdaHarmonicBudget Z := by
      unfold gsA10PrimeLambdaHarmonicBudget
      positivity
    have hMass := gsA10HigherPrimePowerGeometricMass_nonneg_source y Z
    positivity
  have hlogyPos : 0 < Real.log (y : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < y by omega))
  have hbracket0 : 0 ≤
      2 *
          (Real.exp 1 * Real.sqrt Real.pi *
            (gsA10PrimeSourceAffineRowConstant Cbeta +
              gsA10PrimeSourceAffineRowSlope Cbeta y Z * L ^ 2)) *
          (2 * D) +
        4 * L ^ 2 *
          (2 * gsA10PrimeLambdaHarmonicBudget Z *
                gsA10HigherPrimePowerGeometricMass y Z +
            (gsA10HigherPrimePowerGeometricMass y Z) ^ 2) *
          (Real.log (y : ℝ))⁻¹ := by
    positivity
  change P * _ * _ ≤ _
  calc
    P *
          (gsA10SourceMaximumModulusSqrtScalar
              (Erdos67b.realPrefixMovingThreshold X - 1) Z /
            Real.sqrt L) * _ ≤
        P * (M * L ^ (-(1 / 200 : ℝ))) *
          (2 * R * (2 * D) + H) := by
      exact mul_le_mul
        (mul_le_mul_of_nonneg_left hmax hP) hbracket hbracket0
        (mul_nonneg hP (mul_nonneg hM (by positivity)))
    _ = (P * M * (2 * R * (2 * D) + H)) *
        L ^ (-(1 / 200 : ℝ)) := by ring
    _ ≤ (P * M * (2 * R * (2 * D) + H)) *
        L ^ (-(1 / 1000 : ℝ)) := by
      exact mul_le_mul_of_nonneg_left hweak
        (mul_nonneg (mul_nonneg hP hM) (by positivity))
    _ = gsA10SmallPowerSourceContourBaseSubOneConstant Cbeta *
        (Real.log (Z : ℝ)) ^ (-(1 / 1000 : ℝ)) := by
      dsimp only [P, M, R, D, H, L,
        gsA10SmallPowerSourceContourBaseSubOneConstant]

end

end Erdos67b.MRHalaszBands

#print axioms
  Erdos67b.MRHalaszBands.gsA10_fixedSource_normalizedBudget_smallPower_base_sub_one_le
