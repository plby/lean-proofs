import ErdosProblems.Erdos67b.MRGSA10FixedHighVerticalContour

/-!
# Scalar higher-prime-power correction on the fixed-high contour

The two actual Mangoldt-window lines are `c₀ - 2β` and `c₀`.  Thus the
right line has no absolute-mass growth, while all three higher-prime-power
corrections on the left are covered by the single source factor
`X ^ (2 / log y)`.
-/

namespace Erdos67b.MRHalaszBands

noncomputable section

private theorem gsA10PrimeLambdaHarmonicBudget_nonneg (X : ℕ) :
    0 ≤ gsA10PrimeLambdaHarmonicBudget X := by
  unfold gsA10PrimeLambdaHarmonicBudget
  positivity

private theorem gsA10HigherPrimePowerGeometricMass_nonneg (y X : ℕ) :
    0 ≤ gsA10HigherPrimePowerGeometricMass y X := by
  unfold gsA10HigherPrimePowerGeometricMass
  apply Finset.sum_nonneg
  intro p hp
  apply mul_nonneg
  · exact Real.log_nonneg (by
      have hpPrime := (mem_primesUpTo.mp (Finset.mem_filter.mp hp).1).1
      exact_mod_cast hpPrime.one_le)
  · apply Finset.sum_nonneg
    intro k hk
    exact div_nonneg (sub_nonneg.mpr (one_le_pow₀ (by norm_num)))
      (pow_nonneg (Nat.cast_nonneg _) _)

/-- Exact source-square scalarization of the higher-prime-power correction
on the fixed-high pair. -/
theorem gsA10LambdaVerticalSplitError_fixedHigh_le
    {y X : ℕ} (hX : 1 ≤ X)
    {beta : ℝ} (hlogy : 0 < Real.log (y : ℝ))
    (_hbeta0 : 0 ≤ beta)
    (hbeta : beta ≤ (Real.log (y : ℝ))⁻¹) :
    gsA10LambdaVerticalSplitError y X
        (Erdos67b.EulerResidue.taoExponent X - 2 * beta)
        (Erdos67b.EulerResidue.taoExponent X) ≤
      (X : ℝ) ^ (2 * (Real.log (y : ℝ))⁻¹) *
        (2 * gsA10PrimeLambdaHarmonicBudget X *
            gsA10HigherPrimePowerGeometricMass y X +
          (gsA10HigherPrimePowerGeometricMass y X) ^ 2) := by
  let c : ℝ := Erdos67b.EulerResidue.taoExponent X
  let U : ℝ := (X / y : ℕ)
  let rho : ℝ := max (1 - (c - 2 * beta)) 0
  let R : ℝ := (X : ℝ) ^ (2 * (Real.log (y : ℝ))⁻¹)
  let H : ℝ := gsA10PrimeLambdaHarmonicBudget X
  let G : ℝ := gsA10HigherPrimePowerGeometricMass y X
  have hlogX : 0 ≤ Real.log (X : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hX)
  have hcOne : 1 ≤ c := by
    dsimp only [c, Erdos67b.EulerResidue.taoExponent]
    exact le_add_of_nonneg_right (inv_nonneg.mpr hlogX)
  have hrho0 : 0 ≤ rho := by
    dsimp only [rho]
    exact le_max_right _ _
  have hrho : rho ≤ 2 * (Real.log (y : ℝ))⁻¹ := by
    dsimp only [rho]
    apply max_le
    · linarith
    · positivity
  have hU0 : 0 ≤ U := by positivity
  have hUX : U ≤ (X : ℝ) := by
    dsimp only [U]
    exact_mod_cast Nat.div_le_self X y
  have hX0 : (0 : ℝ) ≤ X := by positivity
  have hRbound : U ^ rho ≤ R := by
    calc
      U ^ rho ≤ (X : ℝ) ^ rho :=
        Real.rpow_le_rpow hU0 hUX hrho0
      _ ≤ (X : ℝ) ^ (2 * (Real.log (y : ℝ))⁻¹) :=
        Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hX) hrho
      _ = R := rfl
  have hR0 : 0 ≤ R := Real.rpow_nonneg hX0 _
  have hH0 : 0 ≤ H := by
    exact gsA10PrimeLambdaHarmonicBudget_nonneg X
  have hG0 : 0 ≤ G := by
    exact gsA10HigherPrimePowerGeometricMass_nonneg y X
  have hcGrowth : max (1 - c) 0 = 0 := by
    exact max_eq_right (by linarith)
  have hPleft : gsA10PrimeLambdaAbsoluteBudget y X (c - 2 * beta) ≤
      R * H := by
    unfold gsA10PrimeLambdaAbsoluteBudget
    change U ^ rho * H ≤ R * H
    exact mul_le_mul_of_nonneg_right hRbound hH0
  have hHleft :
      gsA10HigherPrimePowerLambdaAbsoluteBudget y X (c - 2 * beta) ≤
        R * G := by
    unfold gsA10HigherPrimePowerLambdaAbsoluteBudget
    change U ^ rho * G ≤ R * G
    exact mul_le_mul_of_nonneg_right hRbound hG0
  have hPright : gsA10PrimeLambdaAbsoluteBudget y X c = H := by
    unfold gsA10PrimeLambdaAbsoluteBudget
    rw [hcGrowth, Real.rpow_zero, one_mul]
  have hHright : gsA10HigherPrimePowerLambdaAbsoluteBudget y X c = G := by
    unfold gsA10HigherPrimePowerLambdaAbsoluteBudget
    rw [hcGrowth, Real.rpow_zero, one_mul]
  have hPleft0 : 0 ≤
      gsA10PrimeLambdaAbsoluteBudget y X (c - 2 * beta) := by
    unfold gsA10PrimeLambdaAbsoluteBudget
    positivity
  have hHleft0 : 0 ≤
      gsA10HigherPrimePowerLambdaAbsoluteBudget y X (c - 2 * beta) := by
    unfold gsA10HigherPrimePowerLambdaAbsoluteBudget
    positivity
  unfold gsA10LambdaVerticalSplitError
  change
    gsA10PrimeLambdaAbsoluteBudget y X (c - 2 * beta) *
          gsA10HigherPrimePowerLambdaAbsoluteBudget y X c +
        gsA10HigherPrimePowerLambdaAbsoluteBudget y X (c - 2 * beta) *
          gsA10PrimeLambdaAbsoluteBudget y X c +
        gsA10HigherPrimePowerLambdaAbsoluteBudget y X (c - 2 * beta) *
          gsA10HigherPrimePowerLambdaAbsoluteBudget y X c ≤ _
  rw [hPright, hHright]
  calc
    gsA10PrimeLambdaAbsoluteBudget y X (c - 2 * beta) * G +
        gsA10HigherPrimePowerLambdaAbsoluteBudget y X (c - 2 * beta) * H +
        gsA10HigherPrimePowerLambdaAbsoluteBudget y X (c - 2 * beta) * G ≤
      (R * H) * G + (R * G) * H + (R * G) * G := by
        gcongr
    _ = R * (2 * H * G + G ^ 2) := by ring
    _ = _ := rfl

end

end Erdos67b.MRHalaszBands
