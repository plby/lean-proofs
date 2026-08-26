import ErdosProblems.Erdos67b.MRGSA10LambdaVerticalSplit

/-!
# Higher-prime-power correction on the symmetric source lines

For the genuine A.10 pair `c₀-beta`, `c₀+beta`, the right line has no
absolute-mass growth and the left line costs only `(X/y)^beta`.  Retaining
this exact factor is essential: it cancels against the beta decay in the
Perron power before the auxiliary integration.
-/

namespace Erdos67b.MRHalaszBands

noncomputable section

private theorem harmonicBudget_nonneg (X : ℕ) :
    0 ≤ gsA10PrimeLambdaHarmonicBudget X := by
  unfold gsA10PrimeLambdaHarmonicBudget
  positivity

private theorem higherPrimePowerMass_nonneg (y X : ℕ) :
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

/-- Exact source-symmetric higher-prime-power split.  No `X^beta` upper
bound is taken: the natural ratio `(X/y)^beta` remains visible. -/
theorem gsA10LambdaVerticalSplitError_symmetric_le
    {y X : ℕ} (hy : 0 < y) (hyX : y ≤ X) (hX : 2 ≤ X)
    {beta : ℝ} (hbeta : 0 ≤ beta) :
    gsA10LambdaVerticalSplitError y X
        (Erdos67b.EulerResidue.taoExponent X - beta)
        (Erdos67b.EulerResidue.taoExponent X + beta) ≤
      ((X / y : ℕ) : ℝ) ^ beta *
        (2 * gsA10PrimeLambdaHarmonicBudget X *
            gsA10HigherPrimePowerGeometricMass y X +
          (gsA10HigherPrimePowerGeometricMass y X) ^ 2) := by
  let c : ℝ := Erdos67b.EulerResidue.taoExponent X
  let U : ℝ := (X / y : ℕ)
  let rho : ℝ := max (1 - (c - beta)) 0
  let R : ℝ := U ^ beta
  let H : ℝ := gsA10PrimeLambdaHarmonicBudget X
  let G : ℝ := gsA10HigherPrimePowerGeometricMass y X
  have hlogX : 0 < Real.log (X : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < X by omega))
  have hcOne : 1 ≤ c := by
    dsimp only [c, Erdos67b.EulerResidue.taoExponent]
    exact le_add_of_nonneg_right (inv_pos.mpr hlogX).le
  have hUNat : 1 ≤ X / y := Nat.one_le_iff_ne_zero.mpr
    (Nat.ne_of_gt (Nat.div_pos hyX hy))
  have hUOne : (1 : ℝ) ≤ U := by
    dsimp only [U]
    exact_mod_cast hUNat
  have hrho0 : 0 ≤ rho := by
    dsimp only [rho]
    exact le_max_right _ _
  have hrho : rho ≤ beta := by
    dsimp only [rho]
    apply max_le
    · linarith
    · exact hbeta
  have hRbound : U ^ rho ≤ R := by
    dsimp only [R]
    exact Real.rpow_le_rpow_of_exponent_le hUOne hrho
  have hR0 : 0 ≤ R := by
    dsimp only [R]
    positivity
  have hH0 : 0 ≤ H := by
    exact harmonicBudget_nonneg X
  have hG0 : 0 ≤ G := by
    exact higherPrimePowerMass_nonneg y X
  have hcHighGrowth : max (1 - (c + beta)) 0 = 0 := by
    exact max_eq_right (by linarith)
  have hPleft :
      gsA10PrimeLambdaAbsoluteBudget y X (c - beta) ≤ R * H := by
    unfold gsA10PrimeLambdaAbsoluteBudget
    change U ^ rho * H ≤ R * H
    exact mul_le_mul_of_nonneg_right hRbound hH0
  have hHleft :
      gsA10HigherPrimePowerLambdaAbsoluteBudget y X (c - beta) ≤
        R * G := by
    unfold gsA10HigherPrimePowerLambdaAbsoluteBudget
    change U ^ rho * G ≤ R * G
    exact mul_le_mul_of_nonneg_right hRbound hG0
  have hPright :
      gsA10PrimeLambdaAbsoluteBudget y X (c + beta) = H := by
    unfold gsA10PrimeLambdaAbsoluteBudget
    rw [hcHighGrowth, Real.rpow_zero, one_mul]
  have hHright :
      gsA10HigherPrimePowerLambdaAbsoluteBudget y X (c + beta) = G := by
    unfold gsA10HigherPrimePowerLambdaAbsoluteBudget
    rw [hcHighGrowth, Real.rpow_zero, one_mul]
  unfold gsA10LambdaVerticalSplitError
  change
    gsA10PrimeLambdaAbsoluteBudget y X (c - beta) *
          gsA10HigherPrimePowerLambdaAbsoluteBudget y X (c + beta) +
        gsA10HigherPrimePowerLambdaAbsoluteBudget y X (c - beta) *
          gsA10PrimeLambdaAbsoluteBudget y X (c + beta) +
        gsA10HigherPrimePowerLambdaAbsoluteBudget y X (c - beta) *
          gsA10HigherPrimePowerLambdaAbsoluteBudget y X (c + beta) ≤ _
  rw [hPright, hHright]
  calc
    gsA10PrimeLambdaAbsoluteBudget y X (c - beta) * G +
        gsA10HigherPrimePowerLambdaAbsoluteBudget y X (c - beta) * H +
        gsA10HigherPrimePowerLambdaAbsoluteBudget y X (c - beta) * G ≤
      (R * H) * G + (R * G) * H + (R * G) * G := by
        gcongr
    _ = R * (2 * H * G + G ^ 2) := by ring
    _ = _ := rfl

end

end Erdos67b.MRHalaszBands

#print axioms
  Erdos67b.MRHalaszBands.gsA10LambdaVerticalSplitError_symmetric_le
