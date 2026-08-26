import ErdosProblems.Erdos67b.MRTypicalCofactorWeightedAverage
import ErdosProblems.Erdos67b.MRGSA10SmallPowerHPPScalar

/-!
# Decay of the complete uniform cofactor higher-prime-power error

The moving exponent is retained until the geometric prime-power mass is
bounded. A twelfth-power logarithmic cutoff absorbs its square-root cost.
-/

namespace Erdos67b

open MRHalaszBands

noncomputable section

theorem mrCofactor_uniformGrowth_le_sqrt {y X : ℕ}
    (hX : 0 < X) (hlogy : 0 < Real.log (y : ℝ))
    (hlogSquare : 4 * Real.log (X : ℝ) ≤ Real.log (y : ℝ) ^ 2) :
    (X : ℝ) ^ (2 * (Real.log (y : ℝ))⁻¹) ≤ Real.sqrt (y : ℝ) := by
  have hy : (0 : ℝ) < y := by
    have hyne : y ≠ 0 := by intro h; simp [h] at hlogy
    exact_mod_cast Nat.pos_of_ne_zero hyne
  rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos (by exact_mod_cast hX),
    Real.rpow_def_of_pos hy]
  apply Real.exp_le_exp.mpr
  have hdiv : 2 * Real.log (X : ℝ) / Real.log (y : ℝ) ≤ Real.log (y : ℝ) / 2 := by
    apply (div_le_iff₀ hlogy).2
    nlinarith
  simpa only [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm, one_mul] using hdiv

theorem mrCofactor_uniformGrowth_mul_higherMass_le {y X : ℕ}
    (hX : 2 ≤ X) (hy : 3 ≤ y) (hlogX : 1 ≤ Real.log (X : ℝ))
    (hprime : PrimeEstimates.primeReciprocals X ≤ Real.log (X : ℝ))
    (hlogSquare : 4 * Real.log (X : ℝ) ≤ Real.log (y : ℝ) ^ 2)
    (hlogTwelve : Real.log (X : ℝ) ^ 12 ≤ (y : ℝ)) :
    (X : ℝ) ^ (2 * (Real.log (y : ℝ))⁻¹) * gsA10HigherPrimePowerGeometricMass y X ≤
      12 / Real.log (X : ℝ) ^ 4 := by
  let L := Real.log (X : ℝ)
  have hL : 0 < L := zero_lt_one.trans_le hlogX
  have hypos : (0 : ℝ) < y := by positivity
  have hspos : 0 < Real.sqrt (y : ℝ) := Real.sqrt_pos.2 hypos
  have hlogy : 0 < Real.log (y : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < y by omega))
  have hgrowth := mrCofactor_uniformGrowth_le_sqrt (show 0 < X by omega) hlogy hlogSquare
  have hmass : gsA10HigherPrimePowerGeometricMass y X ≤ 12 * L ^ 2 / (y : ℝ) := by
    calc
      _ ≤ 12 * L / (y : ℝ) * PrimeEstimates.primeReciprocals X :=
        gsA10HigherPrimePowerGeometricMass_le hy
      _ ≤ 12 * L / (y : ℝ) * L := mul_le_mul_of_nonneg_left hprime (by positivity)
      _ = _ := by ring
  have hs : L ^ 6 ≤ Real.sqrt (y : ℝ) := by
    apply (Real.le_sqrt (by positivity) (Nat.cast_nonneg y)).2
    simpa only [← pow_mul] using hlogTwelve
  calc
    _ ≤ Real.sqrt (y : ℝ) * (12 * L ^ 2 / (y : ℝ)) :=
      mul_le_mul hgrowth hmass (gsA10HigherPrimePowerGeometricMass_nonneg_source y X)
        (Real.sqrt_nonneg _)
    _ = 12 * L ^ 2 / Real.sqrt (y : ℝ) := by
      field_simp
      nlinarith [Real.sq_sqrt (Nat.cast_nonneg y)]
    _ ≤ 12 * L ^ 2 / L ^ 6 :=
      div_le_div_of_nonneg_left (by positivity) (pow_pos hL 6) hs
    _ = 12 / Real.log (X : ℝ) ^ 4 := by
      change 12 * L ^ 2 / L ^ 6 = 12 / L ^ 4
      field_simp

theorem mrCofactor_uniformHigherPowerFactor_le {y X : ℕ}
    (hX : 2 ≤ X) (hy : 3 ≤ y) (hlogX : 1 ≤ Real.log (X : ℝ))
    (hprime : PrimeEstimates.primeReciprocals X ≤ Real.log (X : ℝ))
    (hlogSquare : 4 * Real.log (X : ℝ) ≤ Real.log (y : ℝ) ^ 2)
    (hlogTwelve : Real.log (X : ℝ) ^ 12 ≤ (y : ℝ)) :
    4 * Real.log (X : ℝ) ^ 2 * mrWeightedCofactorUniformSplitError y X ≤
      gsA10SourceHPPRectangleBound / Real.log (X : ℝ) := by
  let L := Real.log (X : ℝ)
  let H := gsA10PrimeLambdaHarmonicBudget X
  let G := gsA10HigherPrimePowerGeometricMass y X
  let W := (X : ℝ) ^ (2 * (Real.log (y : ℝ))⁻¹)
  let C := gsA10PrimeLambdaHarmonicLogConstant
  have hL : 0 < L := zero_lt_one.trans_le hlogX
  have hG : 0 ≤ G := gsA10HigherPrimePowerGeometricMass_nonneg_source y X
  have hC : 0 ≤ C := gsA10PrimeLambdaHarmonicLogConstant_nonneg
  have hH : H ≤ C * L := gsA10PrimeLambdaHarmonicBudget_le_log hX
  have hW : 1 ≤ W := by
    apply Real.one_le_rpow (by exact_mod_cast (show 1 ≤ X by omega))
    have hlogy : 0 ≤ Real.log (y : ℝ) := Real.log_nonneg (by exact_mod_cast (show 1 ≤ y by omega))
    positivity
  have hWG : W * G ≤ 12 / L ^ 4 :=
    mrCofactor_uniformGrowth_mul_higherMass_le hX hy hlogX hprime hlogSquare hlogTwelve
  have hGbound : G ≤ 12 / L ^ 4 :=
    (le_mul_of_one_le_left hG hW).trans hWG
  have hLsix : L ≤ L ^ 6 := by
    calc
      L = L ^ 1 := by ring
      _ ≤ L ^ 6 := pow_le_pow_right₀ hlogX (by norm_num)
  calc
    _ = 4 * L ^ 2 * (2 * H * (W * G) + (W * G) * G) := by
      dsimp only [L, H, G, W, mrWeightedCofactorUniformSplitError]
      ring
    _ ≤ 4 * L ^ 2 * (2 * (C * L) * (12 / L ^ 4) + (12 / L ^ 4) ^ 2) := by
      have hW0 : 0 ≤ W := zero_le_one.trans hW
      have hH0 : 0 ≤ H := by dsimp only [H, gsA10PrimeLambdaHarmonicBudget]; positivity
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply add_le_add
      · gcongr
      · simpa only [sq] using mul_le_mul hWG hGbound hG (by positivity : 0 ≤ 12 / L ^ 4)
    _ = 96 * C / L + 576 / L ^ 6 := by field_simp; ring
    _ ≤ 96 * C / L + 576 / L :=
      add_le_add le_rfl (div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 576) hL hLsix)
    _ = gsA10SourceHPPRectangleBound / Real.log (X : ℝ) := by
      dsimp only [gsA10SourceHPPRectangleBound, C, L]
      ring

end

end Erdos67b
