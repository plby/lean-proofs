import ErdosProblems.Erdos67b.MRTypicalCofactorReconstruction

/-! # Shiu bound for the first actual cofactor secondary -/

namespace Erdos67b

open MRHalaszBands

noncomputable section

theorem mrShiuWeight_partialSum_le_log
    {y X : ℕ} (hy : 2 ≤ y) (hyX : y ≤ X) :
    HalberstamScratch.partialSum (gsA10ShiuWeight y (Real.log (y : ℝ))⁻¹) X ≤
      gsA10ShiuConstant * (X : ℝ) / Real.log (X : ℝ) * Real.log (y : ℝ) := by
  have hraw := gsA10ShiuWeight_partialSum_le hy hyX
  have hlogy : 0 < Real.log (y : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < y by omega))
  have hlogX : 0 < Real.log (X : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < X by omega))
  have hmertens := PrimeEstimates.abs_primeReciprocals_sub_log_log_le hy
  have hprime : PrimeEstimates.primeReciprocals y ≤
      Real.log (Real.log (y : ℝ)) + PrimeEstimates.mertensBound := by
    have := le_of_abs_le hmertens
    linarith
  have harg :
      PrimeEstimates.primeReciprocals y +
          (Real.log 2 + 2 * PrimeEstimates.mertensBound) +
          EulerQuantitative.primeQuadraticConstant ≤
        Real.log (Real.log (y : ℝ)) +
          (Real.log 2 + 3 * PrimeEstimates.mertensBound +
            EulerQuantitative.primeQuadraticConstant) := by
    linarith
  have hexp :
      Real.exp
          (PrimeEstimates.primeReciprocals y +
            (Real.log 2 + 2 * PrimeEstimates.mertensBound) +
            EulerQuantitative.primeQuadraticConstant) ≤
        Real.log (y : ℝ) *
          Real.exp (Real.log 2 + 3 * PrimeEstimates.mertensBound +
            EulerQuantitative.primeQuadraticConstant) := by
    calc
      _ ≤ Real.exp
          (Real.log (Real.log (y : ℝ)) +
            (Real.log 2 + 3 * PrimeEstimates.mertensBound +
              EulerQuantitative.primeQuadraticConstant)) :=
        Real.exp_le_exp.mpr harg
      _ = _ := by rw [Real.exp_add, Real.exp_log hlogy]
  have hfactor : 0 ≤
      (HalberstamScratch.explicitMassConstant 1 1 + 1) *
        (X : ℝ) / Real.log (X : ℝ) := by
    exact div_nonneg
      (mul_nonneg
        (add_nonneg
          (HalberstamScratch.explicitMassConstant_nonneg
            (by norm_num) (by norm_num)) zero_le_one)
        (Nat.cast_nonneg _)) hlogX.le
  calc
    _ ≤ (HalberstamScratch.explicitMassConstant 1 1 + 1) *
        (X : ℝ) / Real.log (X : ℝ) *
          Real.exp
            (PrimeEstimates.primeReciprocals y +
              (Real.log 2 + 2 * PrimeEstimates.mertensBound) +
              EulerQuantitative.primeQuadraticConstant) := hraw
    _ ≤ (HalberstamScratch.explicitMassConstant 1 1 + 1) *
        (X : ℝ) / Real.log (X : ℝ) *
          (Real.log (y : ℝ) *
            Real.exp (Real.log 2 + 3 * PrimeEstimates.mertensBound +
              EulerQuantitative.primeQuadraticConstant)) :=
      mul_le_mul_of_nonneg_left hexp hfactor
    _ = gsA10ShiuConstant * (X : ℝ) / Real.log (X : ℝ) *
        Real.log (y : ℝ) := by
      unfold gsA10ShiuConstant
      ring


theorem mrNorm_typicalCofactorFirstSecondary_le_partialSum
    {ι : Type*} (A : Finset ℕ) (hA : ∀ p ∈ A, p.Prime)
    (J : Finset ι) (B : ι → Finset ℕ) (hB : ∀ j ∈ J, ∀ p ∈ B j, p.Prime)
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
    (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1) (y X : ℕ)
    (hAy : ∀ p ∈ A, p ≤ y) (hBy : ∀ j ∈ J, ∀ p ∈ B j, p ≤ y) (eta : ℝ) :
    ‖gsA10FirstSecondaryPrefix (mrTypicalCofactorLowArithmetic A J B f y)
        (gsA9HighArithmetic f y) X eta‖ ≤
      HalberstamScratch.partialSum (gsA10ShiuWeight y eta) X := by
  unfold gsA10FirstSecondaryPrefix
  apply norm_positivePrefixSum_le_partialSum
  intro n hn
  have hnpos : 0 < n := (Finset.mem_Icc.mp hn).1
  rw [mrTypicalCofactorSecondary_apply A hA J B hB hmul y hAy hBy eta hnpos,
    norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)]
  simpa only [gsA10ShiuWeight, if_neg hnpos.ne'] using
    mul_le_of_le_one_right (gsA10ShiuWeight_nonneg y eta n)
    (mrIndexedTypicalCofactorCoefficient_norm_le_one A J B hbound hnpos)

theorem mrNorm_typicalCofactorFirstSecondary_le_log
    {ι : Type*} (A : Finset ℕ) (hA : ∀ p ∈ A, p.Prime)
    (J : Finset ι) (B : ι → Finset ℕ) (hB : ∀ j ∈ J, ∀ p ∈ B j, p.Prime)
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
    (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1) {y X : ℕ} (hy : 2 ≤ y) (hyX : y ≤ X)
    (hAy : ∀ p ∈ A, p ≤ y) (hBy : ∀ j ∈ J, ∀ p ∈ B j, p ≤ y) :
    ‖gsA10FirstSecondaryPrefix (mrTypicalCofactorLowArithmetic A J B f y)
        (gsA9HighArithmetic f y) X (Real.log (y : ℝ))⁻¹‖ ≤
      gsA10ShiuConstant * (X : ℝ) / Real.log (X : ℝ) * Real.log (y : ℝ) :=
  (mrNorm_typicalCofactorFirstSecondary_le_partialSum
    A hA J B hB hmul hbound y X hAy hBy _).trans (mrShiuWeight_partialSum_le_log hy hyX)

end

end Erdos67b
