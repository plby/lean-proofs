import ErdosProblems.Erdos67b.MRTypicalCofactorFirstSecondary
import ErdosProblems.Erdos67b.MRTypicalCofactorPrimeSecondary
import ErdosProblems.Erdos67b.MRTypicalCofactorHigherSecondary

/-!
# Scalar secondary error for the actual typical cofactor

The exact prime/higher-power split is combined with the first Shiu sum.
The final theorem compares the actual cofactor prefix with its averaged
Perron transform, with all coefficient-side errors explicit.
-/

namespace Erdos67b

open MRHalaszBands

noncomputable section

theorem mrNorm_typicalCofactorSecondSecondary_le
    {ι : Type*} (A : Finset ℕ) (hA : ∀ p ∈ A, p.Prime)
    (J : Finset ι) (B : ι → Finset ℕ) (hB : ∀ j ∈ J, ∀ p ∈ B j, p.Prime)
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
    (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1) {y X : ℕ} (hy : 23 ≤ y) (hyX : y ≤ X)
    (hlogy : 6 ≤ Real.log (y : ℝ))
    (hAy : ∀ p ∈ A, p ≤ y) (hBy : ∀ j ∈ J, ∀ p ∈ B j, p ≤ y) :
    ‖gsA10SecondSecondaryPrefix (mrTypicalCofactorLowArithmetic A J B f y)
        (gsA9HighArithmetic f y) (gsA9HighGeneralizedMangoldt hmul y) X (Real.log (y : ℝ))⁻¹‖ ≤
      mrTypicalCofactorSecondSecondaryPrimeConstant *
          ((X : ℝ) / Real.log (X : ℝ)) * (1 + Real.log (y : ℝ)) +
        12 * (X : ℝ) * Real.log X / y * PrimeEstimates.primeReciprocals X := by
  have hlogyPos : 0 < Real.log (y : ℝ) := by linarith
  have heta : 0 ≤ (Real.log (y : ℝ))⁻¹ := (inv_pos.mpr hlogyPos).le
  have heta1 : (Real.log (y : ℝ))⁻¹ ≤ 1 :=
    (inv_le_one₀ hlogyPos).2 (by linarith)
  have hprime := mrNorm_typicalCofactorSecondSecondaryPrime_le A J B hmul hbound hy hyX hlogy
  have hhigher := mrNorm_typicalCofactorSecondSecondaryHigher_le
    A hA J B hB hmul hbound (by omega : 3 ≤ y) hyX hAy hBy heta heta1
  have hsplit := gsA9HighGeneralizedMangoldt_eq_primePart_add_higherPrimePowerPart hmul y
  conv_lhs => arg 1; arg 3; rw [hsplit]
  rw [gsA10SecondSecondaryPrefix_add]
  exact (norm_add_le _ _).trans (add_le_add hprime hhigher)

def mrTypicalCofactorSecondaryBound (y X : ℕ) : ℝ :=
  (gsA10ShiuConstant * Real.log (y : ℝ) +
    mrTypicalCofactorSecondSecondaryPrimeConstant * (1 + Real.log (y : ℝ))) /
      Real.log (X : ℝ) +
    12 * Real.log (X : ℝ) / y * PrimeEstimates.primeReciprocals X

theorem mrNorm_typicalCofactorSecondaries_div_le
    {ι : Type*} (A : Finset ℕ) (hA : ∀ p ∈ A, p.Prime)
    (J : Finset ι) (B : ι → Finset ℕ) (hB : ∀ j ∈ J, ∀ p ∈ B j, p.Prime)
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
    (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1) {y X : ℕ} (hy : 23 ≤ y) (hyX : y ≤ X)
    (hlogy : 6 ≤ Real.log (y : ℝ))
    (hAy : ∀ p ∈ A, p ≤ y) (hBy : ∀ j ∈ J, ∀ p ∈ B j, p ≤ y) :
    (‖gsA10FirstSecondaryPrefix (mrTypicalCofactorLowArithmetic A J B f y)
        (gsA9HighArithmetic f y) X (Real.log (y : ℝ))⁻¹‖ +
      ‖gsA10SecondSecondaryPrefix (mrTypicalCofactorLowArithmetic A J B f y)
        (gsA9HighArithmetic f y) (gsA9HighGeneralizedMangoldt hmul y) X (Real.log (y : ℝ))⁻¹‖) /
        (X : ℝ) ≤ mrTypicalCofactorSecondaryBound y X := by
  have hfirst := mrNorm_typicalCofactorFirstSecondary_le_log
    A hA J B hB hmul hbound (by omega : 2 ≤ y) hyX hAy hBy
  have hsecond := mrNorm_typicalCofactorSecondSecondary_le
    A hA J B hB hmul hbound hy hyX hlogy hAy hBy
  have hX : (X : ℝ) ≠ 0 := by exact_mod_cast (show X ≠ 0 by omega)
  have hsum := div_le_div_of_nonneg_right (add_le_add hfirst hsecond) (Nat.cast_nonneg X)
  apply hsum.trans_eq
  unfold mrTypicalCofactorSecondaryBound
  field_simp
  ring

theorem mrNorm_positivePrefix_typicalCofactor_sub_integratedPerron_div_le_source
    {ι : Type*} (A : Finset ℕ) (hA : ∀ p ∈ A, p.Prime)
    (J : Finset ι) (B : ι → Finset ℕ) (hB : ∀ j ∈ J, ∀ p ∈ B j, p.Prime)
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
    (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1) {y X : ℕ} (hy : 23 ≤ y) (hyX : y ≤ X)
    (hlogX : 1 ≤ Real.log (X : ℝ)) (hlogy : 6 ≤ Real.log (y : ℝ))
    (hAy : ∀ p ∈ A, p ≤ y) (hBy : ∀ j ∈ J, ∀ p ∈ B j, p ≤ y)
    (hprimeMass : PrimeEstimates.primeReciprocals X ≤ Real.log (X : ℝ))
    (hySize : (Real.log (X : ℝ)) ^ 4 ≤ (y : ℝ)) :
    ‖positivePrefixSum (mrIndexedTypicalCofactorCoefficient A J B f) X -
        mrTypicalCofactorIntegratedPerron A J B f hmul y X (Real.log (y : ℝ))⁻¹
          ((Real.log (X : ℝ)) ^ 2)‖ / (X : ℝ) ≤
      gsA10OrdinaryMovingProjectionAveragedBound y X (Real.log (y : ℝ))⁻¹ +
        mrTypicalCofactorSecondaryBound y X := by
  have heta : 0 ≤ (Real.log (y : ℝ))⁻¹ := inv_nonneg.mpr (by linarith)
  have hraw := mrNorm_positivePrefix_typicalCofactor_sub_integratedPerron_div_le
    A hA J B hB hmul hbound hy (by omega : 2 ≤ X) hlogX hlogy hAy hBy
    hprimeMass hySize heta le_rfl
  exact hraw.trans (add_le_add le_rfl
    (mrNorm_typicalCofactorSecondaries_div_le A hA J B hB hmul hbound hy hyX hlogy hAy hBy))

end

end Erdos67b
