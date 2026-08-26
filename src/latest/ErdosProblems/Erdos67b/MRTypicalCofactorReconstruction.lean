import ErdosProblems.Erdos67b.MRTypicalCofactorProjectionAverage
import ErdosProblems.Erdos67b.MRGSA10GlobalWindowExact

/-!
# Exact reconstruction of the actual typical cofactor prefix

The high Mangoldt support makes finite windowing exact. The actual prefix
is the tailored rectangle plus the two genuine secondary prefixes. Its
comparison with the averaged Perron transform has no assumed regularity
or hidden truncation error.
-/

open scoped BigOperators Classical
open Set MeasureTheory

namespace Erdos67b

open MRHalaszBands BoundedGaps.Maynard

noncomputable section

theorem mrPositivePrefixSum_toArithmeticFunction (f : ℕ → ℂ) (X : ℕ) :
    positivePrefixSum (toArithmeticFunction f) X = positivePrefixSum f X := by
  simp only [positivePrefixSum, Finset.sum_range_succ', add_sub_cancel_right]
  apply Finset.sum_congr rfl
  intro n _
  simp [toArithmeticFunction]

theorem mrTypicalCofactorFullIntegratedPrefix_eq_tailored {ι : Type*}
    (A : Finset ℕ) (J : Finset ι) (B : ι → Finset ℕ)
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
    {y X : ℕ} (hy : 0 < y) (eta : ℝ) :
    gsA10FullIntegratedPrefix (mrTypicalCofactorLowArithmetic A J B f y)
        (gsA9HighArithmetic f y) (gsA9HighGeneralizedMangoldt hmul y) X eta =
      gsA10TailoredIntegratedPrefix (mrTypicalCofactorLowArithmetic A J B f y)
        (gsA9HighArithmetic f y) (gsA9HighGeneralizedMangoldt hmul y) y X eta := by
  apply gsA10FullIntegratedPrefix_eq_tailored_of_lambda_support _ _ _ hy
  intro k hk
  by_contra hky
  exact hk (gsA9HighGeneralizedMangoldt_eq_zero_of_le hmul y (not_lt.mp hky))

theorem mrPositivePrefix_typicalCofactor_eq_tailored_add_secondaries
    {ι : Type*} (A : Finset ℕ) (hA : ∀ p ∈ A, p.Prime)
    (J : Finset ι) (B : ι → Finset ℕ) (hB : ∀ j ∈ J, ∀ p ∈ B j, p.Prime)
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
    {y X : ℕ} (hy : 0 < y)
    (hAy : ∀ p ∈ A, p ≤ y) (hBy : ∀ j ∈ J, ∀ p ∈ B j, p ≤ y) (eta : ℝ) :
    positivePrefixSum (mrIndexedTypicalCofactorCoefficient A J B f) X =
      gsA10TailoredIntegratedPrefix (mrTypicalCofactorLowArithmetic A J B f y)
          (gsA9HighArithmetic f y) (gsA9HighGeneralizedMangoldt hmul y) y X eta +
        gsA10FirstSecondaryPrefix (mrTypicalCofactorLowArithmetic A J B f y)
          (gsA9HighArithmetic f y) X eta +
        gsA10SecondSecondaryPrefix (mrTypicalCofactorLowArithmetic A J B f y)
          (gsA9HighArithmetic f y) (gsA9HighGeneralizedMangoldt hmul y) X eta := by
  have hid := two_mul_intervalIntegral_intervalIntegral_gsA10FullCoefficient_eq
    (mrTypicalCofactorLowArithmetic A J B f y) (gsA9HighArithmetic f y)
    (gsA9HighGeneralizedMangoldt hmul y) X eta (gsA9HighGeneralizedMangoldt_mul_high hmul y)
  change gsA10FullIntegratedPrefix (mrTypicalCofactorLowArithmetic A J B f y)
      (gsA9HighArithmetic f y) (gsA9HighGeneralizedMangoldt hmul y) X eta =
    positivePrefixSum
        (fun n ↦ (mrTypicalCofactorLowArithmetic A J B f y * gsA9HighArithmetic f y) n) X -
      gsA10FirstSecondaryPrefix (mrTypicalCofactorLowArithmetic A J B f y)
        (gsA9HighArithmetic f y) X eta -
      gsA10SecondSecondaryPrefix (mrTypicalCofactorLowArithmetic A J B f y)
        (gsA9HighArithmetic f y) (gsA9HighGeneralizedMangoldt hmul y) X eta at hid
  rw [mrTypicalCofactorFullIntegratedPrefix_eq_tailored A J B hmul hy eta,
    mrTypicalCofactorLowArithmetic_mul_high A hA J B hB hmul y hAy hBy,
    mrPositivePrefixSum_toArithmeticFunction] at hid
  rw [hid]
  ring

/-- The actual averaged Perron transform, with arbitrary vertical height. -/
def mrTypicalCofactorIntegratedPerron {ι : Type*}
    (A : Finset ℕ) (J : Finset ι) (B : ι → Finset ℕ)
    (f : ℕ → ℂ) (hmul : IsMultiplicativeOnPositiveNat f)
    (y X : ℕ) (eta T : ℝ) : ℂ :=
  2 * ∫ alpha : ℝ in 0..eta, ∫ beta : ℝ in 0..eta,
    mrTypicalCofactorMovingPerronIntegral A J B f hmul y X alpha beta T

theorem mrNorm_positivePrefix_typicalCofactor_sub_integratedPerron_div_le
    {ι : Type*} (A : Finset ℕ) (hA : ∀ p ∈ A, p.Prime)
    (J : Finset ι) (B : ι → Finset ℕ) (hB : ∀ j ∈ J, ∀ p ∈ B j, p.Prime)
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
    (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1) {y X : ℕ} (hy : 23 ≤ y) (hX : 2 ≤ X)
    (hlogX : 1 ≤ Real.log (X : ℝ)) (hlogy : 6 ≤ Real.log (y : ℝ))
    (hAy : ∀ p ∈ A, p ≤ y) (hBy : ∀ j ∈ J, ∀ p ∈ B j, p ≤ y)
    (hprimeMass : PrimeEstimates.primeReciprocals X ≤ Real.log (X : ℝ))
    (hySize : (Real.log (X : ℝ)) ^ 4 ≤ (y : ℝ))
    {eta : ℝ} (heta : 0 ≤ eta) (hetaLog : eta ≤ (Real.log (y : ℝ))⁻¹) :
    ‖positivePrefixSum (mrIndexedTypicalCofactorCoefficient A J B f) X -
        mrTypicalCofactorIntegratedPerron A J B f hmul y X eta ((Real.log (X : ℝ)) ^ 2)‖ /
        (X : ℝ) ≤
      gsA10OrdinaryMovingProjectionAveragedBound y X eta +
        (‖gsA10FirstSecondaryPrefix (mrTypicalCofactorLowArithmetic A J B f y)
              (gsA9HighArithmetic f y) X eta‖ +
          ‖gsA10SecondSecondaryPrefix (mrTypicalCofactorLowArithmetic A J B f y)
              (gsA9HighArithmetic f y) (gsA9HighGeneralizedMangoldt hmul y) X eta‖) / (X : ℝ) := by
  let low := mrTypicalCofactorLowArithmetic A J B f y
  let high := gsA9HighArithmetic f y
  let lambda := gsA9HighGeneralizedMangoldt hmul y
  let S₁ := gsA10FirstSecondaryPrefix low high X eta
  let S₂ := gsA10SecondSecondaryPrefix low high lambda X eta
  let P := gsA10TailoredIntegratedPrefix low high lambda y X eta
  let Q := mrTypicalCofactorIntegratedPerron A J B f hmul y X eta ((Real.log (X : ℝ)) ^ 2)
  have hid : positivePrefixSum (mrIndexedTypicalCofactorCoefficient A J B f) X = P + S₁ + S₂ :=
    mrPositivePrefix_typicalCofactor_eq_tailored_add_secondaries
      A hA J B hB hmul (by omega) hAy hBy eta
  have herr : ‖P - Q‖ / (X : ℝ) ≤ gsA10OrdinaryMovingProjectionAveragedBound y X eta :=
    mrNorm_doubleIntegral_typicalCofactorTailored_sub_perron_div_le
      A hA J B hB hmul hbound hy hX hlogX hlogy hAy hBy hprimeMass hySize heta hetaLog
  change ‖positivePrefixSum (mrIndexedTypicalCofactorCoefficient A J B f) X - Q‖ / (X : ℝ) ≤
    gsA10OrdinaryMovingProjectionAveragedBound y X eta + (‖S₁‖ + ‖S₂‖) / (X : ℝ)
  rw [hid, show P + S₁ + S₂ - Q = (P - Q) + (S₁ + S₂) by ring]
  have hnorm : ‖(P - Q) + (S₁ + S₂)‖ ≤ ‖P - Q‖ + (‖S₁‖ + ‖S₂‖) :=
    (norm_add_le _ _).trans (add_le_add le_rfl (norm_add_le _ _))
  calc
    _ ≤ (‖P - Q‖ + (‖S₁‖ + ‖S₂‖)) / (X : ℝ) :=
      div_le_div_of_nonneg_right hnorm (Nat.cast_nonneg X)
    _ = ‖P - Q‖ / (X : ℝ) + (‖S₁‖ + ‖S₂‖) / (X : ℝ) := add_div _ _ _
    _ ≤ _ := add_le_add herr le_rfl

end

end Erdos67b
