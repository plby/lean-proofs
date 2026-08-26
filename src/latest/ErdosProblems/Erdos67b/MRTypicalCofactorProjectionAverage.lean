import ErdosProblems.Erdos67b.MRTypicalCofactorContinuity

/-!
# Averaged projection error for the actual typical cofactor

All parameter regularity is discharged on the source rectangle. The
quantitative bound is the existing ordinary averaged majorant, with no
loss depending on the denominator set or on the number of typical blocks.
-/

open scoped BigOperators Classical
open Set MeasureTheory

namespace Erdos67b

open MRHalaszBands EulerResidue BoundedGaps.Maynard

noncomputable section

theorem mrNorm_doubleIntegral_typicalCofactorTailored_sub_perron_div_le
    {ι : Type*} (A : Finset ℕ) (hA : ∀ p ∈ A, p.Prime)
    (J : Finset ι) (B : ι → Finset ℕ) (hB : ∀ j ∈ J, ∀ p ∈ B j, p.Prime)
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
    (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1) {y X : ℕ} (hy : 23 ≤ y) (hX : 2 ≤ X)
    (hlogX : 1 ≤ Real.log (X : ℝ)) (hlogy : 6 ≤ Real.log (y : ℝ))
    (hAy : ∀ p ∈ A, p ≤ y) (hBy : ∀ j ∈ J, ∀ p ∈ B j, p ≤ y)
    (hprimeMass : PrimeEstimates.primeReciprocals X ≤ Real.log (X : ℝ))
    (hySize : (Real.log (X : ℝ)) ^ 4 ≤ (y : ℝ))
    {eta : ℝ} (heta : 0 ≤ eta) (hetaLog : eta ≤ (Real.log (y : ℝ))⁻¹) :
    ‖2 * (∫ alpha : ℝ in 0..eta, ∫ beta : ℝ in 0..eta,
          positivePrefixSum
            (mrTypicalCofactorTailoredCoefficient A J B f hmul y X alpha beta) X) -
        2 * (∫ alpha : ℝ in 0..eta, ∫ beta : ℝ in 0..eta,
          mrTypicalCofactorMovingPerronIntegral A J B f hmul y X alpha beta
            ((Real.log (X : ℝ)) ^ 2))‖ / (X : ℝ) ≤
      gsA10OrdinaryMovingProjectionAveragedBound y X eta := by
  let P : ℝ → ℝ → ℂ := fun alpha beta ↦ positivePrefixSum
    (mrTypicalCofactorTailoredCoefficient A J B f hmul y X alpha beta) X
  let Q : ℝ → ℝ → ℂ := fun alpha beta ↦
    mrTypicalCofactorMovingPerronIntegral A J B f hmul y X alpha beta
      ((Real.log (X : ℝ)) ^ 2)
  let G : ℝ → ℝ → ℝ :=
    gsA10OrdinaryMovingProjectionMajorant hmul y X ((Real.log (X : ℝ)) ^ 2)
  have hP : ContinuousOn (Function.uncurry P) (Icc (0 : ℝ) eta ×ˢ Icc (0 : ℝ) eta) :=
    (mrContinuous_positivePrefix_typicalCofactorTailored A J B f hmul y X).continuousOn
  have hQ : ContinuousOn (Function.uncurry Q) (Icc (0 : ℝ) eta ×ˢ Icc (0 : ℝ) eta) := by
    apply (mrContinuousOn_typicalCofactorMovingPerron_sourceRectangle A J B hmul hbound
      (show 1 < X by omega) hlogy ((Real.log (X : ℝ)) ^ 2)).mono
    intro z hz
    exact ⟨⟨hz.1.1, hz.1.2.trans hetaLog⟩, ⟨hz.2.1, hz.2.2.trans hetaLog⟩⟩
  have hG : ContinuousOn (Function.uncurry G) (Icc (0 : ℝ) eta ×ˢ Icc (0 : ℝ) eta) :=
    (continuous_gsA10OrdinaryMovingProjectionMajorant
      hmul y (show 0 < X by omega) ((Real.log (X : ℝ)) ^ 2)).continuousOn
  have hpoint : ∀ alpha ∈ Icc (0 : ℝ) eta, ∀ beta ∈ Icc (0 : ℝ) eta,
      ‖P alpha beta - Q alpha beta‖ ≤ G alpha beta := by
    intro alpha ha beta hb
    exact mrNorm_positivePrefix_typicalCofactorTailored_sub_perron_le_ordinaryMajorant
      A hA J B hB hmul hbound hy hX hlogX hlogy hAy hBy
      ha.1 (ha.2.trans hetaLog) hb.1 (hb.2.trans hetaLog)
  have havg := norm_two_mul_doubleIntervalIntegral_sub_le_of_pointwise_continuousOn
    (P := P) (Q := Q) (G := G) heta hP hQ hG hpoint
  have hdiv := div_le_div_of_nonneg_right havg (Nat.cast_nonneg X : (0 : ℝ) ≤ X)
  change ‖2 * (∫ alpha : ℝ in 0..eta, ∫ beta : ℝ in 0..eta, P alpha beta) -
      2 * (∫ alpha : ℝ in 0..eta, ∫ beta : ℝ in 0..eta, Q alpha beta)‖ / (X : ℝ) ≤ _
  calc
    _ ≤ 2 * (∫ alpha : ℝ in 0..eta, ∫ beta : ℝ in 0..eta, G alpha beta) / (X : ℝ) := hdiv
    _ = gsA10OrdinaryMovingProjectionRectangleMajorant hmul y X
        ((Real.log (X : ℝ)) ^ 2) eta := rfl
    _ ≤ _ := gsA10OrdinaryMovingProjectionRectangleMajorant_le
      hmul hbound hy hX hlogX hprimeMass hySize heta

end

end Erdos67b
