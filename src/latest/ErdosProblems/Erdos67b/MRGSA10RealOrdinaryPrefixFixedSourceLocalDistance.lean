import ErdosProblems.Erdos67b.MRGSA10SourceContourSmallPowerBaseIntegratedLocalHeight
import ErdosProblems.Erdos67b.MRGSA10RealOrdinaryPrefixFixedSource

/-!
# Ordinary prefixes from the local-height fixed source contour
-/

namespace Erdos67b.MRHalaszBands

noncomputable section

theorem exists_norm_positivePrefixMean_twoBlock_le_smallPower_base_sub_one_of_localDistance :
    ∃ Cbeta : ℝ, ∃ Nrow : ℕ, 1 ≤ Cbeta ∧
      ∀ {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f),
        IsCompletelyMultiplicativeOnPositive f →
        (∀ n, 0 < n → ‖f n‖ ≤ 1) →
        ∀ {I₁ I₂ : ℕ × ℕ},
        Disjoint (primesInBlock I₁) (primesInBlock I₂) →
        (∀ p ∈ gsA9SmallPrimeFinset, mrTwoBlockOutside I₁ I₂ p) →
        ∀ {X Z y : ℕ},
        Nrow ≤ y → 3 ≤ X → X ≤ Z → Z ≤ 3 * X →
        23 ≤ y → y ≤ Z → 4 ≤ Z → 2 ≤ Z / y →
        6 ≤ Real.log (y : ℝ) → 1 ≤ Real.log (Z : ℝ) →
        Real.log (Z : ℝ) ^ 2 ≤ Z →
        Erdos67b.PrimeEstimates.primeReciprocals Z ≤ Real.log (Z : ℝ) →
        Real.log (Z : ℝ) ^ 4 ≤ (y : ℝ) →
        Real.log (Z : ℝ) ^ 6 ≤ (y : ℝ) →
        1 ≤ Erdos67b.realPrefixMovingThreshold X →
        (∀ u : ℝ, |u| ≤ Real.log (Z : ℝ) ^ 2 →
          (((Erdos67b.realPrefixMovingThreshold X - 1 : ℕ) : ℝ)) ≤
            pretentiousDistSq f (archimedeanTwist u) Z) →
        (∀ p, (¬ mrTwoBlockOutside I₁ I₂ p ∧
          mrTwoBlockFirst I₁ p) → p ≤ y) →
        (∀ p, (¬ mrTwoBlockOutside I₁ I₂ p ∧
          ¬ mrTwoBlockFirst I₁ p) → p ≤ y) →
        ∀ {rho : ℝ},
        ((atypicalFactorizationSet {I₁, I₂} Z).card : ℝ) ≤ rho * Z →
        ‖positivePrefixMean f Z‖ ≤
          2 * gsA10SmallPowerSourceContourBaseSubOneConstant Cbeta *
              (Real.log (Z : ℝ)) ^ (-(1 / 1000 : ℝ)) +
            gsA10JointMovingProjectionSourceBudget y Z +
            gsA10GlobalSecondaryShiuConstant *
              Real.log (y : ℝ) / Real.log (Z : ℝ) + rho := by
  obtain ⟨Cbeta, Nrow, hCbeta, hcontour⟩ :=
    exists_norm_gsA10TwoBlockSourcePerronIntegrated_div_le_smallPower_base_sub_one_of_localDistance
  refine ⟨Cbeta, Nrow, hCbeta, ?_⟩
  intro f hmul hcomp hbound I₁ I₂ hdisj hsmall X Z y hNrowy hX hXZ
    hZX hy hyZ hZ hquot hlogy hlogZ hlogSq hprime hlogFour hlogSix
    hthreshold hdist hQ₂ hQ₃ rho hbad
  have hcont := hcontour hmul hbound
    (mrTwoBlockOutside I₁ I₂) (mrTwoBlockFirst I₁) hsmall hNrowy
      hX hXZ hZX hy hyZ hZ hquot hlogy hlogZ hlogSq hprime hlogFour
        hlogSix hthreshold hdist
  exact norm_positivePrefixMean_twoBlock_le_sourceContour_add_jointSource
    hmul hcomp hbound hdisj hy hyZ (show 2 ≤ Z by omega) hlogZ hlogy
      hprime hlogFour hQ₂ hQ₃ hcont hbad

end

end Erdos67b.MRHalaszBands

#print axioms
  Erdos67b.MRHalaszBands.exists_norm_positivePrefixMean_twoBlock_le_smallPower_base_sub_one_of_localDistance
