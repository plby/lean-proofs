import ErdosProblems.Erdos67b.MRCofactorDistanceEnvelope
import ErdosProblems.Erdos67b.MRCofactorContourTransfer

/-!
# Cofactor prefix budget independent of the selected-prime mass

The actual denominator average is inserted into the weighted contour.
The resulting explicit prefix estimate has no denominator-set or block-
count factor. Source parameter selection and small-prime restoration are
still required for the nonpretentious mean theorem.
-/

open scoped BigOperators Classical LSeries.notation
open Complex Set MeasureTheory

namespace Erdos67b

open MRHalaszBands MRHalaszEuler

noncomputable section

theorem mrExists_norm_typicalCofactorIntegratedPerron_div_le_averageEnvelope :
    ∃ C : ℝ, ∃ Y : ℕ, 1 ≤ C ∧
      ∀ (A : Finset ℕ) (_hA : ∀ p ∈ A, p.Prime)
        (J : Finset ℕ) (B : ℕ → Finset ℕ) {N X y : ℕ}
        (_hN : 0 < N) (_hY : Y ≤ y) (_hX : 2 ≤ X) (_hy : 23 ≤ y) (_hyX : y ≤ X)
        (_hJ : ∀ j ∈ J, 1 ≤ j) (_hB : ∀ j ∈ J, B j ⊆ primesUpTo X)
        (_hdisj : Set.PairwiseDisjoint (↑J : Set ℕ) B)
        (_hsmall : ∀ j ∈ J, ∀ p ∈ B j, Real.log (p : ℝ) ≤ Real.log (X : ℝ) / 16)
        (_hmass : ∀ j ∈ J, 2 * Real.log (j : ℝ) ≤ ∑ p ∈ B j, 1 / (p : ℝ))
        (_hAy : ∀ p ∈ A, p ≤ y) (_hBy : ∀ j ∈ J, ∀ p ∈ B j, p ≤ y)
        {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
        (_hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1) (_hnonpret : MRArchimedeanNonpretentious f N X)
        {eta T : ℝ} (K : ℕ) (_hlogy : 6 ≤ Real.log (y : ℝ))
        (_heta0 : 0 ≤ eta) (_heta : eta ≤ (Real.log (y : ℝ))⁻¹)
        (_hT : 0 ≤ T) (_hTX : T ≤ X) (_hTK : T ≤ (((2 : ℕ) ^ K : ℕ) : ℝ)),
        ‖mrTypicalCofactorIntegratedPerron A J B (gsDeletePrimeBand f gsA9SmallPrime)
          (gsDeletePrimeBand_isMultiplicativeOnPositiveNat hmul gsA9SmallPrime) y X eta T‖ / (X : ℝ) ≤
          mrWeightedCofactorContourBudget C (mrCofactorAverageEnvelope N X) y X K eta T := by
  obtain ⟨C, Y, hC, hpoint⟩ := mrExists_norm_typicalCofactorPerron_le_of_lowHigh
  refine ⟨C, Y, hC, ?_⟩
  intro A hA J B N X y hN hY hX hy hyX hJ hB hdisj hsmall hmass hAy hBy f hmul hbound hnonpret
    eta T K hlogy heta0 heta hT hTX hTK
  let g := gsDeletePrimeBand f gsA9SmallPrime
  let hgmul := gsDeletePrimeBand_isMultiplicativeOnPositiveNat hmul gsA9SmallPrime
  have hgbound : ∀ n, 0 < n → ‖g n‖ ≤ 1 :=
    fun n hn ↦ norm_gsDeletePrimeBand_le_one hbound gsA9SmallPrime hn
  have hM : 0 ≤ mrCofactorAverageEnvelope N X := by
    unfold mrCofactorAverageEnvelope mrCofactorEulerBase
    positivity
  apply mrNorm_typicalCofactorIntegratedPerron_div_le_of_pointBudget
    A J B hgmul hgbound hX hy hyX hC hM hlogy heta0 heta hT
  intro alpha ha beta hb
  apply hpoint A J B hgmul hgbound hY hX K hlogy
    (ha.2.trans heta) hb.1 (hb.2.trans heta) hT hTK hM
  intro t ht
  rw [LSeries_gsA9HighArithmetic, gsA9High_deleteSmallPrimes_eq f hy]
  exact mrNorm_sourceTypicalCofactorLow_mul_high_le_averageEnvelope A hA J B hN
    (by omega) hy hJ hB hdisj hsmall hmass hAy hBy hmul hbound hnonpret
    hlogy ha.1 (ha.2.trans heta) hb.1 (hb.2.trans heta) (ht.trans hTX)

theorem mrExists_norm_positivePrefix_typicalCofactor_div_le_uniformBudgets :
    ∃ C : ℝ, ∃ Y : ℕ, 1 ≤ C ∧
      ∀ (A : Finset ℕ) (_hA : ∀ p ∈ A, p.Prime)
        (J : Finset ℕ) (B : ℕ → Finset ℕ) {N X y : ℕ}
        (_hN : 0 < N) (_hY : Y ≤ y) (_hy : 23 ≤ y) (_hyX : y ≤ X)
        (_hJ : ∀ j ∈ J, 1 ≤ j) (_hB : ∀ j ∈ J, B j ⊆ primesUpTo X)
        (_hdisj : Set.PairwiseDisjoint (↑J : Set ℕ) B)
        (_hsmall : ∀ j ∈ J, ∀ p ∈ B j, Real.log (p : ℝ) ≤ Real.log (X : ℝ) / 16)
        (_hmass : ∀ j ∈ J, 2 * Real.log (j : ℝ) ≤ ∑ p ∈ B j, 1 / (p : ℝ))
        (_hAy : ∀ p ∈ A, p ≤ y) (_hBy : ∀ j ∈ J, ∀ p ∈ B j, p ≤ y)
        {f : ℕ → ℂ} (_hmul : IsMultiplicativeOnPositiveNat f)
        (_hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1) (_hnonpret : MRArchimedeanNonpretentious f N X)
        (K : ℕ) (_hlogX : 1 ≤ Real.log (X : ℝ)) (_hlogy : 6 ≤ Real.log (y : ℝ))
        (_hTX : (Real.log (X : ℝ)) ^ 2 ≤ X)
        (_hTK : (Real.log (X : ℝ)) ^ 2 ≤ (((2 : ℕ) ^ K : ℕ) : ℝ))
        (_hprimeMass : PrimeEstimates.primeReciprocals X ≤ Real.log (X : ℝ))
        (_hySize : (Real.log (X : ℝ)) ^ 4 ≤ (y : ℝ)),
        ‖positivePrefixSum (mrIndexedTypicalCofactorCoefficient A J B
            (gsDeletePrimeBand f gsA9SmallPrime)) X‖ / (X : ℝ) ≤
          mrWeightedCofactorContourBudget C (mrCofactorAverageEnvelope N X)
              y X K (Real.log (y : ℝ))⁻¹ ((Real.log (X : ℝ)) ^ 2) +
            gsA10OrdinaryMovingProjectionAveragedBound y X (Real.log (y : ℝ))⁻¹ +
            mrTypicalCofactorSecondaryBound y X := by
  obtain ⟨C, Y, hC, hcontour⟩ := mrExists_norm_typicalCofactorIntegratedPerron_div_le_averageEnvelope
  refine ⟨C, Y, hC, ?_⟩
  intro A hA J B N X y hN hY hy hyX hJ hB hdisj hsmall hmass hAy hBy f hmul hbound hnonpret
    K hlogX hlogy hTX hTK hprimeMass hySize
  let g := gsDeletePrimeBand f gsA9SmallPrime
  let hgmul := gsDeletePrimeBand_isMultiplicativeOnPositiveNat hmul gsA9SmallPrime
  let eta := (Real.log (y : ℝ))⁻¹
  let T := (Real.log (X : ℝ)) ^ 2
  let P := positivePrefixSum (mrIndexedTypicalCofactorCoefficient A J B g) X
  let Q := mrTypicalCofactorIntegratedPerron A J B g hgmul y X eta T
  have hgbound : ∀ n, 0 < n → ‖g n‖ ≤ 1 :=
    fun n hn ↦ norm_gsDeletePrimeBand_le_one hbound gsA9SmallPrime hn
  have hBprime : ∀ j ∈ J, ∀ p ∈ B j, p.Prime :=
    fun j hj p hp ↦ (mem_primesUpTo.mp (hB j hj hp)).1
  have heta : 0 ≤ eta := inv_nonneg.mpr (by linarith)
  have hQ := hcontour A hA J B hN hY (show 2 ≤ X by omega) hy hyX hJ hB hdisj hsmall hmass
    hAy hBy hmul hbound hnonpret K hlogy heta le_rfl (sq_nonneg (Real.log (X : ℝ))) hTX hTK
  have hdiff := mrNorm_positivePrefix_typicalCofactor_sub_integratedPerron_div_le_source
    A hA J B hBprime hgmul hgbound hy hyX hlogX hlogy hAy hBy hprimeMass hySize
  have hnorm : ‖P‖ ≤ ‖Q‖ + ‖P - Q‖ := by
    calc
      _ = ‖Q + (P - Q)‖ := by congr 1; ring
      _ ≤ _ := norm_add_le _ _
  have hdiv := div_le_div_of_nonneg_right hnorm (Nat.cast_nonneg X)
  change ‖P‖ / (X : ℝ) ≤ _
  calc
    _ ≤ ‖Q‖ / (X : ℝ) + ‖P - Q‖ / (X : ℝ) := by simpa only [add_div] using hdiv
    _ ≤ mrWeightedCofactorContourBudget C (mrCofactorAverageEnvelope N X) y X K eta T +
        (gsA10OrdinaryMovingProjectionAveragedBound y X eta + mrTypicalCofactorSecondaryBound y X) :=
      add_le_add hQ hdiff
    _ = _ := by ring


end

end Erdos67b
