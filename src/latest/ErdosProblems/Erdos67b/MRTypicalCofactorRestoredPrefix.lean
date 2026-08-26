import ErdosProblems.Erdos67b.MRCofactorRestoredEnvelope
import ErdosProblems.Erdos67b.MRCofactorContourTransfer
import ErdosProblems.Erdos67b.MRCofactorContourScalar

/-!
# Original-coefficient cofactor prefix and its uniform scalar contour

Only the low/high envelope pays for fixed small-prime restoration. The
generic ordinary projection and secondary estimates apply to the original
coefficient directly, with no additional Euler-product factor.
-/

open scoped BigOperators
open Complex Set MeasureTheory

namespace Erdos67b

open MRHalaszBands MRHalaszEuler

noncomputable section

theorem mrExists_norm_typicalCofactorIntegratedPerron_div_le_restoredEnvelope_of_localDistance :
    ∃ C : ℝ, ∃ Y : ℕ, 1 ≤ C ∧
      ∀ (A : Finset ℕ) (_hA : ∀ p ∈ A, p.Prime)
        (J : Finset ℕ) (B : ℕ → Finset ℕ) {N X y : ℕ}
        (_hN : 0 < N) (_hY : Y ≤ y) (_hX : 2 ≤ X) (_hy : 23 ≤ y) (_hyX : y ≤ X)
        (_hJ : ∀ j ∈ J, 1 ≤ j) (_hB : ∀ j ∈ J, B j ⊆ primesUpTo X)
        (_hdisj : Set.PairwiseDisjoint (↑J : Set ℕ) B)
        (_hsmall : ∀ j ∈ J, ∀ p ∈ B j, Real.log (p : ℝ) ≤ Real.log (X : ℝ) / 16)
        (_hmass : ∀ j ∈ J, 2 * Real.log (j : ℝ) ≤ ∑ p ∈ B j, 1 / (p : ℝ))
        (_hAy : ∀ p ∈ A, p ≤ y) (_hBy : ∀ j ∈ J, ∀ p ∈ B j, p ≤ y)
        (_hlarge : ∀ j ∈ J, ∀ p ∈ B j, 23 ≤ p)
        {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
        (_hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
        {eta T : ℝ} (K : ℕ) (_hlogy : 6 ≤ Real.log (y : ℝ))
        (_heta0 : 0 ≤ eta) (_heta : eta ≤ (Real.log (y : ℝ))⁻¹)
        (_hT : 0 ≤ T)
        (_hdistance : ∀ t : ℝ, |t| ≤ T → (N : ℝ) ≤ pretentiousDistSq f (archimedeanTwist t) X)
        (_hTX : T ≤ X) (_hTK : T ≤ (((2 : ℕ) ^ K : ℕ) : ℝ)),
        ‖mrTypicalCofactorIntegratedPerron A J B f hmul y X eta T‖ / (X : ℝ) ≤
          mrWeightedCofactorContourBudget C (mrCofactorRestoredEnvelope N X) y X K eta T := by
  obtain ⟨C, Y, hC, hpoint⟩ := mrExists_norm_typicalCofactorPerron_le_of_lowHigh
  refine ⟨C, Y, hC, ?_⟩
  intro A hA J B N X y hN hY hX hy hyX hJ hB hdisj hsmall hmass hAy hBy hlarge
    f hmul hbound eta T K hlogy heta0 heta hT hdistance hTX hTK
  have hM := mrCofactorRestoredEnvelope_nonneg N X
  apply mrNorm_typicalCofactorIntegratedPerron_div_le_of_pointBudget
    A J B hmul hbound hX hy hyX hC hM hlogy heta0 heta hT
  intro alpha ha beta hb
  apply hpoint A J B hmul hbound hY hX K hlogy
    (ha.2.trans heta) hb.1 (hb.2.trans heta) hT hTK hM
  intro t ht
  rw [LSeries_gsA9HighArithmetic]
  exact mrNorm_sourceRestoredTypicalCofactorLow_mul_high_le_envelope_of_distance A hA J B hN
    (by omega) hy hJ hB hdisj hsmall hmass hAy hBy hlarge hmul hbound
    hlogy ha.1 (ha.2.trans heta) hb.1 (hb.2.trans heta) (hdistance t ht)

theorem mrExists_norm_typicalCofactorIntegratedPerron_div_le_restoredEnvelope :
    ∃ C : ℝ, ∃ Y : ℕ, 1 ≤ C ∧
      ∀ (A : Finset ℕ) (_hA : ∀ p ∈ A, p.Prime)
        (J : Finset ℕ) (B : ℕ → Finset ℕ) {N X y : ℕ}
        (_hN : 0 < N) (_hY : Y ≤ y) (_hX : 2 ≤ X) (_hy : 23 ≤ y) (_hyX : y ≤ X)
        (_hJ : ∀ j ∈ J, 1 ≤ j) (_hB : ∀ j ∈ J, B j ⊆ primesUpTo X)
        (_hdisj : Set.PairwiseDisjoint (↑J : Set ℕ) B)
        (_hsmall : ∀ j ∈ J, ∀ p ∈ B j, Real.log (p : ℝ) ≤ Real.log (X : ℝ) / 16)
        (_hmass : ∀ j ∈ J, 2 * Real.log (j : ℝ) ≤ ∑ p ∈ B j, 1 / (p : ℝ))
        (_hAy : ∀ p ∈ A, p ≤ y) (_hBy : ∀ j ∈ J, ∀ p ∈ B j, p ≤ y)
        (_hlarge : ∀ j ∈ J, ∀ p ∈ B j, 23 ≤ p)
        {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
        (_hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1) (_hnonpret : MRArchimedeanNonpretentious f N X)
        {eta T : ℝ} (K : ℕ) (_hlogy : 6 ≤ Real.log (y : ℝ))
        (_heta0 : 0 ≤ eta) (_heta : eta ≤ (Real.log (y : ℝ))⁻¹)
        (_hT : 0 ≤ T) (_hTX : T ≤ X) (_hTK : T ≤ (((2 : ℕ) ^ K : ℕ) : ℝ)),
        ‖mrTypicalCofactorIntegratedPerron A J B f hmul y X eta T‖ / (X : ℝ) ≤
          mrWeightedCofactorContourBudget C (mrCofactorRestoredEnvelope N X) y X K eta T := by
  obtain ⟨C, Y, hC, hlocal⟩ :=
    mrExists_norm_typicalCofactorIntegratedPerron_div_le_restoredEnvelope_of_localDistance
  refine ⟨C, Y, hC, ?_⟩
  intro A hA J B N X y hN hY hX hy hyX hJ hB hdisj hsmall hmass hAy hBy hlarge
    f hmul hbound hnonpret eta T K hlogy heta0 heta hT hTX hTK
  exact hlocal A hA J B hN hY hX hy hyX hJ hB hdisj hsmall hmass hAy hBy hlarge
    hmul hbound K hlogy heta0 heta hT (fun t ht ↦ hnonpret t (ht.trans hTX)) hTX hTK

theorem mrExists_norm_positivePrefix_typicalCofactor_div_le_restoredBudgets_of_localDistance :
    ∃ C : ℝ, ∃ Y : ℕ, 1 ≤ C ∧
      ∀ (A : Finset ℕ) (_hA : ∀ p ∈ A, p.Prime)
        (J : Finset ℕ) (B : ℕ → Finset ℕ) {N X y : ℕ}
        (_hN : 0 < N) (_hY : Y ≤ y) (_hy : 23 ≤ y) (_hyX : y ≤ X)
        (_hJ : ∀ j ∈ J, 1 ≤ j) (_hB : ∀ j ∈ J, B j ⊆ primesUpTo X)
        (_hdisj : Set.PairwiseDisjoint (↑J : Set ℕ) B)
        (_hsmall : ∀ j ∈ J, ∀ p ∈ B j, Real.log (p : ℝ) ≤ Real.log (X : ℝ) / 16)
        (_hmass : ∀ j ∈ J, 2 * Real.log (j : ℝ) ≤ ∑ p ∈ B j, 1 / (p : ℝ))
        (_hAy : ∀ p ∈ A, p ≤ y) (_hBy : ∀ j ∈ J, ∀ p ∈ B j, p ≤ y)
        (_hlarge : ∀ j ∈ J, ∀ p ∈ B j, 23 ≤ p)
        {f : ℕ → ℂ} (_hmul : IsMultiplicativeOnPositiveNat f)
        (_hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1) (_hdistance : ∀ t : ℝ, |t| ≤ Real.log (X : ℝ) ^ 2 →
          (N : ℝ) ≤ pretentiousDistSq f (archimedeanTwist t) X)
        (K : ℕ) (_hlogX : 1 ≤ Real.log (X : ℝ)) (_hlogy : 6 ≤ Real.log (y : ℝ))
        (_hTX : Real.log (X : ℝ) ^ 2 ≤ X)
        (_hTK : Real.log (X : ℝ) ^ 2 ≤ (((2 : ℕ) ^ K : ℕ) : ℝ))
        (_hprimeMass : PrimeEstimates.primeReciprocals X ≤ Real.log (X : ℝ))
        (_hySize : Real.log (X : ℝ) ^ 4 ≤ (y : ℝ)),
        ‖positivePrefixSum (mrIndexedTypicalCofactorCoefficient A J B f) X‖ / (X : ℝ) ≤
          mrWeightedCofactorContourBudget C (mrCofactorRestoredEnvelope N X)
              y X K (Real.log (y : ℝ))⁻¹ (Real.log (X : ℝ) ^ 2) +
            gsA10OrdinaryMovingProjectionAveragedBound y X (Real.log (y : ℝ))⁻¹ +
            mrTypicalCofactorSecondaryBound y X := by
  obtain ⟨C, Y, hC, hcontour⟩ :=
    mrExists_norm_typicalCofactorIntegratedPerron_div_le_restoredEnvelope_of_localDistance
  refine ⟨C, Y, hC, ?_⟩
  intro A hA J B N X y hN hY hy hyX hJ hB hdisj hsmall hmass hAy hBy hlarge
    f hmul hbound hdistance K hlogX hlogy hTX hTK hprimeMass hySize
  let eta := (Real.log (y : ℝ))⁻¹
  let T := Real.log (X : ℝ) ^ 2
  let P := positivePrefixSum (mrIndexedTypicalCofactorCoefficient A J B f) X
  let Q := mrTypicalCofactorIntegratedPerron A J B f hmul y X eta T
  have hBprime : ∀ j ∈ J, ∀ p ∈ B j, p.Prime :=
    fun j hj p hp ↦ (mem_primesUpTo.mp (hB j hj hp)).1
  have heta : 0 ≤ eta := inv_nonneg.mpr (by linarith)
  have hQ := hcontour A hA J B hN hY (show 2 ≤ X by omega) hy hyX hJ hB hdisj hsmall hmass
    hAy hBy hlarge hmul hbound K hlogy heta le_rfl (sq_nonneg (Real.log (X : ℝ))) hdistance hTX hTK
  have hdiff := mrNorm_positivePrefix_typicalCofactor_sub_integratedPerron_div_le_source
    A hA J B hBprime hmul hbound hy hyX hlogX hlogy hAy hBy hprimeMass hySize
  have hnorm : ‖P‖ ≤ ‖Q‖ + ‖P - Q‖ := by
    calc
      _ = ‖Q + (P - Q)‖ := by congr 1; ring
      _ ≤ _ := norm_add_le _ _
  have hdiv := div_le_div_of_nonneg_right hnorm (Nat.cast_nonneg X)
  change ‖P‖ / (X : ℝ) ≤ _
  calc
    _ ≤ ‖Q‖ / (X : ℝ) + ‖P - Q‖ / (X : ℝ) := by simpa only [add_div] using hdiv
    _ ≤ mrWeightedCofactorContourBudget C (mrCofactorRestoredEnvelope N X) y X K eta T +
        (gsA10OrdinaryMovingProjectionAveragedBound y X eta + mrTypicalCofactorSecondaryBound y X) :=
      add_le_add hQ hdiff
    _ = _ := by ring

theorem mrExists_norm_positivePrefix_typicalCofactor_div_le_restoredBudgets :
    ∃ C : ℝ, ∃ Y : ℕ, 1 ≤ C ∧
      ∀ (A : Finset ℕ) (_hA : ∀ p ∈ A, p.Prime)
        (J : Finset ℕ) (B : ℕ → Finset ℕ) {N X y : ℕ}
        (_hN : 0 < N) (_hY : Y ≤ y) (_hy : 23 ≤ y) (_hyX : y ≤ X)
        (_hJ : ∀ j ∈ J, 1 ≤ j) (_hB : ∀ j ∈ J, B j ⊆ primesUpTo X)
        (_hdisj : Set.PairwiseDisjoint (↑J : Set ℕ) B)
        (_hsmall : ∀ j ∈ J, ∀ p ∈ B j, Real.log (p : ℝ) ≤ Real.log (X : ℝ) / 16)
        (_hmass : ∀ j ∈ J, 2 * Real.log (j : ℝ) ≤ ∑ p ∈ B j, 1 / (p : ℝ))
        (_hAy : ∀ p ∈ A, p ≤ y) (_hBy : ∀ j ∈ J, ∀ p ∈ B j, p ≤ y)
        (_hlarge : ∀ j ∈ J, ∀ p ∈ B j, 23 ≤ p)
        {f : ℕ → ℂ} (_hmul : IsMultiplicativeOnPositiveNat f)
        (_hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1) (_hnonpret : MRArchimedeanNonpretentious f N X)
        (K : ℕ) (_hlogX : 1 ≤ Real.log (X : ℝ)) (_hlogy : 6 ≤ Real.log (y : ℝ))
        (_hTX : Real.log (X : ℝ) ^ 2 ≤ X)
        (_hTK : Real.log (X : ℝ) ^ 2 ≤ (((2 : ℕ) ^ K : ℕ) : ℝ))
        (_hprimeMass : PrimeEstimates.primeReciprocals X ≤ Real.log (X : ℝ))
        (_hySize : Real.log (X : ℝ) ^ 4 ≤ (y : ℝ)),
        ‖positivePrefixSum (mrIndexedTypicalCofactorCoefficient A J B f) X‖ / (X : ℝ) ≤
          mrWeightedCofactorContourBudget C (mrCofactorRestoredEnvelope N X)
              y X K (Real.log (y : ℝ))⁻¹ (Real.log (X : ℝ) ^ 2) +
            gsA10OrdinaryMovingProjectionAveragedBound y X (Real.log (y : ℝ))⁻¹ +
            mrTypicalCofactorSecondaryBound y X := by
  obtain ⟨C, Y, hC, hlocal⟩ :=
    mrExists_norm_positivePrefix_typicalCofactor_div_le_restoredBudgets_of_localDistance
  refine ⟨C, Y, hC, ?_⟩
  intro A hA J B N X y hN hY hy hyX hJ hB hdisj hsmall hmass hAy hBy hlarge
    f hmul hbound hnonpret K hlogX hlogy hTX hTK hprimeMass hySize
  exact hlocal A hA J B hN hY hy hyX hJ hB hdisj hsmall hmass hAy hBy hlarge hmul hbound
    (fun t ht ↦ hnonpret t (ht.trans hTX)) K hlogX hlogy hTX hTK hprimeMass hySize

theorem mrWeightedCofactorContourBudget_mul_envelope (C M a : ℝ) (y X K : ℕ) (eta T : ℝ) :
    mrWeightedCofactorContourBudget C (a * M) y X K eta T =
      a * mrWeightedCofactorContourBudget C M y X K eta T := by
  unfold mrWeightedCofactorContourBudget mrWeightedCofactorContourCoefficient
  ring

def mrCofactorRestoredMeanConstant (C : ℝ) : ℝ :=
  gsA9SmallPrimeEulerBound * mrCofactorContourMeanConstant C

theorem mrCofactorRestoredMeanConstant_nonneg {C : ℝ} (hC : 1 ≤ C) :
    0 ≤ mrCofactorRestoredMeanConstant C :=
  mul_nonneg mrCofactorSmallPrimeConstant_nonneg (mrCofactorContourMeanConstant_nonneg hC)

theorem mrCofactor_restoredContourBudget_le_inverse_nonpretentious {C delta : ℝ}
    (hC : 1 ≤ C) (hdelta : 0 < delta) {N y X : ℕ}
    (hN : 0 < N) (hX : 4 ≤ X) (hy : 3 ≤ y) (hlogX : 1 ≤ Real.log (X : ℝ))
    (hprime : PrimeEstimates.primeReciprocals X ≤ Real.log (X : ℝ))
    (hlogSquare : 4 * Real.log (X : ℝ) ≤ Real.log (y : ℝ) ^ 2)
    (hlogTwelve : Real.log (X : ℝ) ^ 12 ≤ (y : ℝ))
    (hcutoff : delta * Real.log (X : ℝ) ≤ Real.log (y : ℝ)) :
    mrWeightedCofactorContourBudget C (mrCofactorRestoredEnvelope N X)
        y X (mrCofactorDyadicHeight X) (Real.log (y : ℝ))⁻¹ (Real.log (X : ℝ) ^ 2) ≤
      mrCofactorRestoredMeanConstant C / (N * delta) := by
  rw [mrCofactorRestoredEnvelope, mrWeightedCofactorContourBudget_mul_envelope]
  have hbound := mrCofactor_contourBudget_le_inverse_nonpretentious
    hC hdelta hN hX hy hlogX hprime hlogSquare hlogTwelve hcutoff
  exact (mul_le_mul_of_nonneg_left hbound mrCofactorSmallPrimeConstant_nonneg).trans_eq (by
    unfold mrCofactorRestoredMeanConstant
    ring)

end

end Erdos67b
