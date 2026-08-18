/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.CFP.Corollary217ScaledMapBack
import ErdosProblems.Erdos186.CFP.CenteredCompletedReserveCertificate

/-!
# Source-scaled completed centered reserves

This is the completed-reserve construction with the Corollary 2.17 basis
radii divided by the common source scale.  Unlike the uncontracted wrapper,
the resulting certificate has a fixed denominator independent of the block
size.
-/

namespace Erdos186.CFP

open scoped BigOperators

noncomputable section

namespace RandomPartition

/-- Uniform constants for the source-scaled completed-reserve construction. -/
theorem exists_centeredScaledCompletedReserveCertificateConstants
    (d : ℕ) (hd : 0 < d) (cNum cDen : ℕ)
    (hcNum : 0 < cNum) (hc : cNum ≤ cDen) :
    ∃ corConstant corWidth denseConstant denseEll denseWidth : ℕ,
      0 < corConstant ∧ 0 < denseConstant ∧
      ∀ {W B A : Finset ℤ} {relevant : Finset ℕ}
        (hproper : Stability.RelevantBoxesProper W relevant),
        (hdrel : d ∈ relevant) → B ⊆ W → A ⊆ B → 0 ∈ B →
        ∀ {q deletionBudget steps level sourceScale s D : ℕ}
          (c : {a // a ∈ A} → Fin (q + 1))
          (completion : Fin (q + 1) → Finset ℤ),
          denseEll ≤ q + 1 →
          max corWidth denseWidth ≤
            (Preprocessing.centeredCoordinateAxisBox
              (BoundingBox.dBoundingBox W d
                (hproper.positive hdrel)).progression
              sourceScale).minWidth →
          denseConstant ≤ q + 1 →
          0 < sourceScale → d ≤ D →
          (∀ i, steps ≤ (integerColorClass A c i).card) →
          (∀ i, Greedy.dyadicBinStart (integerColorClass A c i)
            deletionBudget steps level < steps) →
          (∀ i, (completedColorSet A c steps completion i).card ≤
            sourceScale) →
          (∀ i, completedColorSet A c steps completion i ⊆ A) →
          (∀ i, cNum *
              (Preprocessing.centeredCoordinateAxisBox
                (BoundingBox.dBoundingBox W d
                  (hproper.positive hdrel)).progression
                sourceScale).volume ≤
            cDen * Greedy.positiveDyadicThreshold
              (integerColorClass A c i) deletionBudget level) →
          (∀ i, generatedSublattice
              (coordinateCompletedColorReserve A c steps completion
                (Stability.centeredMinimalIdentificationFamily hproper d) i) =
            Stability.generatedSubgroup
              (Stability.centeredMinimalIdentificationFamily hproper d) B) →
          (Set.univ : Set (Fin (q + 1))).PairwiseDisjoint
            (completedGreedyColorReserve A c steps completion) →
          (∀ i, completedGreedyColorReserve A c steps completion i ⊆
            Stability.integerPoints B) →
          (∀ i, (completedGreedyColorReserve A c steps completion i).Nonempty) →
          (∑ i, (completedGreedyColorReserve A c steps completion i).card) ≤
            s →
          s ≤ 2 * (q + 1) * sourceScale →
          sourceScale * ((q + 1) / denseConstant) ≤ s →
          (((BoundingBox.dBoundingBox W d
              (hproper.positive hdrel)).progression).dilate
            (((q + 1) / denseConstant) * corConstant *
              (2 * sourceScale))).Proper →
          Nonempty (PreprocessedReserveCertificate B s D 0 1
            (4 * denseConstant)) := by
  obtain ⟨corConstant, corWidth, denseConstant, denseEll, denseWidth,
      hcorConstant, hdenseConstant, hcommon⟩ :=
    exists_commonBasis_denseBoxConstants d hd cNum cDen hcNum hc
  refine ⟨corConstant, max 2 corWidth, denseConstant, denseEll, denseWidth,
    hcorConstant, hdenseConstant, ?_⟩
  intro W B A relevant hproper hdrel hBW hAB hzeroB q deletionBudget steps level
    sourceScale s D c completion hell hwidth hCell hsourceScale hdD hsteps
    hcross hcompletedCard hcompletedSubset hvolume hgenerated hdisjoint
    hreserveCore hreserveNonempty hreserveSmall hsUpper hscaleUpper hnoCarry
  let P := BoundingBox.dBoundingBox W d (hproper.positive hdrel)
  let phi := Stability.centeredMinimalIdentificationFamily hproper d
  let coordinateReserve : Fin (q + 1) → Finset (LatticePoint d) :=
    coordinateCompletedColorReserve A c steps completion phi
  let family : Fin (q + 1) → Finset (LatticePoint d) := fun i ↦
    GAP.subsetSums (coordinateReserve i)
  let reserve : Fin (q + 1) → Finset (LatticePoint 1) :=
    completedGreedyColorReserve A c steps completion
  let Q := Preprocessing.centeredCoordinateAxisBox P.progression sourceScale
  let scale := (q + 1) / denseConstant
  have hphi : Preprocessing.centeredIdentification P (hproper.proper hdrel)
      (hBW hzeroB) = phi := by
    exact Preprocessing.centeredIdentification_eq_centeredMinimalIdentificationFamily
      hproper hdrel (hBW hzeroB)
  have hinputs := centeredCompletedReserves_denseBoxInputs_of_firstCrossing
    P (hproper.proper hdrel) (hBW hzeroB) (hAB.trans hBW) c completion hsteps hcross
      hcompletedCard (fun i ↦ (hcompletedSubset i).trans (hAB.trans hBW)) hvolume
  have hinputSubset : ∀ i, family i ⊆ Q.carrier := by
    intro i
    simpa only [family, coordinateReserve, Q, P, phi, hphi] using hinputs.1 i
  have hinputDensity : ∀ i, cNum * Q.volume ≤ cDen * (family i).card := by
    intro i
    simpa only [family, coordinateReserve, Q, P, phi, hphi] using hinputs.2 i
  have hfamilyZero : ∀ i, (0 : LatticePoint d) ∈ family i := by
    intro i
    exact GAP.zero_mem_subsetSums _
  have hfamilyGenerated : ∀ i,
      generatedSublattice (family i) = generatedSublattice (family 0) := by
    intro i
    dsimp only [family]
    rw [generatedSublattice_subsetSums, generatedSublattice_subsetSums,
      hgenerated i, hgenerated 0]
  have hwidthCommon : max corWidth denseWidth ≤ Q.minWidth := by
    exact (max_le_max_right denseWidth (Nat.le_max_right 2 corWidth)).trans hwidth
  have hQtwo : 2 ≤ Q.minWidth := by
    exact (Nat.le_max_left 2 corWidth).trans
      ((Nat.le_max_left (max 2 corWidth) denseWidth).trans hwidth)
  obtain ⟨cert, hcertConstant, hcovered⟩ :=
    hcommon Q family hwidthCommon hfamilyZero hinputSubset hinputDensity
      hfamilyGenerated hell
  have hinj : Set.InjOn (sourceLineEvaluation P.progression)
      (cert.progression.dilate scale).carrier := by
    apply sourceLineEvaluation_injOn
    apply cert.stepEvaluation_injOn_dilate P
    simpa only [scale, corollary217NoCarryScale, hcertConstant] using hnoCarry
  have hfamilyMap : ∀ i,
      (family i).image (sourceLineEvaluation P.progression) ⊆
        GAP.subsetSums (reserve i) := by
    intro i
    exact image_centeredMinimalCompletedSubsetSums_subset_completedReserveSubsetSums
      hproper hdrel (hBW hzeroB) c completion
        (fun i ↦ (hcompletedSubset i).trans (hAB.trans hBW)) i
  have hcoreLattice : ∀ z ∈ B,
      Preprocessing.centeredIdentification P (hproper.proper hdrel)
          (hBW hzeroB) z ∈ generatedSublattice (family 0) := by
    intro z hz
    rw [show Preprocessing.centeredIdentification P (hproper.proper hdrel)
        (hBW hzeroB) = phi from
      Preprocessing.centeredIdentification_eq_centeredMinimalIdentificationFamily
        hproper hdrel (hBW hzeroB)]
    dsimp only [family]
    rw [generatedSublattice_subsetSums, hgenerated 0]
    exact Stability.image_mem_generatedSubgroup hz
  have hscaleLower :
      1 * s ≤ (4 * denseConstant) * (sourceScale * scale) := by
    have hs := le_four_mul_mul_div hdenseConstant hCell hsUpper
    simpa only [one_mul, scale] using (show
      s ≤ (4 * denseConstant) * (sourceScale * ((q + 1) / denseConstant)) by
        calc
          s ≤ (4 * denseConstant * sourceScale) *
              ((q + 1) / denseConstant) := hs
          _ = (4 * denseConstant) *
              (sourceScale * ((q + 1) / denseConstant)) := by ring)
  apply preprocessedReserveCertificate_of_scaled_corollary217Certificate
    family 0 reserve hfamilyGenerated P (hproper.proper hdrel) (hBW hzeroB)
      hsourceScale cert hd hQtwo hcovered hfamilyMap hinj
      (Finset.Subset.rfl) (by simp) hdisjoint hreserveCore hreserveSmall hBW
      hcoreLattice hdD (Nat.div_pos hCell hdenseConstant) Nat.zero_lt_one
  · positivity
  · exact hscaleLower
  · simpa only [scale] using hscaleUpper

end RandomPartition

end

end Erdos186.CFP

#print axioms
  Erdos186.CFP.RandomPartition.exists_centeredScaledCompletedReserveCertificateConstants
