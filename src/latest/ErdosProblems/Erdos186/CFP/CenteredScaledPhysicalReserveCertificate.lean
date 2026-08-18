/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.CFP.CenteredScaledCompletedReserveCertificate

/-!
# Source-scaled certificate from physical reserve density

This is the source-facing boundary after the per-color greedy arguments.
Those arguments may use different ranks, levels, and run lengths.  Only their
physical subset-sum cardinal lower bounds enter here.  Every reserve is then
transported through one global centered coordinate map and one common box.
-/

namespace Erdos186.CFP

open scoped BigOperators

noncomputable section

namespace RandomPartition

/-- Uniform source-scaled certificate constants from arbitrary physical
selected and generator-completed reserve families. -/
theorem exists_centeredScaledPhysicalReserveCertificateConstants
    (d : ℕ) (hd : 0 < d) (cNum cDen : ℕ)
    (hcNum : 0 < cNum) (hc : cNum ≤ cDen) :
    ∃ corConstant corWidth denseConstant denseEll denseWidth : ℕ,
      0 < corConstant ∧ 0 < denseConstant ∧
      ∀ {W B : Finset ℤ} {relevant : Finset ℕ}
        (hproper : Stability.RelevantBoxesProper W relevant),
        (hdrel : d ∈ relevant) → B ⊆ W → 0 ∈ B →
        ∀ {q sourceScale s D : ℕ}
          (selected completed : Fin (q + 1) → Finset ℤ),
          denseEll ≤ q + 1 →
          max corWidth denseWidth ≤
            (Preprocessing.centeredCoordinateAxisBox
              (BoundingBox.dBoundingBox W d
                (hproper.positive hdrel)).progression
              sourceScale).minWidth →
          denseConstant ≤ q + 1 →
          0 < sourceScale → d ≤ D →
          (∀ i, selected i ⊆ completed i) →
          (∀ i, (completed i).card ≤ sourceScale) →
          (∀ i, completed i ⊆ B) →
          (∀ i, cNum *
              (Preprocessing.centeredCoordinateAxisBox
                (BoundingBox.dBoundingBox W d
                  (hproper.positive hdrel)).progression
                sourceScale).volume ≤
            cDen * (Greedy.subsetSums (selected i)).card) →
          (∀ i, generatedSublattice
              ((completed i).image
                (Stability.centeredMinimalIdentificationFamily hproper d)) =
            Stability.generatedSubgroup
              (Stability.centeredMinimalIdentificationFamily hproper d) B) →
          (Set.univ : Set (Fin (q + 1))).PairwiseDisjoint
            (fun i ↦ Stability.integerPoints (completed i)) →
          (∑ i, (Stability.integerPoints (completed i)).card) ≤ s →
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
  intro W B relevant hproper hdrel hBW hzeroB q sourceScale s D
    selected completed hell hwidth hCell hsourceScale hdD hselected
    hcompletedCard hcompletedSubset hphysicalDensity hgenerated hdisjoint
    hreserveSmall hsUpper hscaleUpper hnoCarry
  let P := BoundingBox.dBoundingBox W d (hproper.positive hdrel)
  let phi := Stability.centeredMinimalIdentificationFamily hproper d
  let coordinateReserve : Fin (q + 1) → Finset (LatticePoint d) := fun i ↦
    (completed i).image phi
  let family : Fin (q + 1) → Finset (LatticePoint d) := fun i ↦
    GAP.subsetSums (coordinateReserve i)
  let reserve : Fin (q + 1) → Finset (LatticePoint 1) := fun i ↦
    Stability.integerPoints (completed i)
  let Q := Preprocessing.centeredCoordinateAxisBox P.progression sourceScale
  let scale := (q + 1) / denseConstant
  have hphi : Preprocessing.centeredIdentification P (hproper.proper hdrel)
      (hBW hzeroB) = phi :=
    Preprocessing.centeredIdentification_eq_centeredMinimalIdentificationFamily
      hproper hdrel (hBW hzeroB)
  have hinputSubset : ∀ i, family i ⊆ Q.carrier := by
    intro i
    have hsub :=
      Preprocessing.centeredCoordinateSubsetSums_subset_centeredCoordinateAxisBox
        ((hcompletedSubset i).trans hBW) (hcompletedCard i)
        P (hproper.proper hdrel) (hBW hzeroB)
    simpa only [family, coordinateReserve, Q, phi, hphi] using hsub
  have hinputDensity : ∀ i, cNum * Q.volume ≤ cDen * (family i).card := by
    intro i
    have hcard :=
      Preprocessing.card_integerSubsetSums_le_centeredCoordinateSubsetSums
        ((hselected i).trans ((hcompletedSubset i).trans hBW))
        P (hproper.proper hdrel) (hBW hzeroB)
    have hmono : GAP.subsetSums
        ((selected i).image
          (Preprocessing.centeredIdentification P (hproper.proper hdrel)
            (hBW hzeroB))) ⊆ family i := by
      apply subsetSums_mono
      simpa only [coordinateReserve, phi, hphi] using
        Finset.image_mono
          (Preprocessing.centeredIdentification P (hproper.proper hdrel)
            (hBW hzeroB)) (hselected i)
    calc
      cNum * Q.volume ≤ cDen * (Greedy.subsetSums (selected i)).card :=
        hphysicalDensity i
      _ ≤ cDen * (GAP.subsetSums
          ((selected i).image
            (Preprocessing.centeredIdentification P (hproper.proper hdrel)
              (hBW hzeroB)))).card := Nat.mul_le_mul_left _ hcard
      _ ≤ cDen * (family i).card :=
        Nat.mul_le_mul_left _ (Finset.card_le_card hmono)
  have hfamilyZero : ∀ i, (0 : LatticePoint d) ∈ family i := fun i ↦
    GAP.zero_mem_subsetSums _
  have hfamilyGenerated : ∀ i,
      generatedSublattice (family i) = generatedSublattice (family 0) := by
    intro i
    dsimp only [family, coordinateReserve]
    rw [generatedSublattice_subsetSums, generatedSublattice_subsetSums,
      hgenerated i, hgenerated 0]
  have hwidthCommon : max corWidth denseWidth ≤ Q.minWidth :=
    (max_le_max_right denseWidth (Nat.le_max_right 2 corWidth)).trans hwidth
  have hQtwo : 2 ≤ Q.minWidth :=
    (Nat.le_max_left 2 corWidth).trans
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
    have hmap := image_centeredCoordinateSubsetSums_subset_sourceSubsetSums
      ((hcompletedSubset i).trans hBW) P (hproper.proper hdrel) (hBW hzeroB)
    rw [hphi] at hmap
    simpa only [family, coordinateReserve, reserve, phi] using hmap
  have hcoreLattice : ∀ z ∈ B,
      Preprocessing.centeredIdentification P (hproper.proper hdrel)
          (hBW hzeroB) z ∈ generatedSublattice (family 0) := by
    intro z hz
    rw [hphi]
    dsimp only [family, coordinateReserve]
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
      (Finset.Subset.rfl) (by simp) hdisjoint
      (fun i ↦ Stability.integerPoints_mono (hcompletedSubset i))
      hreserveSmall hBW hcoreLattice hdD
      (Nat.div_pos hCell hdenseConstant) Nat.zero_lt_one
  · positivity
  · exact hscaleLower
  · simpa only [scale] using hscaleUpper

end RandomPartition

end

end Erdos186.CFP

#print axioms
  Erdos186.CFP.RandomPartition.exists_centeredScaledPhysicalReserveCertificateConstants
