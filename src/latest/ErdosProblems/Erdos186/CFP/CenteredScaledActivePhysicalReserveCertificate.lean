/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.CFP.CenteredScaledPhysicalReserveCertificate

/-!
# Source-scaled certificates in an active bounding presentation

The canonical fixed-rank bounding GAP may have padded width-one coordinates.
After projecting to its active coordinates, the bounding presentation is
nondegenerate.  This module states the physical-reserve sink for an arbitrary
proper nondegenerate bounding presentation.  Its Corollary 2.17 minimum-width
hypothesis is discharged from the scalar source scale, rather than exposed as
a hypothesis about the displayed box.
-/

namespace Erdos186.CFP

open scoped BigOperators

noncomputable section

namespace Preprocessing

/-- A positive dilation of a nondegenerate coordinate presentation has
centered coordinate-box minimum width at least `2 * k + 1`. -/
theorem two_mul_add_one_le_centeredCoordinateAxisBox_minWidth
    {d : ℕ} (hd : 0 < d) (P : GAP 1 d) (hP : P.Nondegenerate)
    (k : ℕ) :
    2 * k + 1 ≤ (centeredCoordinateAxisBox P k).minWidth := by
  rw [AxisBox.minWidth, dif_pos hd]
  apply Finset.le_inf'
  intro i _hi
  change 2 * k + 1 ≤ (2 * k) * (P.widths i - 1) + 1
  have hi := hP i
  have hone : 1 ≤ P.widths i - 1 := by omega
  simpa only [Nat.mul_one] using
    Nat.add_le_add_right (Nat.mul_le_mul_left (2 * k) hone) 1

end Preprocessing

namespace RandomPartition

/-- Uniform source-scaled certificate constants for a proper nondegenerate
bounding presentation.  This is the active-coordinate version of
`exists_centeredScaledPhysicalReserveCertificateConstants`.

The fixed common-box width threshold is absorbed by `sourceScale`; no
minimum-width premise on the raw canonical box remains. -/
theorem exists_centeredScaledActivePhysicalReserveCertificateConstants
    (d : ℕ) (hd : 0 < d) (cNum cDen : ℕ)
    (hcNum : 0 < cNum) (hc : cNum ≤ cDen) :
    ∃ corConstant corWidth denseConstant denseEll denseWidth : ℕ,
      0 < corConstant ∧ 0 < denseConstant ∧
      ∀ {W B : Finset ℤ}
        (P : BoundingBox.BoundingGAP W d)
        (hPproper : P.progression.Proper)
        (hPnondegenerate : P.progression.Nondegenerate)
        (hBW : B ⊆ W) (hzeroW : 0 ∈ W) (hzeroB : 0 ∈ B),
        ∀ {q sourceScale s D block : ℕ}
          (selected completed : Fin (q + 1) → Finset ℤ),
          denseEll ≤ q + 1 →
          max corWidth denseWidth ≤ sourceScale →
          denseConstant ≤ q + 1 →
          0 < sourceScale → 0 < block → d ≤ D →
          (∀ i, selected i ⊆ completed i) →
          (∀ i, (completed i).card ≤ sourceScale) →
          (∀ i, completed i ⊆ B) →
          (∀ i, cNum *
              (Preprocessing.centeredCoordinateAxisBox
                P.progression sourceScale).volume ≤
            cDen * (Greedy.subsetSums (selected i)).card) →
          (∀ i, generatedSublattice
              ((completed i).image
                (Preprocessing.centeredIdentification
                  P hPproper hzeroW)) =
            Stability.generatedSubgroup
              (Preprocessing.centeredIdentification
                P hPproper hzeroW) B) →
          (Set.univ : Set (Fin (q + 1))).PairwiseDisjoint
            (fun i ↦ Stability.integerPoints (completed i)) →
          (∑ i, (Stability.integerPoints (completed i)).card) ≤ s →
          s ≤ 2 * block * (q + 1) * sourceScale →
          sourceScale * ((q + 1) / denseConstant) ≤ s →
          (P.progression.dilate
            (((q + 1) / denseConstant) * corConstant *
              (2 * sourceScale))).Proper →
          Nonempty (PreprocessedReserveCertificate B s D 0 1
            (4 * denseConstant * block)) := by
  obtain ⟨corConstant, corWidth, denseConstant, denseEll, denseWidth,
      hcorConstant, hdenseConstant, hcommon⟩ :=
    exists_commonBasis_denseBoxConstants d hd cNum cDen hcNum hc
  refine ⟨corConstant, corWidth, denseConstant, denseEll, denseWidth,
    hcorConstant, hdenseConstant, ?_⟩
  intro W B P hPproper hPnondegenerate hBW hzeroW hzeroB q sourceScale s D
    block selected completed hell hwidthScale hCell hsourceScale hblock hdD hselected
    hcompletedCard hcompletedSubset hphysicalDensity hgenerated hdisjoint
    hreserveSmall hsUpper hscaleUpper hnoCarry
  let phi := Preprocessing.centeredIdentification P hPproper hzeroW
  let coordinateReserve : Fin (q + 1) → Finset (LatticePoint d) := fun i ↦
    (completed i).image phi
  let family : Fin (q + 1) → Finset (LatticePoint d) := fun i ↦
    GAP.subsetSums (coordinateReserve i)
  let reserve : Fin (q + 1) → Finset (LatticePoint 1) := fun i ↦
    Stability.integerPoints (completed i)
  let Q := Preprocessing.centeredCoordinateAxisBox P.progression sourceScale
  let scale := (q + 1) / denseConstant
  have hinputSubset : ∀ i, family i ⊆ Q.carrier := by
    intro i
    have hsub :=
      Preprocessing.centeredCoordinateSubsetSums_subset_centeredCoordinateAxisBox
        ((hcompletedSubset i).trans hBW) (hcompletedCard i)
        P hPproper hzeroW
    simpa only [family, coordinateReserve, Q, phi] using hsub
  have hinputDensity : ∀ i, cNum * Q.volume ≤ cDen * (family i).card := by
    intro i
    have hcard :=
      Preprocessing.card_integerSubsetSums_le_centeredCoordinateSubsetSums
        ((hselected i).trans ((hcompletedSubset i).trans hBW))
        P hPproper hzeroW
    have hmono : GAP.subsetSums
        ((selected i).image phi) ⊆ family i := by
      apply subsetSums_mono
      simpa only [coordinateReserve] using Finset.image_mono phi (hselected i)
    calc
      cNum * Q.volume ≤ cDen * (Greedy.subsetSums (selected i)).card :=
        hphysicalDensity i
      _ ≤ cDen * (GAP.subsetSums ((selected i).image phi)).card :=
        Nat.mul_le_mul_left _ hcard
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
  have hQlower : 2 * sourceScale + 1 ≤ Q.minWidth := by
    exact Preprocessing.two_mul_add_one_le_centeredCoordinateAxisBox_minWidth
      hd P.progression hPnondegenerate sourceScale
  have hwidthCommon : max corWidth denseWidth ≤ Q.minWidth := by
    exact hwidthScale.trans (Nat.le_add_left sourceScale sourceScale |>.trans
      (show sourceScale + sourceScale ≤ 2 * sourceScale + 1 by omega) |>.trans
      hQlower)
  have hQtwo : 2 ≤ Q.minWidth := by
    exact (show 2 ≤ 2 * sourceScale + 1 by omega).trans hQlower
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
      ((hcompletedSubset i).trans hBW) P hPproper hzeroW
    simpa only [family, coordinateReserve, reserve, phi] using hmap
  have hcoreLattice : ∀ z ∈ B,
      phi z ∈ generatedSublattice (family 0) := by
    intro z hz
    dsimp only [family, coordinateReserve]
    rw [generatedSublattice_subsetSums, hgenerated 0]
    exact Stability.image_mem_generatedSubgroup hz
  have hscaleLower :
      1 * s ≤ (4 * denseConstant * block) * (sourceScale * scale) := by
    have hs : s ≤
        (4 * denseConstant * (block * sourceScale)) *
          ((q + 1) / denseConstant) := by
      apply le_four_mul_mul_div hdenseConstant hCell
      calc
        s ≤ 2 * block * (q + 1) * sourceScale := hsUpper
        _ = 2 * (q + 1) * (block * sourceScale) := by ring
    simpa only [one_mul, scale] using (show
      s ≤ (4 * denseConstant * block) *
          (sourceScale * ((q + 1) / denseConstant)) by
        calc
          s ≤ (4 * denseConstant * (block * sourceScale)) *
              ((q + 1) / denseConstant) := hs
          _ = (4 * denseConstant * block) *
              (sourceScale * ((q + 1) / denseConstant)) := by ring)
  apply preprocessedReserveCertificate_of_scaled_corollary217Certificate
    family 0 reserve hfamilyGenerated P hPproper hzeroW hsourceScale cert hd
      hQtwo hcovered hfamilyMap hinj (Finset.Subset.rfl) (by simp) hdisjoint
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
  Erdos186.CFP.RandomPartition.exists_centeredScaledActivePhysicalReserveCertificateConstants
