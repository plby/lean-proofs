/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.CFP.CenteredScaledActivePhysicalReserveCertificate
import ErdosProblems.Erdos186.CFP.CoordinateCorollary217ProjectedWitness

/-!
# Active physical reserves with projected properization

This is the source-correct replacement for the direct no-carry map-back.
The Corollary 2.17 witness is assembled in integral basis coordinates and
then projected to the source line by Lemma 2.27.
-/

namespace Erdos186.CFP

open scoped BigOperators

noncomputable section

namespace RandomPartition

/-- Uniform active-coordinate physical-reserve constants, with generic
projected properization replacing injectivity on a large source dilate. -/
theorem exists_centeredScaledActiveProjectedPhysicalReserveCertificateConstants
    (d : ℕ) (hd : 0 < d) (cNum cDen : ℕ)
    (hcNum : 0 < cNum) (hc : cNum ≤ cDen) :
    ∃ corWidth denseConstant denseEll denseWidth : ℕ,
      0 < denseConstant ∧
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
          ProjectedProperization.projectionFactor D ≤
            sourceScale * ((q + 1) / denseConstant) →
          ∃ k : ℕ, Nonempty (FixedScaleWitness
            (Stability.integerPoints B) s D k 0 1
            ((4 * denseConstant * block) *
              ProjectedProperization.projectionFactor D)) := by
  obtain ⟨_corConstant, corWidth, denseConstant, denseEll, denseWidth,
      _hcorConstant, hdenseConstant, hcommon⟩ :=
    exists_commonBasis_denseBoxConstants d hd cNum cDen hcNum hc
  refine ⟨corWidth, denseConstant, denseEll, denseWidth,
    hdenseConstant, ?_⟩
  intro W B P hPproper hPnondegenerate hBW hzeroW hzeroB q sourceScale s D
    block selected completed hell hwidthScale hCell hsourceScale hblock hdD hselected
    hcompletedCard hcompletedSubset hphysicalDensity hgenerated hdisjoint
    hreserveSmall hsUpper hscaleUpper hprojection
  let phi := Preprocessing.centeredIdentification P hPproper hzeroW
  let coordinateReserve : Fin (q + 1) → Finset (LatticePoint d) := fun i ↦
    (completed i).image phi
  let family : Fin (q + 1) → Finset (LatticePoint d) := fun i ↦
    GAP.subsetSums (coordinateReserve i)
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
  obtain ⟨cert, _hcertConstant, hcovered⟩ :=
    hcommon Q family hwidthCommon hfamilyZero hinputSubset hinputDensity
      hfamilyGenerated hell
  have hcoordinateGenerated : ∀ i,
      generatedSublattice (coordinateReserve i) =
        generatedSublattice (coordinateReserve 0) := by
    intro i
    exact (hgenerated i).trans (hgenerated 0).symm
  have hcoordinateSubset : ∀ i, coordinateReserve i ⊆ B.image phi := by
    intro i
    exact Finset.image_mono phi (hcompletedSubset i)
  have hcoreLattice : ∀ z ∈ B,
      phi z ∈ generatedSublattice (coordinateReserve 0) := by
    intro z hz
    rw [hgenerated 0]
    exact Stability.image_mem_generatedSubgroup hz
  have hcoordinateDisjoint :
      (Set.univ : Set (Fin (q + 1))).PairwiseDisjoint coordinateReserve := by
    intro i _hi j _hj hij
    change Disjoint ((completed i).image phi) ((completed j).image phi)
    rw [Finset.disjoint_left]
    intro x hxi hxj
    obtain ⟨a, hai, hax⟩ := Finset.mem_image.mp hxi
    obtain ⟨b, hbj, hbx⟩ := Finset.mem_image.mp hxj
    have hab : a = b :=
      (Preprocessing.centeredIdentification_injectiveOn
        P hPproper hzeroW)
        (hBW (hcompletedSubset i hai))
        (hBW (hcompletedSubset j hbj))
        (hax.trans hbx.symm)
    subst b
    have hpointI : Stability.integerPoint a ∈
        Stability.integerPoints (completed i) :=
      Stability.integerPoint_mem_integerPoints_iff.mpr hai
    have hpointJ : Stability.integerPoint a ∈
        Stability.integerPoints (completed j) :=
      Stability.integerPoint_mem_integerPoints_iff.mpr hbj
    exact Finset.disjoint_left.mp (hdisjoint trivial trivial hij) hpointI hpointJ
  have hcoordinateSmall : (∑ i, (coordinateReserve i).card) ≤ s := by
    calc
      (∑ i, (coordinateReserve i).card) =
          ∑ i, (completed i).card := by
        apply Finset.sum_congr rfl
        intro i _hi
        exact Finset.card_image_of_injOn
          ((Preprocessing.centeredIdentification_injectiveOn
            P hPproper hzeroW).mono
            ((hcompletedSubset i).trans hBW))
      _ = ∑ i, (Stability.integerPoints (completed i)).card := by
        simp only [Stability.card_integerPoints]
      _ ≤ s := hreserveSmall
  have hscaleLower :
      s ≤ (4 * denseConstant * block) * (sourceScale * scale) := by
    have hs : s ≤
        (4 * denseConstant * (block * sourceScale)) *
          ((q + 1) / denseConstant) := by
      apply le_four_mul_mul_div hdenseConstant hCell
      calc
        s ≤ 2 * block * (q + 1) * sourceScale := hsUpper
        _ = 2 * (q + 1) * (block * sourceScale) := by ring
    simpa only [scale] using (show
      s ≤ (4 * denseConstant * block) *
          (sourceScale * ((q + 1) / denseConstant)) by
        calc
          s ≤ (4 * denseConstant * (block * sourceScale)) *
              ((q + 1) / denseConstant) := hs
          _ = (4 * denseConstant * block) *
              (sourceScale * ((q + 1) / denseConstant)) := by ring)
  apply exists_projectedFixedScaleWitness_of_scaled_corollary217Certificate
    coordinateReserve 0 hcoordinateGenerated P hPproper hzeroW hsourceScale
      cert hd hQtwo
  · simpa only [family, coordinateReserve] using hcovered
  · exact hBW
  · exact hcoordinateSubset
  · simpa only [phi] using hcoreLattice
  · exact hcoordinateDisjoint
  · exact hcoordinateSmall
  · exact hdD
  · exact Nat.div_pos hCell hdenseConstant
  · positivity
  · simpa only [scale] using hscaleLower
  · simpa only [scale] using hscaleUpper
  · simpa only [scale] using hprojection

end RandomPartition

end

end Erdos186.CFP

#print axioms
  Erdos186.CFP.RandomPartition.exists_centeredScaledActiveProjectedPhysicalReserveCertificateConstants
