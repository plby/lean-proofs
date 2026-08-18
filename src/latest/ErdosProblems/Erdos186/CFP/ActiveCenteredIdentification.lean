/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.CFP.RandomGreedyCorollary217Density
import ErdosProblems.Erdos186.CFP.HDimension
import ErdosProblems.Erdos186.CFP.CenteredPhysicalIndex

/-!
# Centered coordinates after deleting inactive GAP directions

A proper canonical bounding GAP can have displayed width-one directions.
They carry no coordinate information and prevent the full-rank box lemmas
from applying.  This file deletes exactly those directions.  The resulting
bounding presentation has the same carrier, is proper and nondegenerate,
and its centered identification is the coordinate projection of the
original centered identification.  Consequently every common-span equality
proved by the sharp colouring descends to the active coordinates.
-/

namespace Erdos186.CFP

noncomputable section

namespace BoundingBox.BoundingGAP

/-- The bounding presentation obtained by deleting all displayed width-one
directions. -/
def activeDimensions {A : Finset ℤ} {d : ℕ} (P : BoundingGAP A d) :
    BoundingGAP A P.progression.activeRank where
  progression := P.progression.activeDimensions
  bounds := by
    intro z
    rw [GAP.carrier_activeDimensions]
    exact P.bounds z

@[simp]
theorem activeDimensions_progression {A : Finset ℤ} {d : ℕ}
    (P : BoundingGAP A d) :
    P.activeDimensions.progression = P.progression.activeDimensions := rfl

theorem activeDimensions_proper {A : Finset ℤ} {d : ℕ}
    (P : BoundingGAP A d) (hproper : P.progression.Proper) :
    P.activeDimensions.progression.Proper :=
  P.progression.activeDimensions_proper hproper

theorem activeDimensions_nondegenerate {A : Finset ℤ} {d : ℕ}
    (P : BoundingGAP A d) :
    P.activeDimensions.progression.Nondegenerate :=
  P.progression.activeDimensions_nondegenerate

/-- A proper bounding presentation of a nontrivial anchored set has a
positive number of active directions. -/
theorem activeRank_pos {A : Finset ℤ} {d : ℕ}
    (P : BoundingGAP A d) (hproper : P.progression.Proper)
    (hzero : 0 ∈ A) (hne : A ≠ {0}) :
    0 < P.progression.activeRank := by
  have hex : ∃ z ∈ A, z ≠ 0 := by
    by_contra hnot
    push_neg at hnot
    apply hne
    ext z
    constructor
    · intro hz
      simpa [hnot z hz]
    · intro hz
      have hz0 : z = 0 := by simpa using hz
      simpa [hz0] using hzero
  obtain ⟨z, hz, hz0⟩ := hex
  have hpair : ({0, z} : Finset ℤ) ⊆ A := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact hzero
    · exact hz
  have hcardA : 2 ≤ A.card := by
    have := Finset.card_le_card hpair
    simpa [hz0, Ne.symm hz0] using this
  let active := P.activeDimensions
  have himage : A.image intPoint ⊆ active.progression.carrier := by
    intro x hx
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
    exact active.bounds ⟨a, ha⟩
  have hcardImage : (A.image intPoint).card = A.card := by
    exact Finset.card_image_of_injective A intPoint_injective
  have hcardActive : 2 ≤ active.progression.carrier.card := by
    rw [← hcardImage] at hcardA
    exact hcardA.trans (Finset.card_le_card himage)
  by_contra hnot
  have hrank : P.progression.activeRank = 0 := Nat.eq_zero_of_not_pos hnot
  have hvolume : active.progression.volume = 1 := by
    rw [GAP.volume]
    apply Finset.prod_eq_one
    intro i _hi
    exact Fin.elim0 (Fin.cast hrank i)
  have hcardOne : active.progression.carrier.card = 1 := by
    rw [active.progression.card_carrier_eq_volume
      (activeDimensions_proper P hproper), hvolume]
  omega

end BoundingBox.BoundingGAP

namespace Preprocessing

/-- Projection from all displayed coordinates to the genuinely active
coordinates. -/
def activeCoordinateProjection {d : ℕ} (P : GAP 1 d) :
    LatticePoint d →+ LatticePoint P.activeRank where
  toFun x := fun j ↦ x (P.activeIndex j)
  map_zero' := rfl
  map_add' := by
    intro x y
    rfl

@[simp]
theorem activeCoordinateProjection_apply {d : ℕ} (P : GAP 1 d)
    (x : LatticePoint d) (j : Fin P.activeRank) :
    activeCoordinateProjection P x j = x (P.activeIndex j) := rfl

/-- Proper coordinate identification commutes with deletion of inactive
directions. -/
theorem activeDimensions_identificationMap {A : Finset ℤ} {d : ℕ}
    (P : BoundingBox.BoundingGAP A d) (hproper : P.progression.Proper)
    (z : {z // z ∈ A}) :
    P.activeDimensions.identificationMap
        (P.activeDimensions_proper hproper) z =
      activeCoordinateProjection P.progression
        (P.identificationMap hproper z) := by
  have hzactive : BoundingBox.intPoint z.1 ∈
      P.progression.activeDimensions.carrier := by
    rw [GAP.carrier_activeDimensions]
    exact P.bounds z
  let m := P.progression.activeDimensions.coordinateMap
    (P.progression.activeDimensions_proper hproper)
      ⟨BoundingBox.intPoint z.1, hzactive⟩
  let n := P.progression.coordinateMap hproper
    ⟨BoundingBox.intPoint z.1, P.bounds z⟩
  have hmPoint : P.progression.activeDimensions.coordPoint m =
      BoundingBox.intPoint z.1 := by
    exact P.progression.activeDimensions.coordPoint_coordinateMap
      (P.progression.activeDimensions_proper hproper) _
  have hnPoint : P.progression.coordPoint n =
      BoundingBox.intPoint z.1 := by
    exact P.progression.coordPoint_coordinateMap hproper _
  have hembed : P.progression.activeCoordToFull m = n := by
    apply hproper
    rw [P.progression.coordPoint_activeCoordToFull, hmPoint, hnPoint]
  funext j
  change ((m j : ℕ) : ℤ) = ((n (P.progression.activeIndex j) : ℕ) : ℤ)
  have hj := congrArg
    (fun c : P.progression.Coord ↦ (c (P.progression.activeIndex j) : ℕ))
      hembed
  simpa only [P.progression.activeCoordToFull_activeIndex] using
    congrArg (fun a : ℕ ↦ (a : ℤ)) hj

/-- The centered active identification is exactly the projection of the
centered full identification. -/
theorem centeredIdentification_activeDimensions {A : Finset ℤ} {d : ℕ}
    (P : BoundingBox.BoundingGAP A d) (hproper : P.progression.Proper)
    (hzero : 0 ∈ A) :
    centeredIdentification P.activeDimensions
        (P.activeDimensions_proper hproper) hzero =
      fun z ↦ activeCoordinateProjection P.progression
        (centeredIdentification P hproper hzero z) := by
  funext z
  by_cases hz : z ∈ A
  · rw [centeredIdentification_apply _ _ _ hz,
      centeredIdentification_apply _ _ _ hz,
      map_sub, activeDimensions_identificationMap,
      activeDimensions_identificationMap]
  · simp only [centeredIdentification, dif_neg hz, map_neg,
      activeDimensions_identificationMap]
    rw [activeDimensions_identificationMap]

/-- Canonical centered minimal-box coordinates, after deleting inactive
directions, agree with the centered coordinates of the active bounding GAP. -/
theorem centeredIdentification_activeMinimalBox
    {W : Finset ℤ} {d : ℕ} {relevant : Finset ℕ}
    (hproper : Stability.RelevantBoxesProper W relevant)
    (hd : d ∈ relevant) (hzero : 0 ∈ W) :
    let P := BoundingBox.dBoundingBox W d (hproper.positive hd)
    centeredIdentification P.activeDimensions
        (P.activeDimensions_proper (hproper.proper hd)) hzero =
      fun z ↦ activeCoordinateProjection P.progression
        (Stability.centeredMinimalIdentificationFamily hproper d z) := by
  let P := BoundingBox.dBoundingBox W d (hproper.positive hd)
  have hfull := centeredIdentification_activeDimensions
    P (hproper.proper hd) hzero
  have hcanonical :=
    centeredIdentification_eq_centeredMinimalIdentificationFamily
      hproper hd hzero
  simpa only [P, hcanonical] using hfull

/-- Generated subgroups commute with an additive coordinate projection. -/
theorem generatedSubgroup_activeCoordinateProjection
    {A : Type*} [DecidableEq A] {d : ℕ} (P : GAP 1 d)
    (phi : A → LatticePoint d) (S : Finset A) :
    Stability.generatedSubgroup
        (fun z ↦ activeCoordinateProjection P (phi z)) S =
      AddSubgroup.map (activeCoordinateProjection P)
        (Stability.generatedSubgroup phi S) := by
  unfold Stability.generatedSubgroup
  rw [AddMonoidHom.map_closure]
  congr 1
  rw [Set.image_image]

/-- A common-span equality in the full canonical coordinates descends to
the active centered coordinates. -/
theorem generatedSubgroup_centeredActive_eq_of_centeredMinimal_eq
    {W S T : Finset ℤ} {d : ℕ} {relevant : Finset ℕ}
    (hproper : Stability.RelevantBoxesProper W relevant)
    (hd : d ∈ relevant) (hzero : 0 ∈ W)
    (hspan : Stability.generatedSubgroup
          (Stability.centeredMinimalIdentificationFamily hproper d) S =
        Stability.generatedSubgroup
          (Stability.centeredMinimalIdentificationFamily hproper d) T) :
    let P := BoundingBox.dBoundingBox W d (hproper.positive hd)
    Stability.generatedSubgroup
        (centeredIdentification P.activeDimensions
          (P.activeDimensions_proper (hproper.proper hd)) hzero) S =
      Stability.generatedSubgroup
        (centeredIdentification P.activeDimensions
          (P.activeDimensions_proper (hproper.proper hd)) hzero) T := by
  dsimp only
  rw [centeredIdentification_activeMinimalBox hproper hd hzero,
    generatedSubgroup_activeCoordinateProjection,
    generatedSubgroup_activeCoordinateProjection, hspan]

/-- Physical subset-sum density bounds the selected-to-ambient relative
index in the centered coordinates of any proper bounding presentation.  In
particular this applies to the nondegenerate active presentation above. -/
theorem centeredPhysicalDensity_relIndex_ne_zero_and_le_boundingGAP
    {W A B : Finset ℤ} {d h K : ℕ}
    (P : BoundingBox.BoundingGAP W d) (hproper : P.progression.Proper)
    (hAW : A ⊆ W) (hzeroW : 0 ∈ W) (hzeroA : 0 ∈ A)
    (hBA : B ⊆ A) (hBcard : B.card ≤ h) (hKh : K ≤ h)
    (hdensity : (P.progression.dilate (2 * h)).volume ≤
      K * (Greedy.subsetSums B).card) :
    let phi := centeredIdentification P hproper hzeroW
    (Stability.generatedSubgroup phi B).relIndex
          (Stability.generatedSubgroup phi A) ≠ 0 ∧
      (Stability.generatedSubgroup phi B).relIndex
          (Stability.generatedSubgroup phi A) ≤ K := by
  classical
  let phi := centeredIdentification P hproper hzeroW
  let raw : ℤ → LatticePoint d := fun z ↦
    if hz : z ∈ W then P.identificationMap hproper ⟨z, hz⟩ else 0
  let B0 := insert 0 B
  have hB0A : B0 ⊆ A := Finset.insert_subset hzeroA hBA
  let X := coordinateGeneratorFinset phi A
  let XB := ambientSubsetGeneratorFinset phi A B0 hB0A
  let S := constantIteratedSumset XB h
  have hSsub : S ⊆ constantIteratedSumset X h :=
    constantIteratedSumset_mono_set
      (ambientSubsetGeneratorFinset_subset phi hB0A) h
  have hSH : ∀ s ∈ S,
      (s.1 : LatticePoint d) ∈ Stability.generatedSubgroup phi B0 := by
    intro s hs
    exact ambientSubsetIteratedSumset_mem_generatedSubgroup phi hB0A hs
  have hpack := quotientGeneratorIteratedSumset_card_mul_le_twice
    (Stability.generatedSubgroup_mono hB0A) X S h hSsub hSH
  have heval : ∀ z (hz : z ∈ A),
      stepEvaluation P.progression (phi z) = z := by
    intro z hz
    rw [show phi z =
        P.identificationMap hproper ⟨z, hAW hz⟩ -
          P.identificationMap hproper ⟨0, hzeroW⟩ by
      exact centeredIdentification_apply P hproper hzeroW (hAW hz)]
    exact stepEvaluation_centeredIdentificationMap
      P hproper hzeroW ⟨z, hAW hz⟩
  have hphysicalLower : (Greedy.subsetSums B).card ≤ S.card := by
    calc
      (Greedy.subsetSums B).card ≤
          (GrowthLemmas.multifoldSumset h B0).card :=
        Finset.card_le_card
          (Greedy.subsetSums_subset_multifoldSumset_insert_zero_of_card_le
            hBcard)
      _ ≤ S.card := by
        simpa only [S, XB, B0] using
          card_multifoldSumset_le_ambientSubsetIteratedSumset_of_evaluation
            hB0A phi (stepEvaluation P.progression) heval
  have hraw : ∀ z (hz : z ∈ A), raw z =
      P.identificationMap hproper ⟨z, hAW hz⟩ := by
    intro z hz
    simp only [raw, dif_pos (hAW hz)]
  have hcentered : ∀ z (hz : z ∈ A), phi z = raw z - raw 0 := by
    intro z hz
    rw [show phi z =
        P.identificationMap hproper ⟨z, hAW hz⟩ -
          P.identificationMap hproper ⟨0, hzeroW⟩ by
      exact centeredIdentification_apply P hproper hzeroW (hAW hz)]
    rw [hraw z hz]
    simp only [raw, dif_pos hzeroW]
  have hambientUpper : (constantIteratedSumset X (2 * h)).card ≤
      (P.progression.dilate (2 * h)).volume := by
    exact card_centeredSubsetCoordinateGeneratorIteratedSumset_le_dilate_volume
      P hproper hAW raw phi hzeroA hraw hcentered (2 * h)
  have hmul :
      (quotientGeneratorIteratedSumset
        (Stability.generatedSubgroup phi B0)
        (Stability.generatedSubgroup phi A) X h).card * S.card ≤
        K * S.card := by
    calc
      _ ≤ (constantIteratedSumset X (2 * h)).card := hpack
      _ ≤ (P.progression.dilate (2 * h)).volume := hambientUpper
      _ ≤ K * (Greedy.subsetSums B).card := hdensity
      _ ≤ K * S.card := Nat.mul_le_mul_left K hphysicalLower
  have hSpos : 0 < S.card := by
    have hsubsetPos : 0 < (Greedy.subsetSums B).card :=
      Finset.card_pos.mpr ⟨0, Greedy.zero_mem_subsetSums B⟩
    omega
  have hcard :
      (quotientGeneratorIteratedSumset
        (Stability.generatedSubgroup phi B0)
        (Stability.generatedSubgroup phi A)
        (coordinateGeneratorFinset phi A) h).card ≤ K := by
    dsimp only [X] at hmul
    exact Nat.le_of_mul_le_mul_right hmul hSpos
  have hindex := generatedSubgroup_relIndex_ne_zero_and_le_of_quotient_sumset
    phi hB0A hKh hcard
  have hphiZero : phi 0 = 0 :=
    centeredIdentification_zero P hproper hzeroW
  have hgen : Stability.generatedSubgroup phi B0 =
      Stability.generatedSubgroup phi B := by
    exact RandomPartition.generatedSubgroup_insert_zero_eq phi B hphiZero
  simpa only [B0, hgen] using hindex

end Preprocessing

end

end Erdos186.CFP

#print axioms
  Erdos186.CFP.BoundingBox.BoundingGAP.activeRank_pos
#print axioms
  Erdos186.CFP.Preprocessing.centeredIdentification_activeMinimalBox
#print axioms
  Erdos186.CFP.Preprocessing.generatedSubgroup_centeredActive_eq_of_centeredMinimal_eq
#print axioms
  Erdos186.CFP.Preprocessing.centeredPhysicalDensity_relIndex_ne_zero_and_le_boundingGAP
