/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.CFP.CenteredFixedReferenceIndex
import ErdosProblems.Erdos186.CFP.RandomPartitionSharp

/-!
# Relative index from physical subset-sum density

After the independently run colour-greedy arguments, CFP no longer uses an
approximation of the selected reserve.  Instead, its ordinary subset sums
occupy a fixed positive proportion of the final global coefficient box.
The quotient-packing argument then bounds the index of the selected
coordinate subgroup in the full colour subgroup.  This formulation keeps
the colour's dyadic rank and level entirely out of the final coordinate
system.
-/

namespace Erdos186.CFP

noncomputable section

namespace Greedy

/-- Every subset sum uses at most `B.card` summands; after adjoining zero it
is therefore an element of the `B.card`-fold sumset. -/
theorem subsetSums_subset_multifoldSumset_card_insert_zero (B : Finset ℤ) :
    subsetSums B ⊆
      GrowthLemmas.multifoldSumset B.card (insert 0 B) := by
  classical
  induction B using Finset.induction_on with
  | empty => simp
  | @insert a B ha ih =>
      rw [subsetSums_insert ha, Finset.card_insert_of_notMem ha]
      intro z hz
      rcases Finset.mem_union.mp hz with hz | hz
      · have hz' : z ∈ GrowthLemmas.multifoldSumset B.card
            (insert 0 (insert a B)) := by
          apply HDimension.multifoldSumset_mono_set B.card
            (show insert 0 B ⊆ insert 0 (insert a B) by simp)
          exact ih hz
        exact GrowthLemmas.multifoldSumset_mono_index
          (show 0 ∈ insert 0 (insert a B) by simp) (by omega) hz'
      · obtain ⟨y, hy, rfl⟩ := GrowthLemmas.mem_translate_iff.mp hz
        apply GrowthLemmas.mem_multifoldSumset_succ_iff.mpr
        refine ⟨y, ?_, a, by simp, add_comm y a⟩
        apply HDimension.multifoldSumset_mono_set B.card
          (show insert 0 B ⊆ insert 0 (insert a B) by simp)
        exact ih hy

/-- The same inclusion at any larger fold. -/
theorem subsetSums_subset_multifoldSumset_insert_zero_of_card_le
    {B : Finset ℤ} {h : ℕ} (hBh : B.card ≤ h) :
    subsetSums B ⊆ GrowthLemmas.multifoldSumset h (insert 0 B) := by
  exact (subsetSums_subset_multifoldSumset_card_insert_zero B).trans
    (GrowthLemmas.multifoldSumset_mono_index (by simp) hBh)

end Greedy

namespace Preprocessing

/-- Physical subset-sum density in a fixed outer centered box bounds the
relative index of the selected subgroup in its ambient colour subgroup.

`B.card ≤ h` permits padding a subset sum by zero to an exact `h`-fold
sum.  `K ≤ h` is the standard finite-quotient saturation threshold. -/
theorem centeredPhysicalDensity_relIndex_ne_zero_and_le
    {W A B : Finset ℤ} {d h K : ℕ} {relevant : Finset ℕ}
    (hproper : Stability.RelevantBoxesProper W relevant)
    (hdmem : d ∈ relevant) (hAW : A ⊆ W) (hzeroW : 0 ∈ W)
    (hzeroA : 0 ∈ A) (hBA : B ⊆ A)
    (hBcard : B.card ≤ h) (hKh : K ≤ h)
    (hdensity :
      (((BoundingBox.dBoundingBox W d
        (hproper.positive hdmem)).progression).dilate (2 * h)).volume ≤
        K * (Greedy.subsetSums B).card) :
    let phi := Stability.centeredMinimalIdentificationFamily hproper d
    (Stability.generatedSubgroup phi B).relIndex
          (Stability.generatedSubgroup phi A) ≠ 0 ∧
      (Stability.generatedSubgroup phi B).relIndex
          (Stability.generatedSubgroup phi A) ≤ K := by
  classical
  let P := BoundingBox.dBoundingBox W d (hproper.positive hdmem)
  let raw := Stability.minimalIdentificationFamily hproper d
  let phi := Stability.centeredMinimalIdentificationFamily hproper d
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
        P.identificationMap (hproper.proper hdmem) ⟨z, hAW hz⟩ -
          P.identificationMap (hproper.proper hdmem) ⟨0, hzeroW⟩ by
      dsimp only [phi, Stability.centeredMinimalIdentificationFamily]
      rw [Stability.minimalIdentificationFamily_apply hproper hdmem (hAW hz),
        Stability.minimalIdentificationFamily_apply hproper hdmem hzeroW]]
    exact stepEvaluation_centeredIdentificationMap
      P (hproper.proper hdmem) hzeroW ⟨z, hAW hz⟩
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
      P.identificationMap (hproper.proper hdmem) ⟨z, hAW hz⟩ := by
    intro z hz
    exact Stability.minimalIdentificationFamily_apply hproper hdmem (hAW hz)
  have hcentered : ∀ z (_hz : z ∈ A), phi z = raw z - raw 0 := by
    intro z _hz
    rfl
  have hambientUpper : (constantIteratedSumset X (2 * h)).card ≤
      (P.progression.dilate (2 * h)).volume := by
    exact card_centeredSubsetCoordinateGeneratorIteratedSumset_le_dilate_volume
      P (hproper.proper hdmem) hAW raw phi hzeroA hraw hcentered (2 * h)
  have hmul :
      (quotientGeneratorIteratedSumset
        (Stability.generatedSubgroup phi B0)
        (Stability.generatedSubgroup phi A) X h).card * S.card ≤
        K * S.card := by
    calc
      _ ≤ (constantIteratedSumset X (2 * h)).card := hpack
      _ ≤ (P.progression.dilate (2 * h)).volume := hambientUpper
      _ ≤ K * (Greedy.subsetSums B).card := by
        simpa only [P] using hdensity
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
    Stability.centeredMinimalIdentificationFamily_zero hproper d
  have hgen : Stability.generatedSubgroup phi B0 =
      Stability.generatedSubgroup phi B := by
    exact RandomPartition.generatedSubgroup_insert_zero_eq phi B hphiZero
  simpa only [B0, hgen] using hindex

end Preprocessing

end


end Erdos186.CFP

#print axioms
  Erdos186.CFP.Preprocessing.centeredPhysicalDensity_relIndex_ne_zero_and_le
