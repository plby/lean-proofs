/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.CFP.RandomGreedyCorollary217Density

/-!
# Relative index in fixed centered minimal-box coordinates

The random-color stage keeps the coordinate system of an outer source `W`,
while the immediate ambient set for generator completion is one anchored
color class `A`.  This is the fixed-reference centered form of CFP Lemma
2.32 needed to bridge those two layers.
-/

namespace Erdos186.CFP

open scoped BigOperators

noncomputable section

namespace Preprocessing

/-- A centered coordinate-generator sumset for a subset `A ⊆ W` is still
contained, after the standard fixed translation, in the coefficient
dilation of the outer bounding box of `W`. -/
theorem card_centeredSubsetCoordinateGeneratorIteratedSumset_le_dilate_volume
    {W A : Finset ℤ} {d : ℕ}
    (P : BoundingBox.BoundingGAP W d) (hproper : P.progression.Proper)
    (hAW : A ⊆ W) (raw centered : ℤ → LatticePoint d)
    (hzeroA : 0 ∈ A)
    (hraw : ∀ z (hz : z ∈ A), raw z =
      P.identificationMap hproper ⟨z, hAW hz⟩)
    (hcentered : ∀ z (hz : z ∈ A), centered z = raw z - raw 0)
    (k : ℕ) :
    (constantIteratedSumset (coordinateGeneratorFinset centered A) k).card ≤
      (P.progression.dilate k).volume := by
  classical
  let Gamma := Stability.generatedSubgroup centered A
  let X := coordinateGeneratorFinset centered A
  let S := constantIteratedSumset X k
  let shift : Gamma → LatticePoint d := fun x ↦ x.1 + k • raw 0
  have hshiftInjective : Function.Injective shift := by
    intro x y hxy
    apply Subtype.ext
    exact add_right_cancel hxy
  have hrawBox : A.image raw ⊆ coordinateBox P.progression 1 := by
    intro x hx
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
    rw [hraw a ha]
    exact identificationMap_mem_coordinateBox P hproper ⟨a, hAW ha⟩
  have hshiftSubset : S.image shift ⊆ coordinateBox P.progression k := by
    intro y hy
    obtain ⟨x, hxS, rfl⟩ := Finset.mem_image.mp hy
    obtain ⟨f, hf, hsum⟩ := mem_constantIteratedSumset_iff.mp hxS
    have hterm : ∀ i : Fin k, ∃ a ∈ A, (f i).1 = centered a := by
      intro i
      have hfi := hf i
      rw [show X = insert 0 (A.attach.image fun a ↦
          ⟨centered a.1, Stability.image_mem_generatedSubgroup a.2⟩) by
        rfl] at hfi
      rcases Finset.mem_insert.mp hfi with hfi | hfi
      · refine ⟨0, hzeroA, ?_⟩
        rw [hfi, hcentered 0 hzeroA]
        simp
      · obtain ⟨a, _ha, hai⟩ := Finset.mem_image.mp hfi
        exact ⟨a.1, a.2, (congrArg Subtype.val hai).symm⟩
    choose a ha hfa using hterm
    let g : Fin k → LatticePoint d := fun i ↦ raw (a i)
    have hg (i : Fin k) : g i ∈ A.image raw :=
      Finset.mem_image.mpr ⟨a i, ha i, rfl⟩
    have hgsum : (∑ i, g i) ∈ constantIteratedSumset (A.image raw) k :=
      mem_constantIteratedSumset_iff.mpr ⟨g, hg, rfl⟩
    have hsumBox : (∑ i, g i) ∈ coordinateBox P.progression k :=
      constantIteratedSumset_subset_coordinateBox P.progression
        (A.image raw) hrawBox k hgsum
    have hxsum : (x.1 : LatticePoint d) = ∑ i, centered (a i) := by
      rw [← hsum]
      change Gamma.subtype (∑ i, f i) = _
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro i _hi
      exact hfa i
    have hshiftEq : shift x = ∑ i, g i := by
      funext j
      simp only [shift, hxsum, g, Finset.sum_apply, Pi.add_apply,
        Pi.smul_apply, nsmul_eq_mul, hcentered (a _) (ha _), Pi.sub_apply]
      simp
    rw [hshiftEq]
    exact hsumBox
  calc
    (constantIteratedSumset (coordinateGeneratorFinset centered A) k).card =
        S.card := rfl
    _ = (S.image shift).card :=
      (Finset.card_image_of_injective S hshiftInjective).symm
    _ ≤ (coordinateBox P.progression k).card :=
      Finset.card_le_card hshiftSubset
    _ = (P.progression.dilate k).volume := card_coordinateBox _ _

/-- Rank-flexible relative-index control for a subset `B ⊆ A` when both
are measured in the centered coordinates of a fixed outer box `W`.

The coefficient `16` is the fixed-reference cost already present in
`fixedMinimalReference_two_mul_dilate_volume_le`; no additional geometric
or cardinality assumption is introduced here. -/
theorem HApproximation.fixedMinimalReference_centered_relIndex_general_ne_zero_and_le
    {W A B : Finset ℤ} {x D n h d e scaleNum scaleDen : ℕ}
    {relevant : Finset ℕ}
    (hproper : Stability.RelevantBoxesProper W relevant)
    (hdmem : d ∈ relevant) (hAW : A ⊆ W) (hzeroW : 0 ∈ W)
    (hzeroA : 0 ∈ A)
    (hstable : Stability.WeaklyStableFor A
      (Stability.minimalBoxFamily W) x D (n ^ 2))
    (hBA : B ⊆ A) (hloss : A.card ≤ B.card + x)
    (VA : HDimension.HApproximation A h d scaleNum scaleDen)
    (VB : HDimension.HApproximation B h e scaleNum scaleDen)
    (he : 0 < e) (hdD : d ≤ D) (heD : e ≤ D)
    (hhn : h ≤ n) (hA : ∀ z ∈ A, 0 ≤ z ∧ z < (n : ℤ))
    (hnumericA :
      (2 * scaleDen) ^ d * (h + 1) ^ (d - 1) <
        (scaleNum * h) ^ d)
    (hnumericB :
      (2 * scaleDen) ^ e * (h + 1) ^ (e - 1) <
        (scaleNum * h) ^ e)
    (hlarge : 16 * (6 * scaleDen) ^ D * (4 * scaleDen) ^ D ≤ h) :
    let phi := Stability.centeredMinimalIdentificationFamily hproper d
    (Stability.generatedSubgroup phi B).relIndex
          (Stability.generatedSubgroup phi A) ≠ 0 ∧
      (Stability.generatedSubgroup phi B).relIndex
          (Stability.generatedSubgroup phi A) ≤
        16 * (6 * scaleDen) ^ D * (4 * scaleDen) ^ D := by
  classical
  let P := BoundingBox.dBoundingBox W d (hproper.positive hdmem)
  let raw := Stability.minimalIdentificationFamily hproper d
  let phi := Stability.centeredMinimalIdentificationFamily hproper d
  let X := coordinateGeneratorFinset phi A
  let XB := ambientSubsetGeneratorFinset phi A B hBA
  let S := constantIteratedSumset XB h
  have hSsub : S ⊆ constantIteratedSumset X h :=
    constantIteratedSumset_mono_set
      (ambientSubsetGeneratorFinset_subset phi hBA) h
  have hSH : ∀ s ∈ S,
      (s.1 : LatticePoint d) ∈ Stability.generatedSubgroup phi B := by
    intro s hs
    exact ambientSubsetIteratedSumset_mem_generatedSubgroup phi hBA hs
  have hpack := quotientGeneratorIteratedSumset_card_mul_le_twice
    (Stability.generatedSubgroup_mono hBA) X S h hSsub hSH
  have heval : ∀ z (hz : z ∈ A),
      stepEvaluation P.progression (phi z) = z := by
    intro z hz
    rw [show phi z =
        P.identificationMap (hproper.proper hdmem) ⟨z, hAW hz⟩ -
          P.identificationMap (hproper.proper hdmem) ⟨0, hzeroW⟩ by
      dsimp only [phi, Stability.centeredMinimalIdentificationFamily]
      rw [
        Stability.minimalIdentificationFamily_apply hproper hdmem (hAW hz),
        Stability.minimalIdentificationFamily_apply hproper hdmem hzeroW]]
    exact stepEvaluation_centeredIdentificationMap
      P (hproper.proper hdmem) hzeroW ⟨z, hAW hz⟩
  have hsumLower : (GrowthLemmas.multifoldSumset h B).card ≤ S.card := by
    exact card_multifoldSumset_le_ambientSubsetIteratedSumset_of_evaluation
      hBA phi (stepEvaluation P.progression) heval
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
  have hvolume : (P.progression.dilate (2 * h)).volume ≤
      (16 * (6 * scaleDen) ^ d * (4 * scaleDen) ^ e) *
        (GrowthLemmas.multifoldSumset h B).card := by
    exact HApproximation.fixedMinimalReference_two_mul_dilate_volume_le
      hAW hstable hBA hloss VA VB (hproper.positive hdmem) he hdD heD
        hhn hA hnumericA hnumericB
  let Kde := 16 * (6 * scaleDen) ^ d * (4 * scaleDen) ^ e
  let KD := 16 * (6 * scaleDen) ^ D * (4 * scaleDen) ^ D
  have hKde : Kde ≤ KD := by
    dsimp only [Kde, KD]
    have h6pos : 1 ≤ 6 * scaleDen := by
      have := VA.scaleDen_pos
      omega
    have h4pos : 1 ≤ 4 * scaleDen := by
      have := VA.scaleDen_pos
      omega
    have hp6 : (6 * scaleDen) ^ d ≤ (6 * scaleDen) ^ D :=
      pow_le_pow_right' h6pos hdD
    have hp4 : (4 * scaleDen) ^ e ≤ (4 * scaleDen) ^ D :=
      pow_le_pow_right' h4pos heD
    exact Nat.mul_le_mul (Nat.mul_le_mul_left 16 hp6) hp4
  have hmul :
      (quotientGeneratorIteratedSumset
        (Stability.generatedSubgroup phi B)
        (Stability.generatedSubgroup phi A) X h).card * S.card ≤
        KD * S.card := by
    calc
      _ ≤ (constantIteratedSumset X (2 * h)).card := hpack
      _ ≤ (P.progression.dilate (2 * h)).volume := hambientUpper
      _ ≤ Kde * (GrowthLemmas.multifoldSumset h B).card := hvolume
      _ ≤ Kde * S.card := by gcongr
      _ ≤ KD * S.card := Nat.mul_le_mul_right S.card hKde
  have hSpos : 0 < S.card := by
    have hzeroB : 0 ∈ GrowthLemmas.multifoldSumset h B :=
      GrowthLemmas.zero_mem_multifoldSumset VB.zero_mem h
    have hpositive : 0 < (GrowthLemmas.multifoldSumset h B).card :=
      Finset.card_pos.mpr ⟨0, hzeroB⟩
    omega
  have hcard :
      (quotientGeneratorIteratedSumset
        (Stability.generatedSubgroup phi B)
        (Stability.generatedSubgroup phi A)
        (coordinateGeneratorFinset phi A) h).card ≤ KD := by
    dsimp only [X] at hmul
    exact Nat.le_of_mul_le_mul_right hmul hSpos
  apply generatedSubgroup_relIndex_ne_zero_and_le_of_quotient_sumset
    phi hBA (by simpa only [KD] using hlarge)
  simpa only [KD] using hcard

end Preprocessing

end


end Erdos186.CFP

#print axioms
  Erdos186.CFP.Preprocessing.HApproximation.fixedMinimalReference_centered_relIndex_general_ne_zero_and_le
