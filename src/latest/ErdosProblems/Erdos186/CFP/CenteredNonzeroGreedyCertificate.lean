/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.CFP.CenteredScaledGreedyCompletionCertificate
import ErdosProblems.Erdos186.CFP.CenteredFixedReferenceIndex
import ErdosProblems.Erdos186.CFP.RandomPartitionGeneratedSubgroup

/-!
# Centered certificate from greedy runs on the nonzero colored source

This is the finite source-shaped join after sharp random coloring.  Colors
are taken on `B.erase 0`; zero is reattached only for stability,
H-approximation, and common-span statements.  The completed reserves remain
subsets of the nonzero source, while the resulting certificate has core `B`.
-/

namespace Erdos186.CFP

noncomputable section

namespace RandomPartition

/-- The retained-positive-rank finite endpoint.

The two approximation inputs are the actual dyadic-scale facts needed by
the source proof: one rank-`d` approximation of every anchored color and a
rank-flexible approximation of every large anchored subset.  From these the
theorem proves both the common-box density and the bounded generator-
completion index, rather than accepting either as a proposition. -/
theorem exists_centeredScaledNonzeroGreedyCertificateConstants
    (d D scaleNum scaleDen : ℕ) (hd : 0 < d) (hdD : d ≤ D)
    (hscaleDen : 0 < scaleDen) :
    ∃ corConstant corWidth denseConstant denseEll denseWidth : ℕ,
      0 < corConstant ∧ 0 < denseConstant ∧
      ∀ {W B : Finset ℤ} {relevant : Finset ℕ}
        (hproper : Stability.RelevantBoxesProper W relevant),
        (hdrel : d ∈ relevant) → B ⊆ W → 0 ∈ B →
        ∀ {n q deletionBudget steps level sourceScale s C0 : ℕ}
          (c : {a // a ∈ B.erase 0} → Fin (q + 1)),
          (∀ z ∈ W, 0 ≤ z ∧ z < (n : ℤ)) →
          denseEll ≤ q + 1 →
          max corWidth denseWidth ≤
            (Preprocessing.centeredCoordinateAxisBox
              (BoundingBox.dBoundingBox W d
                (hproper.positive hdrel)).progression
              sourceScale).minWidth →
          denseConstant ≤ q + 1 →
          sourceScale = 2 ^ level →
          0 < steps →
          (∀ i, steps ≤
            (integerColorClass (B.erase 0) c i).card) →
          (∀ i, Greedy.dyadicBinStart
            (integerColorClass (B.erase 0) c i)
              deletionBudget steps level < steps) →
          (∀ i, (integerColorClass (B.erase 0) c i).card ≤
            steps + deletionBudget) →
          (∀ i, Stability.StronglyStableFor
            (anchoredColorClass (B.erase 0) c i)
            (Stability.minimalBoxFamily W) deletionBudget D (n ^ 2)
              relevant
              (Stability.centeredMinimalIdentificationFamily hproper) C0) →
          (∀ i, Stability.generatedSubgroup
              (Stability.centeredMinimalIdentificationFamily hproper d)
              (anchoredColorClass (B.erase 0) c i) =
            Stability.generatedSubgroup
              (Stability.centeredMinimalIdentificationFamily hproper d) B) →
          (∀ i, HDimension.HApproximation
            (anchoredColorClass (B.erase 0) c i) (2 ^ level) d
              scaleNum scaleDen) →
          2 ^ level ≤ n →
          (2 * scaleDen) ^ d *
              (2 ^ level + 1) ^ (d - 1) <
            (scaleNum * 2 ^ level) ^ d →
          (∀ i, ∀ {T : Finset ℤ},
            T ⊆ integerColorClass (B.erase 0) c i →
            (integerColorClass (B.erase 0) c i).card ≤
              T.card + deletionBudget →
            ∃ e : ℕ, 0 < e ∧ e ≤ D ∧
              ∃ V : HDimension.HApproximation
                  (insert 0 T) (2 ^ level) e scaleNum scaleDen,
                (2 * scaleDen) ^ e * (2 ^ level + 1) ^ (e - 1) <
                  (scaleNum * 2 ^ level) ^ e) →
          16 * (6 * scaleDen) ^ D * (4 * scaleDen) ^ D ≤ 2 ^ level →
          steps + 16 * (6 * scaleDen) ^ D * (4 * scaleDen) ^ D ≤
            sourceScale →
          (q + 1) *
              (steps + 16 * (6 * scaleDen) ^ D * (4 * scaleDen) ^ D) ≤ s →
          s ≤ 2 * (q + 1) * sourceScale →
          sourceScale * ((q + 1) / denseConstant) ≤ s →
          (((BoundingBox.dBoundingBox W d
              (hproper.positive hdrel)).progression).dilate
            (((q + 1) / denseConstant) * corConstant *
              (2 * sourceScale))).Proper →
          Nonempty (PreprocessedReserveCertificate B s D 0 1
            (4 * denseConstant)) := by
  let volumeConstant :=
    32 * (6 * scaleDen) ^ D * (4 * scaleDen) ^ D
  have hvolumeConstant : 0 < volumeConstant := by
    dsimp only [volumeConstant]
    positivity
  obtain ⟨corConstant, corWidth, denseConstant, denseEll, denseWidth,
      hcorConstant, hdenseConstant, hcertificate⟩ :=
    exists_centeredScaledGreedyCompletionReserveCertificateConstants
      d hd 1 volumeConstant (by omega) (by omega)
  refine ⟨corConstant, corWidth, denseConstant, denseEll, denseWidth,
    hcorConstant, hdenseConstant, ?_⟩
  intro W B relevant hproper hdrel hBW hzeroB n q
    deletionBudget steps level sourceScale s C0 c hWinterval hell hwidth hCell
    hsourceScale hstepsPos hsteps hcross hnear hstable hspan happrox
    hfoldn hnumeric haccessible hindexLarge hsourceBound hsLower hsUpper
    hscaleUpper hnoCarry
  let phi := Stability.centeredMinimalIdentificationFamily hproper d
  let indexBound := 16 * (6 * scaleDen) ^ D * (4 * scaleDen) ^ D
  have hsourceSubset : B.erase 0 ⊆ B := Finset.erase_subset 0 B
  have hsourceScalePos : 0 < sourceScale := by
    rw [hsourceScale]
    positivity
  have hfinite : ∀ i,
      (Stability.generatedSubgroup phi
          (Greedy.selected (integerColorClass (B.erase 0) c i) steps)).relIndex
        (Stability.generatedSubgroup phi
          (integerColorClass (B.erase 0) c i)) ≠ 0 := by
    intro i
    let S := integerColorClass (B.erase 0) c i
    let T := Greedy.selected S steps
    have hzeroS : 0 ∉ S := by
      intro hzero
      exact Finset.notMem_erase 0 B (integerColorClass_subset (B.erase 0) c i hzero)
    have hzeroT : 0 ∉ T := fun hzero ↦
      hzeroS (Greedy.selected_subset S steps hzero)
    obtain ⟨e, he, heD, V, hnumericV⟩ :=
      haccessible i (T := T) (Greedy.selected_subset S steps) (by
        rw [Greedy.card_selected_eq (hsteps i)]
        exact hnear i)
    have hanchoredSubset : insert 0 T ⊆ anchoredColorClass (B.erase 0) c i := by
      exact Finset.insert_subset (by simp [anchoredColorClass])
        ((Greedy.selected_subset S steps).trans
          (Finset.subset_insert 0 S))
    have hcardAnchored : (anchoredColorClass (B.erase 0) c i).card ≤
        (insert 0 T).card + deletionBudget := by
      change (insert 0 S).card ≤ (insert 0 T).card + deletionBudget
      rw [Finset.card_insert_of_notMem hzeroS,
        Finset.card_insert_of_notMem hzeroT,
        Greedy.card_selected_eq (hsteps i)]
      exact (Nat.add_le_add_right (hnear i) 1).trans_eq (by omega)
    have hanchoredW : anchoredColorClass (B.erase 0) c i ⊆ W := by
      intro z hz
      rcases Finset.mem_insert.mp hz with rfl | hz
      · exact hBW hzeroB
      · exact hBW (hsourceSubset (integerColorClass_subset (B.erase 0) c i hz))
    have hresult :=
      Preprocessing.HApproximation.fixedMinimalReference_centered_relIndex_general_ne_zero_and_le
        hproper hdrel
        hanchoredW
        (hBW hzeroB) (by simp [anchoredColorClass])
        (hstable i).weaklyStable hanchoredSubset hcardAnchored
        (happrox i) V he hdD heD hfoldn
        (fun z hz ↦ hWinterval z
          (hanchoredW hz))
        hnumeric hnumericV hindexLarge
    change
      (Stability.generatedSubgroup phi (insert 0 T)).relIndex
          (Stability.generatedSubgroup phi
            (anchoredColorClass (B.erase 0) c i)) ≠ 0 ∧
        (Stability.generatedSubgroup phi (insert 0 T)).relIndex
          (Stability.generatedSubgroup phi
            (anchoredColorClass (B.erase 0) c i)) ≤ indexBound at hresult
    have hTgroup : Stability.generatedSubgroup phi (insert 0 T) =
        Stability.generatedSubgroup phi T :=
      generatedSubgroup_insert_zero_eq phi T
        (Stability.centeredMinimalIdentificationFamily_zero hproper d)
    have hSgroup : Stability.generatedSubgroup phi S =
        Stability.generatedSubgroup phi (anchoredColorClass (B.erase 0) c i) :=
      generatedSubgroup_integerColorClass_eq_anchoredColorClass c i phi
        (Stability.centeredMinimalIdentificationFamily_zero hproper d)
    rw [hTgroup, ← hSgroup] at hresult
    exact hresult.1
  have hindex : ∀ i,
      (Stability.generatedSubgroup phi
          (Greedy.selected (integerColorClass (B.erase 0) c i) steps)).relIndex
        (Stability.generatedSubgroup phi
          (integerColorClass (B.erase 0) c i)) ≤ indexBound := by
    intro i
    let S := integerColorClass (B.erase 0) c i
    let T := Greedy.selected S steps
    have hzeroS : 0 ∉ S := by
      intro hzero
      exact Finset.notMem_erase 0 B (integerColorClass_subset (B.erase 0) c i hzero)
    have hzeroT : 0 ∉ T := fun hzero ↦
      hzeroS (Greedy.selected_subset S steps hzero)
    obtain ⟨e, he, heD, V, hnumericV⟩ :=
      haccessible i (T := T) (Greedy.selected_subset S steps) (by
        rw [Greedy.card_selected_eq (hsteps i)]
        exact hnear i)
    have hanchoredSubset : insert 0 T ⊆ anchoredColorClass (B.erase 0) c i := by
      exact Finset.insert_subset (by simp [anchoredColorClass])
        ((Greedy.selected_subset S steps).trans
          (Finset.subset_insert 0 S))
    have hcardAnchored : (anchoredColorClass (B.erase 0) c i).card ≤
        (insert 0 T).card + deletionBudget := by
      change (insert 0 S).card ≤ (insert 0 T).card + deletionBudget
      rw [Finset.card_insert_of_notMem hzeroS,
        Finset.card_insert_of_notMem hzeroT,
        Greedy.card_selected_eq (hsteps i)]
      exact (Nat.add_le_add_right (hnear i) 1).trans_eq (by omega)
    have hanchoredW : anchoredColorClass (B.erase 0) c i ⊆ W := by
      intro z hz
      rcases Finset.mem_insert.mp hz with rfl | hz
      · exact hBW hzeroB
      · exact hBW (hsourceSubset (integerColorClass_subset (B.erase 0) c i hz))
    have hresult :=
      Preprocessing.HApproximation.fixedMinimalReference_centered_relIndex_general_ne_zero_and_le
        hproper hdrel
        hanchoredW
        (hBW hzeroB) (by simp [anchoredColorClass])
        (hstable i).weaklyStable hanchoredSubset hcardAnchored
        (happrox i) V he hdD heD hfoldn
        (fun z hz ↦ hWinterval z
          (hanchoredW hz))
        hnumeric hnumericV hindexLarge
    change
      (Stability.generatedSubgroup phi (insert 0 T)).relIndex
          (Stability.generatedSubgroup phi
            (anchoredColorClass (B.erase 0) c i)) ≠ 0 ∧
        (Stability.generatedSubgroup phi (insert 0 T)).relIndex
          (Stability.generatedSubgroup phi
            (anchoredColorClass (B.erase 0) c i)) ≤ indexBound at hresult
    have hTgroup : Stability.generatedSubgroup phi (insert 0 T) =
        Stability.generatedSubgroup phi T :=
      generatedSubgroup_insert_zero_eq phi T
        (Stability.centeredMinimalIdentificationFamily_zero hproper d)
    have hSgroup : Stability.generatedSubgroup phi S =
        Stability.generatedSubgroup phi (anchoredColorClass (B.erase 0) c i) :=
      generatedSubgroup_integerColorClass_eq_anchoredColorClass c i phi
        (Stability.centeredMinimalIdentificationFamily_zero hproper d)
    rw [hTgroup, ← hSgroup] at hresult
    simpa only [indexBound] using hresult.2
  have hvolume : ∀ i, 1 *
      (Preprocessing.centeredCoordinateAxisBox
        (BoundingBox.dBoundingBox W d
          (hproper.positive hdrel)).progression sourceScale).volume ≤
      volumeConstant * Greedy.positiveDyadicThreshold
        (integerColorClass (B.erase 0) c i) deletionBudget level := by
    intro i
    let S := integerColorClass (B.erase 0) c i
    have hzeroS : 0 ∉ S := by
      intro hzero
      exact Finset.notMem_erase 0 B (integerColorClass_subset (B.erase 0) c i hzero)
    have hSW : insert 0 S ⊆ W := by
      intro z hz
      rcases Finset.mem_insert.mp hz with rfl | hz
      · exact hBW hzeroB
      · exact hBW (hsourceSubset (integerColorClass_subset (B.erase 0) c i hz))
    have hinterval : ∀ z ∈ insert 0 S, 0 ≤ z ∧ z < (n : ℤ) := by
      intro z hz
      exact hWinterval z (hSW hz)
    have hv :=
      Preprocessing.HApproximation.fixedMinimalReference_dilate_volume_le_positiveDyadicThreshold
        hSW hzeroS (hstable i).weaklyStable (happrox i)
        (hproper.positive hdrel) hdD hfoldn hinterval hnumeric
        (fun T hTS hcard ↦ haccessible i (T := T) hTS hcard)
    simpa only [one_mul, Preprocessing.centeredCoordinateAxisBox_volume,
      hsourceScale, volumeConstant] using hv
  have hambient : ∀ i, Stability.generatedSubgroup phi
      (integerColorClass (B.erase 0) c i) =
        Stability.generatedSubgroup phi B := by
    intro i
    rw [generatedSubgroup_integerColorClass_eq_anchoredColorClass c i phi
      (Stability.centeredMinimalIdentificationFamily_zero hproper d)]
    exact hspan i
  apply hcertificate hproper hdrel hBW hsourceSubset hzeroB c hell hwidth
    hCell hsourceScalePos hdD hstepsPos hsteps hcross hvolume hfinite hindex
    hambient
  · simpa only [indexBound] using hsourceBound
  · simpa only [indexBound] using hsLower
  · exact hsUpper
  · exact hscaleUpper
  · exact hnoCarry

end RandomPartition

end

end Erdos186.CFP

#print axioms
  Erdos186.CFP.RandomPartition.exists_centeredScaledNonzeroGreedyCertificateConstants
