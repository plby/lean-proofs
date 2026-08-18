/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.CFP.CenteredPhysicalIndex
import ErdosProblems.Erdos186.CFP.CenteredScaledPhysicalTargetCertificate

/-!
# Physical density supplies the generator-completion index

The common physical target already makes every selected subset-sum set
dense in the final centered coordinate box.  The quotient-packing estimate
therefore bounds the selected subgroup's index in its colour subgroup by
the same denominator.  This removes the last per-colour approximation input
from the varying-run scaled certificate.
-/

namespace Erdos186.CFP

open scoped BigOperators

noncomputable section

namespace RandomPartition

/-- Source-shaped varying-run certificate in which the relative-index
hypotheses are consequences of the common physical density estimate. -/
theorem exists_centeredScaledPhysicalDensityTargetCertificateConstants
    (d : ℕ) (hd : 0 < d) (cNum cDen : ℕ)
    (hcNum : 0 < cNum) (hc : cNum ≤ cDen) :
    ∃ corConstant corWidth denseConstant denseEll denseWidth : ℕ,
      0 < corConstant ∧ 0 < denseConstant ∧
      ∀ {W B A : Finset ℤ} {relevant : Finset ℕ}
        (hproper : Stability.RelevantBoxesProper W relevant),
        (hdrel : d ∈ relevant) → B ⊆ W → A ⊆ B → 0 ∈ B →
        ∀ {q cap target sourceScale s D : ℕ}
          (c : {a // a ∈ A} → Fin (q + 1))
          (run : ∀ i, Greedy.PhysicalTargetRun
            (integerColorClass A c i) cap target),
          denseEll ≤ q + 1 →
          max corWidth denseWidth ≤
            (Preprocessing.centeredCoordinateAxisBox
              (BoundingBox.dBoundingBox W d
                (hproper.positive hdrel)).progression
              sourceScale).minWidth →
          denseConstant ≤ q + 1 →
          0 < sourceScale → d ≤ D →
          (∀ i, Stability.generatedSubgroup
              (Stability.centeredMinimalIdentificationFamily hproper d)
              (integerColorClass A c i) =
            Stability.generatedSubgroup
              (Stability.centeredMinimalIdentificationFamily hproper d) B) →
          (∀ i, (run i).steps + cDen ≤ sourceScale) →
          cNum *
              (Preprocessing.centeredCoordinateAxisBox
                (BoundingBox.dBoundingBox W d
                  (hproper.positive hdrel)).progression
                sourceScale).volume ≤
            cDen * target →
          (q + 1) * sourceScale ≤ s →
          s ≤ 2 * (q + 1) * sourceScale →
          sourceScale * ((q + 1) / denseConstant) ≤ s →
          (((BoundingBox.dBoundingBox W d
              (hproper.positive hdrel)).progression).dilate
            (((q + 1) / denseConstant) * corConstant *
              (2 * sourceScale))).Proper →
          Nonempty (PreprocessedReserveCertificate B s D 0 1
            (4 * denseConstant)) := by
  obtain ⟨corConstant, corWidth, denseConstant, denseEll, denseWidth,
      hcorConstant, hdenseConstant, hcertificate⟩ :=
    exists_centeredScaledPhysicalTargetCertificateConstants
      d hd cNum cDen hcNum hc
  refine ⟨corConstant, corWidth, denseConstant, denseEll, denseWidth,
    hcorConstant, hdenseConstant, ?_⟩
  intro W B A relevant hproper hdrel hBW hAB hzeroB q cap target sourceScale
    s D c run hell hwidth hCell hsourceScale hdD hambient hsourceBound
    htarget hreserveLower hsUpper hscaleUpper hnoCarry
  let phi := Stability.centeredMinimalIdentificationFamily hproper d
  let selected : Fin (q + 1) → Finset ℤ := fun i ↦
    Greedy.selected (integerColorClass A c i) (run i).steps
  have hindexPair : ∀ i,
      (Stability.generatedSubgroup phi (selected i)).relIndex
          (Stability.generatedSubgroup phi
            (integerColorClass A c i)) ≠ 0 ∧
        (Stability.generatedSubgroup phi (selected i)).relIndex
          (Stability.generatedSubgroup phi
            (integerColorClass A c i)) ≤ cDen := by
    intro i
    let S := integerColorClass A c i
    have hSW : insert 0 S ⊆ W := by
      exact Finset.insert_subset (hBW hzeroB)
        ((integerColorClass_subset A c i).trans (hAB.trans hBW))
    have hselectedS : selected i ⊆ insert 0 S := by
      exact (Greedy.selected_subset S (run i).steps).trans
        (Finset.subset_insert 0 S)
    have hselectedCard : (selected i).card ≤ sourceScale := by
      rw [show (selected i).card = (run i).steps by
        exact (run i).selected_card]
      exact (Nat.le_add_right (run i).steps cDen).trans (hsourceBound i)
    have hcDenScale : cDen ≤ sourceScale := by
      exact (Nat.le_add_left cDen (run i).steps).trans (hsourceBound i)
    have hdensity :
        (((BoundingBox.dBoundingBox W d
          (hproper.positive hdrel)).progression).dilate
            (2 * sourceScale)).volume ≤
          cDen * (Greedy.subsetSums (selected i)).card := by
      rw [← Preprocessing.centeredCoordinateAxisBox_volume]
      calc
        (Preprocessing.centeredCoordinateAxisBox
            (BoundingBox.dBoundingBox W d
              (hproper.positive hdrel)).progression sourceScale).volume ≤
            cNum *
              (Preprocessing.centeredCoordinateAxisBox
                (BoundingBox.dBoundingBox W d
                  (hproper.positive hdrel)).progression sourceScale).volume :=
          Nat.le_mul_of_pos_left _ hcNum
        _ ≤ cDen * target := htarget
        _ ≤ cDen * (Greedy.subsetSums (selected i)).card :=
          Nat.mul_le_mul_left cDen (run i).target_le_subsetSums
    have hresult :=
      Preprocessing.centeredPhysicalDensity_relIndex_ne_zero_and_le
        hproper hdrel hSW (hBW hzeroB) (Finset.mem_insert_self 0 S)
        hselectedS hselectedCard hcDenScale hdensity
    change
      (Stability.generatedSubgroup phi (selected i)).relIndex
            (Stability.generatedSubgroup phi (insert 0 S)) ≠ 0 ∧
        (Stability.generatedSubgroup phi (selected i)).relIndex
            (Stability.generatedSubgroup phi (insert 0 S)) ≤ cDen at hresult
    have hphiZero : phi 0 = 0 :=
      Stability.centeredMinimalIdentificationFamily_zero hproper d
    have hgen : Stability.generatedSubgroup phi (insert 0 S) =
        Stability.generatedSubgroup phi S :=
      generatedSubgroup_insert_zero_eq phi S hphiZero
    rw [hgen] at hresult
    simpa only [S] using hresult
  apply hcertificate hproper hdrel hBW hAB hzeroB c run hell hwidth hCell
    hsourceScale hdD (fun i ↦ (hindexPair i).1)
    (fun i ↦ (hindexPair i).2) hambient hsourceBound htarget
    hreserveLower hsUpper hscaleUpper hnoCarry

end RandomPartition

end

end Erdos186.CFP

#print axioms
  Erdos186.CFP.RandomPartition.exists_centeredScaledPhysicalDensityTargetCertificateConstants
