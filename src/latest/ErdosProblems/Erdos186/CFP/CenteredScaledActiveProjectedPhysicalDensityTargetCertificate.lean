/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.CFP.CenteredScaledActiveProjectedPhysicalTargetCertificate
import ErdosProblems.Erdos186.CFP.CenteredScaledActivePhysicalDensityTargetCertificate

/-! # Physical density supplies completion before projected properization -/

namespace Erdos186.CFP

noncomputable section

namespace RandomPartition

/-- The active-coordinate physical-density target wrapper with the final
source map handled by generic projected properization. -/
theorem exists_centeredScaledActiveProjectedPhysicalDensityTargetCertificateConstants
    (d : ℕ) (hd : 0 < d) (cNum cDen : ℕ)
    (hcNum : 0 < cNum) (hc : cNum ≤ cDen) :
    ∃ corWidth denseConstant denseEll denseWidth : ℕ,
      0 < denseConstant ∧
      ∀ {W B A : Finset ℤ}
        (P : BoundingBox.BoundingGAP W d)
        (hPproper : P.progression.Proper)
        (hPnondegenerate : P.progression.Nondegenerate)
        (hBW : B ⊆ W) (hAB : A ⊆ B)
        (hzeroW : 0 ∈ W) (hzeroB : 0 ∈ B),
        ∀ {q cap target sourceScale s D block : ℕ}
          (c : {a // a ∈ A} → Fin (q + 1))
          (run : ∀ i, Greedy.PhysicalTargetRun
            (integerColorClass A c i) cap target),
          denseEll ≤ q + 1 →
          max corWidth denseWidth ≤ sourceScale →
          denseConstant ≤ q + 1 →
          0 < sourceScale → 0 < block → d ≤ D →
          (∀ i, Stability.generatedSubgroup
              (Preprocessing.centeredIdentification P hPproper hzeroW)
              (integerColorClass A c i) =
            Stability.generatedSubgroup
              (Preprocessing.centeredIdentification P hPproper hzeroW) B) →
          (∀ i, (run i).steps + cDen ≤ sourceScale) →
          cNum *
              (Preprocessing.centeredCoordinateAxisBox
                P.progression sourceScale).volume ≤
            cDen * target →
          (q + 1) * sourceScale ≤ s →
          s ≤ 2 * block * (q + 1) * sourceScale →
          sourceScale * ((q + 1) / denseConstant) ≤ s →
          ProjectedProperization.projectionFactor D ≤
            sourceScale * ((q + 1) / denseConstant) →
          ∃ k : ℕ, Nonempty (FixedScaleWitness
            (Stability.integerPoints B) s D k 0 1
            ((4 * denseConstant * block) *
              ProjectedProperization.projectionFactor D)) := by
  obtain ⟨corWidth, denseConstant, denseEll, denseWidth,
      hdenseConstant, hcertificate⟩ :=
    exists_centeredScaledActiveProjectedPhysicalTargetCertificateConstants
      d hd cNum cDen hcNum hc
  refine ⟨corWidth, denseConstant, denseEll, denseWidth,
    hdenseConstant, ?_⟩
  intro W B A P hPproper hPnondegenerate hBW hAB hzeroW hzeroB q cap
    target sourceScale s D block c run hell hwidthScale hCell hsourceScale hblock hdD
    hambient hsourceBound htarget hreserveLower hsUpper hscaleUpper hprojection
  let phi := Preprocessing.centeredIdentification P hPproper hzeroW
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
        (P.progression.dilate (2 * sourceScale)).volume ≤
          cDen * (Greedy.subsetSums (selected i)).card := by
      rw [← Preprocessing.centeredCoordinateAxisBox_volume]
      calc
        (Preprocessing.centeredCoordinateAxisBox
            P.progression sourceScale).volume ≤
            cNum * (Preprocessing.centeredCoordinateAxisBox
              P.progression sourceScale).volume :=
          Nat.le_mul_of_pos_left _ hcNum
        _ ≤ cDen * target := htarget
        _ ≤ cDen * (Greedy.subsetSums (selected i)).card :=
          Nat.mul_le_mul_left cDen (run i).target_le_subsetSums
    have hresult :=
      Preprocessing.centeredPhysicalDensity_relIndex_ne_zero_and_le_boundingGAP
        P hPproper hSW hzeroW (Finset.mem_insert_self 0 S)
        hselectedS hselectedCard hcDenScale hdensity
    change
      (Stability.generatedSubgroup phi (selected i)).relIndex
            (Stability.generatedSubgroup phi (insert 0 S)) ≠ 0 ∧
        (Stability.generatedSubgroup phi (selected i)).relIndex
            (Stability.generatedSubgroup phi (insert 0 S)) ≤ cDen at hresult
    have hphiZero : phi 0 = 0 :=
      Preprocessing.centeredIdentification_zero P hPproper hzeroW
    have hgen : Stability.generatedSubgroup phi (insert 0 S) =
        Stability.generatedSubgroup phi S :=
      generatedSubgroup_insert_zero_eq phi S hphiZero
    rw [hgen] at hresult
    simpa only [S] using hresult
  apply hcertificate P hPproper hPnondegenerate hBW hAB hzeroW hzeroB
    c run hell hwidthScale hCell hsourceScale hblock hdD
    (fun i ↦ (hindexPair i).1) (fun i ↦ (hindexPair i).2)
    hambient hsourceBound htarget hreserveLower hsUpper hscaleUpper hprojection

end RandomPartition

end

end Erdos186.CFP

#print axioms
  Erdos186.CFP.RandomPartition.exists_centeredScaledActiveProjectedPhysicalDensityTargetCertificateConstants
