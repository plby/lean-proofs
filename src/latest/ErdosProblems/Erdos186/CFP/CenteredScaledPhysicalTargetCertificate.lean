/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.CFP.CenteredScaledPhysicalReserveCertificate
import ErdosProblems.Erdos186.CFP.GreedyPhysicalTarget

/-!
# Varying-run physical targets give the centered scaled certificate

Each color has its own canonical physical-target greedy run.  The run
lengths may differ.  Generator completion is then performed independently
inside each original color class and transported through one global centered
coordinate map.
-/

namespace Erdos186.CFP

open scoped BigOperators

noncomputable section

namespace RandomPartition

/-- The finite source-shaped endpoint after the per-color approximation
arguments have established one common physical subset-sum target. -/
theorem exists_centeredScaledPhysicalTargetCertificateConstants
    (d : ℕ) (hd : 0 < d) (cNum cDen : ℕ)
    (hcNum : 0 < cNum) (hc : cNum ≤ cDen) :
    ∃ corConstant corWidth denseConstant denseEll denseWidth : ℕ,
      0 < corConstant ∧ 0 < denseConstant ∧
      ∀ {W B A : Finset ℤ} {relevant : Finset ℕ}
        (hproper : Stability.RelevantBoxesProper W relevant),
        (hdrel : d ∈ relevant) → B ⊆ W → A ⊆ B → 0 ∈ B →
        ∀ {q cap target sourceScale s D K : ℕ}
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
          (∀ i,
            (Stability.generatedSubgroup
                (Stability.centeredMinimalIdentificationFamily hproper d)
                (Greedy.selected (integerColorClass A c i) (run i).steps)).relIndex
              (Stability.generatedSubgroup
                (Stability.centeredMinimalIdentificationFamily hproper d)
                (integerColorClass A c i)) ≠ 0) →
          (∀ i,
            (Stability.generatedSubgroup
                (Stability.centeredMinimalIdentificationFamily hproper d)
                (Greedy.selected (integerColorClass A c i) (run i).steps)).relIndex
              (Stability.generatedSubgroup
                (Stability.centeredMinimalIdentificationFamily hproper d)
                (integerColorClass A c i)) ≤ K) →
          (∀ i, Stability.generatedSubgroup
              (Stability.centeredMinimalIdentificationFamily hproper d)
              (integerColorClass A c i) =
            Stability.generatedSubgroup
              (Stability.centeredMinimalIdentificationFamily hproper d) B) →
          (∀ i, (run i).steps + K ≤ sourceScale) →
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
    exists_centeredScaledPhysicalReserveCertificateConstants
      d hd cNum cDen hcNum hc
  refine ⟨corConstant, corWidth, denseConstant, denseEll, denseWidth,
    hcorConstant, hdenseConstant, ?_⟩
  intro W B A relevant hproper hdrel hBW hAB hzeroB q cap target sourceScale
    s D K c run hell hwidth hCell hsourceScale hdD hfinite hindex hambient
    hsourceBound htarget hreserveLower hsUpper hscaleUpper hnoCarry
  let phi := Stability.centeredMinimalIdentificationFamily hproper d
  let Gamma := Stability.generatedSubgroup phi B
  let selected : Fin (q + 1) → Finset ℤ := fun i ↦
    Greedy.selected (integerColorClass A c i) (run i).steps
  have hexists : ∀ i : Fin (q + 1), ∃ T : Finset ℤ,
      T ⊆ integerColorClass A c i \ selected i ∧
      Disjoint (selected i) T ∧ T.card ≤ K ∧
      Stability.generatedSubgroup phi (selected i ∪ T) = Gamma := by
    intro i
    obtain ⟨T, hTsub, hTdisjoint, hTcard, hTgen⟩ :=
      exists_bounded_generatorCompletion phi
        (Greedy.selected_subset (integerColorClass A c i) (run i).steps)
        (hfinite i)
    refine ⟨T, hTsub, hTdisjoint, hTcard.trans (hindex i), ?_⟩
    exact hTgen.trans (hambient i)
  choose completion hcompletion using hexists
  let completed : Fin (q + 1) → Finset ℤ := fun i ↦
    selected i ∪ completion i
  have hselected : ∀ i, selected i ⊆ completed i := fun i ↦
    Finset.subset_union_left
  have hcompletedCard : ∀ i, (completed i).card ≤ sourceScale := by
    intro i
    change (selected i ∪ completion i).card ≤ sourceScale
    rw [Finset.card_union_of_disjoint (hcompletion i).2.1]
    change (Greedy.selected (integerColorClass A c i) (run i).steps).card +
      (completion i).card ≤ sourceScale
    rw [(run i).selected_card]
    exact Nat.add_le_add_left (hcompletion i).2.2.1 (run i).steps |>.trans
      (hsourceBound i)
  have hcompletedSubset : ∀ i, completed i ⊆ B := by
    intro i z hz
    apply hAB
    apply integerColorClass_subset A c i
    rcases Finset.mem_union.mp hz with hzSelected | hzCompletion
    · exact Greedy.selected_subset _ _ hzSelected
    · exact (Finset.mem_sdiff.mp ((hcompletion i).1 hzCompletion)).1
  have hphysicalDensity : ∀ i, cNum *
        (Preprocessing.centeredCoordinateAxisBox
          (BoundingBox.dBoundingBox W d
            (hproper.positive hdrel)).progression sourceScale).volume ≤
      cDen * (Greedy.subsetSums (selected i)).card := by
    intro i
    exact htarget.trans (Nat.mul_le_mul_left cDen (run i).target_le_subsetSums)
  have hgenerated : ∀ i, generatedSublattice
        ((completed i).image phi) =
      Stability.generatedSubgroup phi B := by
    intro i
    rw [generatedSublattice_image_eq_generatedSubgroup]
    exact (hcompletion i).2.2.2
  have hcompletedDisjoint : (Set.univ : Set (Fin (q + 1))).PairwiseDisjoint
      completed := by
    intro i _hi j _hj hij
    change Disjoint (completed i) (completed j)
    rw [Finset.disjoint_left]
    intro z hzi hzj
    have hzi' : z ∈ integerColorClass A c i := by
      rcases Finset.mem_union.mp hzi with hzSelected | hzCompletion
      · exact Greedy.selected_subset _ _ hzSelected
      · exact (Finset.mem_sdiff.mp ((hcompletion i).1 hzCompletion)).1
    have hzj' : z ∈ integerColorClass A c j := by
      rcases Finset.mem_union.mp hzj with hzSelected | hzCompletion
      · exact Greedy.selected_subset _ _ hzSelected
      · exact (Finset.mem_sdiff.mp ((hcompletion j).1 hzCompletion)).1
    exact Finset.disjoint_left.mp (integerColorClass_disjoint A c hij) hzi' hzj'
  have hreserveDisjoint : (Set.univ : Set (Fin (q + 1))).PairwiseDisjoint
      (fun i ↦ Stability.integerPoints (completed i)) := by
    intro i hi j hj hij
    change Disjoint (Stability.integerPoints (completed i))
      (Stability.integerPoints (completed j))
    rw [Finset.disjoint_left]
    intro x hxi hxj
    obtain ⟨a, hai, hax⟩ := Stability.mem_integerPoints_iff.mp hxi
    obtain ⟨b, hbj, hbx⟩ := Stability.mem_integerPoints_iff.mp hxj
    have hab : a = b := by
      apply Stability.integerPoint_injective
      exact hax.trans hbx.symm
    subst b
    exact Finset.disjoint_left.mp (hcompletedDisjoint hi hj hij) hai hbj
  have hreserveSmall :
      (∑ i, (Stability.integerPoints (completed i)).card) ≤ s := by
    calc
      (∑ i, (Stability.integerPoints (completed i)).card) =
          ∑ i, (completed i).card := by simp
      _ ≤ ∑ _i : Fin (q + 1), sourceScale :=
        Finset.sum_le_sum fun i _hi ↦ hcompletedCard i
      _ = (q + 1) * sourceScale := by simp
      _ ≤ s := hreserveLower
  exact hcertificate hproper hdrel hBW hzeroB selected completed hell hwidth
    hCell hsourceScale hdD hselected hcompletedCard hcompletedSubset
    hphysicalDensity hgenerated hreserveDisjoint hreserveSmall hsUpper
    hscaleUpper hnoCarry

end RandomPartition

end

end Erdos186.CFP

#print axioms
  Erdos186.CFP.RandomPartition.exists_centeredScaledPhysicalTargetCertificateConstants
