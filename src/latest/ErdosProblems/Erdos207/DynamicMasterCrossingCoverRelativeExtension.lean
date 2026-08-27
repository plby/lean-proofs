/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.DynamicCrossingLinkRelativeExtension
import ErdosProblems.Erdos207.MasterIterationUpdate

/-!
# Master crossing-cover stage with a relative-extension output

This is the deterministic master-stage wrapper around the invariant-carrying
dynamic center sweep.  It both attributes all old-graph coverage to the new
stage family and rewrites the terminal extension remainder using that same
stage family.
-/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

theorem exists_masterCoverStep_of_dynamic_crossingLinkExtensions_with_relativeExtension
    {V J : Type*} [Fintype V] [Fintype J] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {U : Finset V} {F : ForbiddenFamilyOn V}
    {A I D R : TripleSystemOn V}
    (configurations : J → TripleSystemOn V)
    (sigma : ℝ≥0) (baseWeight : TripleOn V → ℝ≥0)
    (kappa : Finset {x : V // x ∉ U} → ℝ≥0)
    (hold : G ≤ leaveGraph (I ∪ D))
    (hRselected : R ⊆ A)
    (hpreDisjoint : Disjoint I (D ∪ R))
    (hprePacking : IsPackingOn (I ∪ (D ∪ R)))
    (hpreAvoid : AvoidsForbidden (I ∪ (D ∪ R)) F)
    (hinitial : HasExtensionBound
      (fun j ↦ configurations j \ (I ∪ (D ∪ R)))
      (fun T ↦ 3 * sigma + baseWeight T) (kappa ∅))
    (hstep : ∀ (S : Finset {x : V // x ∉ U})
      (P : TripleSystemOn V),
      I ∪ (D ∪ R) ⊆ P → P ⊆ (I ∪ (D ∪ R)) ∪ A →
      IsPackingOn P → AvoidsForbidden P F →
      HasExtensionBound (fun j ↦ configurations j \ P)
        (fun T ↦ centerIndexedTriangleWeight
            (fun o : {x : V // x ∉ U} ↦ o.1) (univ \ S) sigma T +
          baseWeight T)
        (kappa S) →
      ∀ o : {x : V // x ∉ U}, o ∉ S →
        ∃ K : BipartiteLink V,
          IsResidualBipartition G P o.1 K ∧
          ∃ L : TripleSystemOn V,
            L ⊆ A ∧ Disjoint P L ∧
            IsPackingOn (P ∪ L) ∧ AvoidsForbidden (P ∪ L) F ∧
            CoversBipartiteLink K L ∧
            HasExtensionBound (fun j ↦ configurations j \ (P ∪ L))
              (fun T ↦ centerIndexedTriangleWeight
                  (fun o : {x : V // x ∉ U} ↦ o.1)
                  (univ \ insert o S) sigma T + baseWeight T)
              (kappa (insert o S))) :
    ∃ M : TripleSystemOn V,
      IsMasterCoverStep F G U A I D M ∧
      HasExtensionBound
        (fun j ↦ configurations j \ (I ∪ (D ∪ M)))
        baseWeight (kappa univ) := by
  let P₀ := I ∪ (D ∪ R)
  let center : {x : V // x ∉ U} → V := fun o ↦ o.1
  obtain ⟨L, hLselected, hpreLdisjoint, hpreLpacking, hpreLavoid,
      htotalCover, hrelative⟩ :=
    exists_dynamic_crossingLinkCover_with_relativeExtension center
      Subtype.val_injective F A P₀ configurations sigma baseWeight kappa
      hprePacking hpreAvoid (by simpa only [P₀] using hinitial) (by
        intro S P hP₀P hPsub hPpacking hPavoid hInv o ho
        exact hstep S P hP₀P hPsub hPpacking hPavoid hInv o ho)
  let M := R ∪ L
  have hMselected : M ⊆ A := by
    intro T hT
    rcases mem_union.mp hT with hTR | hTL
    · exact hRselected hTR
    · exact hLselected hTL
  have hfinalDisjoint : Disjoint I (D ∪ M) := by
    rw [Finset.disjoint_left]
    intro T hTI hTDM
    rcases mem_union.mp hTDM with hTD | hTM
    · exact Finset.disjoint_left.mp hpreDisjoint hTI
        (mem_union_left R hTD)
    · rcases mem_union.mp hTM with hTR | hTL
      · exact Finset.disjoint_left.mp hpreDisjoint hTI
          (mem_union_right D hTR)
      · apply Finset.disjoint_left.mp hpreLdisjoint _ hTL
        exact mem_union_left (D ∪ R) hTI
  have hfinalPacking : IsPackingOn (I ∪ (D ∪ M)) := by
    simpa only [P₀, M, union_assoc] using hpreLpacking
  have hfinalAvoid : AvoidsForbidden (I ∪ (D ∪ M)) F := by
    simpa only [P₀, M, union_assoc] using hpreLavoid
  have hmaster : IsMasterCoverStep F G U A I D M :=
    { selected := hMselected
      disjoint_initial := hfinalDisjoint
      packing := hfinalPacking
      avoids := hfinalAvoid
      covers_outside := by
        intro u v huv houtside
        have htotal : (coveredGraph (P₀ ∪ L)).Adj u v := by
          rcases houtside with hu | hv
          · exact htotalCover ⟨u, hu⟩ v huv
          · exact (htotalCover ⟨v, hv⟩ u huv.symm).symm
        obtain ⟨T, hTtotal, huT, hvT, huvT⟩ := coveredGraph_adj.mp htotal
        have hnotOld : T ∉ I ∪ D := by
          intro hTold
          have hleave := leaveGraph_adj.mp (hold huv)
          exact hleave.2 ⟨T, hTold, huT, hvT, huvT⟩
        apply coveredGraph_adj.mpr
        refine ⟨T, ?_, huT, hvT, huvT⟩
        rcases mem_union.mp hTtotal with hTP₀ | hTL
        · change T ∈ I ∪ (D ∪ R) at hTP₀
          rcases mem_union.mp hTP₀ with hTI | hTDR
          · exact (hnotOld (mem_union_left D hTI)).elim
          · rcases mem_union.mp hTDR with hTD | hTR
            · exact (hnotOld (mem_union_right I hTD)).elim
            · exact mem_union_left L hTR
        · exact mem_union_right R hTL }
  refine ⟨M, hmaster, ?_⟩
  simpa only [P₀, M, union_assoc] using hrelative

end

end Erdos207
