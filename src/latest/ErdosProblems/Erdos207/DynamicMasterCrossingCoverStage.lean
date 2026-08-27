/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.DynamicCrossingLink
import ErdosProblems.Erdos207.MasterIterationUpdate

/-!
# Master cover steps from dynamically chosen residual links

This is the sound state-dependent assembly theorem for the crossing-link
phase.  The old initial and internal families leave every edge of `G`
uncovered.  Consequently, coverage of `G` by the enlarged total packing can
be attributed entirely to the stage family `R ∪ L`.
-/

namespace Erdos207

open Finset

noncomputable section

/-- Dynamically choosing and covering a balanced partition of the current
residual link at every outer center gives a complete master cover step. -/
theorem exists_masterCoverStep_of_dynamic_crossingLinkExtensions
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {U : Finset V} {F : ForbiddenFamilyOn V}
    {A I D R : TripleSystemOn V}
    (hold : G ≤ leaveGraph (I ∪ D))
    (hRselected : R ⊆ A)
    (hpreDisjoint : Disjoint I (D ∪ R))
    (hprePacking : IsPackingOn (I ∪ (D ∪ R)))
    (hpreAvoid : AvoidsForbidden (I ∪ (D ∪ R)) F)
    (hstep : ∀ (P : TripleSystemOn V),
      I ∪ (D ∪ R) ⊆ P → P ⊆ (I ∪ (D ∪ R)) ∪ A →
      IsPackingOn P → AvoidsForbidden P F →
      ∀ o : {x : V // x ∉ U}, ∃ K : BipartiteLink V,
        IsResidualBipartition G P o.1 K ∧
        HasLinkCoverExtension F A P K) :
    ∃ M : TripleSystemOn V, IsMasterCoverStep F G U A I D M := by
  let P₀ := I ∪ (D ∪ R)
  obtain ⟨L, hLselected, hpreLdisjoint, hpreLpacking, hpreLavoid,
      htotalCover⟩ :=
    exists_dynamic_crossingLinkCover_outside
      (fun o : {x : V // x ∉ U} ↦ o.1) (fun o ↦ o.2)
      (fun v hv ↦ ⟨⟨v, hv⟩, rfl⟩) F A P₀ hprePacking hpreAvoid
      (by
        intro P hP₀P hPsub hPpacking hPavoid o
        exact hstep P hP₀P hPsub hPpacking hPavoid o)
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
        show T ∈ P₀
        exact mem_union_left (D ∪ R) hTI
  have hfinalPacking : IsPackingOn (I ∪ (D ∪ M)) := by
    simpa only [P₀, M, union_assoc] using hpreLpacking
  have hfinalAvoid : AvoidsForbidden (I ∪ (D ∪ M)) F := by
    simpa only [P₀, M, union_assoc] using hpreLavoid
  refine ⟨M, ?_⟩
  exact
    { selected := hMselected
      disjoint_initial := hfinalDisjoint
      packing := hfinalPacking
      avoids := hfinalAvoid
      covers_outside := by
        intro u v huv houtside
        have htotal := htotalCover u v huv houtside
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

end

end Erdos207
