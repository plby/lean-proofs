/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.IntermediateResidualLinks
import ErdosProblems.Erdos207.InternalEdgeConditionedKernel

/-!
# From an internal-greedy outcome to the simultaneous-link state

The preliminary family and the genuinely new triangles of the internal
greedy process together form the stage family `R`.  This file proves that
the support certificate of the internal kernel supplies all structural facts
needed to construct the reserve-supported residual links.
-/

namespace Erdos207

open Finset

noncomputable section

/-- The stage family after adjoining the triangles genuinely inserted by
the internal-edge greedy process. -/
def internalStageFamily
    {V : Type*} [DecidableEq V]
    (I D Mstar Q : TripleSystemOn V) : TripleSystemOn V :=
  Mstar ∪ (Q \ (I ∪ (D ∪ Mstar)))

/-- A supported internal-edge outcome produces the complete structural
input for the reserve-aware simultaneous-link kernel. -/
theorem exists_residualLinks_of_internalOutcome
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {U : Finset V}
    {reserve : Finset (Sym2 V)} {F : ForbiddenFamilyOn V}
    {A I D Mstar Q : TripleSystemOn V}
    (heven : ∀ v, Even ((neighborsIn G univ v).card))
    (hold : G <= leaveGraph (I ∪ D))
    (htri : ConsistsOfTriangles G A)
    (hstarSelected : Mstar ⊆ A)
    (hpreDisjoint : Disjoint I (D ∪ Mstar))
    (hprePacking : IsPackingOn (I ∪ (D ∪ Mstar)))
    (hreach : GreedyReachable F (I ∪ (D ∪ Mstar)) Q)
    (hQsub : Q ⊆ (I ∪ (D ∪ Mstar)) ∪ A)
    (hinternal : ∀ e ∈ internalOuterEdges G U,
      (coveredGraph Q).Adj e.out.1 e.out.2)
    (hcrossingStar :
      CoversCrossingOutsideReserve G U reserve Mstar) :
    let R := internalStageFamily I D Mstar Q
    let center := outsideVertexEmbedding U
    ∃ K : {x : V // x ∉ U} -> BipartiteLink V,
      IsIntermediateLinkState G U A I D R K ∧
      (∀ o, (K o).center = center o) ∧
      (∀ o, center o ∉ U) ∧
      (∀ o, (K o).left ⊆ U) ∧
      (∀ o, (K o).right ⊆ U) ∧
      (∀ o, (K o).SpokesIn reserve) := by
  dsimp only
  let P0 := I ∪ (D ∪ Mstar)
  let R := internalStageFamily I D Mstar Q
  have hP0Q : P0 ⊆ Q := by
    simpa only [P0] using hreach.initial_subset
  have hRQ : R ⊆ Q := by
    intro T hT
    rcases mem_union.mp hT with hTstar | hTnew
    · exact hP0Q (mem_union_right I (mem_union_right D hTstar))
    · exact (mem_sdiff.mp hTnew).1
  have hRselected : R ⊆ A := by
    intro T hT
    rcases mem_union.mp hT with hTstar | hTnew
    · exact hstarSelected hTstar
    · have hTdata := mem_sdiff.mp hTnew
      rcases mem_union.mp (hQsub hTdata.1) with hTP0 | hTA
      · exact (hTdata.2 (by simpa only [P0] using hTP0)).elim
      · exact hTA
  have hRtri : ConsistsOfTriangles G R := by
    intro T hT
    exact htri T (hRselected hT)
  have hRpacking : IsPackingOn R :=
    (hreach.isPacking hprePacking).mono hRQ
  have hRdisjoint : Disjoint I (D ∪ R) := by
    rw [disjoint_left]
    intro T hTI hTDR
    rcases mem_union.mp hTDR with hTD | hTR
    · exact disjoint_left.mp hpreDisjoint hTI (mem_union_left Mstar hTD)
    · rcases mem_union.mp hTR with hTstar | hTnew
      · exact disjoint_left.mp hpreDisjoint hTI
          (mem_union_right D hTstar)
      · exact (mem_sdiff.mp hTnew).2
          (by simpa only [P0] using
            (mem_union_left (D ∪ Mstar) hTI))
  have hinternalR : ∀ u v : V, G.Adj u v -> u ∉ U -> v ∉ U ->
      (coveredGraph R).Adj u v := by
    intro u v huv hu hv
    let e : Sym2 V := s(u, v)
    have heGraph : e ∈ graphEdges G := by
      apply mem_graphEdges_iff.mpr
      change s(u, v) ∈ G.edgeSet
      exact huv
    have heOuter : e ∈ internalOuterEdges G U := by
      apply mem_internalOuterEdges_iff.mpr
      refine ⟨heGraph, ?_, ?_⟩
      · intro heU
        have heMem := Sym2.out_fst_mem e
        simp only [e, Sym2.mem_iff] at heMem
        rcases heMem with h | h
        · exact hu (h ▸ heU)
        · exact hv (h ▸ heU)
      · intro heU
        have heMem := Sym2.out_snd_mem e
        simp only [e, Sym2.mem_iff] at heMem
        rcases heMem with h | h
        · exact hu (h ▸ heU)
        · exact hv (h ▸ heU)
    have hcoveredQ := hinternal e heOuter
    obtain ⟨T, hTQ, huT, hvT, huvT⟩ := coveredGraph_adj.mp
      (by
        have hmem : e ∈ (coveredGraph Q).edgeSet := by
          rw [← e.out_eq]
          exact hcoveredQ
        change s(u, v) ∈ (coveredGraph Q).edgeSet
        exact hmem)
    have hTR : T ∈ R := by
      by_cases hTP0 : T ∈ P0
      · rcases mem_union.mp (by simpa only [P0] using hTP0) with hTI | hTDM
        · have hleave := leaveGraph_adj.mp (hold huv)
          exact (hleave.2 ⟨T, mem_union_left D hTI, huT, hvT, huvT⟩).elim
        · rcases mem_union.mp hTDM with hTD | hTstar
          · have hleave := leaveGraph_adj.mp (hold huv)
            exact (hleave.2
              ⟨T, mem_union_right I hTD, huT, hvT, huvT⟩).elim
          · exact mem_union_left _ hTstar
      · exact mem_union_right _ (mem_sdiff.mpr
          ⟨hTQ, by simpa only [P0] using hTP0⟩)
    exact coveredGraph_adj.mpr ⟨T, hTR, huT, hvT, huvT⟩
  have hcrossingR : CoversCrossingOutsideReserve G U reserve R := by
    intro v x hv hxU hvx hnot
    obtain ⟨T, hTstar, hvT, hxT, hvxT⟩ :=
      coveredGraph_adj.mp (hcrossingStar v x hv hxU hvx hnot)
    exact coveredGraph_adj.mpr
      ⟨T, mem_union_left _ hTstar, hvT, hxT, hvxT⟩
  simpa only [R] using exists_residualLinks_masterData
    (F := F) heven hRtri hRpacking hRselected hRdisjoint hinternalR
      hcrossingR

end

end Erdos207
