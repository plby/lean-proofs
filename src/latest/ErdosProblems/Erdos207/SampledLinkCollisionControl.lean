/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.SimultaneousLinkCollision
import ErdosProblems.Erdos207.ProcessedSimultaneousLinkControls

/-! # Every dynamic sampled pair-conflict is an actual two-bit collision -/

namespace Erdos207

open Finset
open scoped Classical NNReal

noncomputable section

theorem simultaneousLinkInnerEdge_eq_of_mem_ne_center
    {O V : Type*} [DecidableEq V] (K : O → BipartiteLink V)
    (x : SimultaneousLinkPair O V K) {u v : V}
    (hu : u ∈ (simultaneousLinkPairTriple K x).1)
    (hv : v ∈ (simultaneousLinkPairTriple K x).1)
    (huc : u ≠ (K x.1).center) (hvc : v ≠ (K x.1).center) (huv : u ≠ v) :
    s(u, v) = simultaneousLinkInnerEdge K x := by
  rw [simultaneousLinkPairTriple, mem_linkMatchingTriple_iff] at hu hv
  rcases hu.resolve_left huc with hu | hu <;>
    rcases hv.resolve_left hvc with hv | hv
  · exact (huv (hu.trans hv.symm)).elim
  · simp only [hu, hv, simultaneousLinkInnerEdge]
  · simp only [hu, hv, simultaneousLinkInnerEdge, Sym2.eq_swap]
  · exact (huv (hu.trans hv.symm)).elim

theorem simultaneousLinkReservoir_mem_coordinate_iff
    {O V : Type*} [Fintype O] [DecidableEq O] [Fintype V] [DecidableEq V]
    (U : Finset V) (center : O ↪ V) (K : O → BipartiteLink V)
    (hcenter : ∀ o, (K o).center = center o) (hout : ∀ o, center o ∉ U)
    (hleft : ∀ o, (K o).left ⊆ U) (hright : ∀ o, (K o).right ⊆ U)
    (omega : SimultaneousLinkPair O V K → Bool) (x : SimultaneousLinkPair O V K) :
    simultaneousLinkPairTriple K x ∈
      simultaneousLinkReservoir U center K hcenter hout hleft hright omega ↔ omega x = true := by
  change (simultaneousLinkPairEmbedding U center K hcenter hout hleft hright) x ∈
    (FiniteLaw.selectedByBits omega).map (simultaneousLinkPairEmbedding U center K hcenter hout hleft hright) ↔ _
  rw [mem_map']
  exact FiniteLaw.mem_selectedByBits_iff

theorem sampled_link_pair_conflict_witness
    {O V : Type*} [Fintype O] [DecidableEq O] [Fintype V] [DecidableEq V]
    (U : Finset V) (center : O ↪ V) (K : O → BipartiteLink V)
    (hcenter : ∀ o, (K o).center = center o) (hout : ∀ o, center o ∉ U)
    (hleft : ∀ o, (K o).left ⊆ U) (hright : ∀ o, (K o).right ⊆ U)
    (r : ∀ o, ↥(K o).left → ↥(K o).right → Prop)
    (omega : SimultaneousLinkPair O V K → Bool) (P P' : TripleSystemOn V) (S : Finset O)
    (hsub : P' ⊆ P ∪ simultaneousLinkReservoir U center K hcenter hout hleft hright
      (candidateFilteredLinkBits K r omega))
    (hprocessed : IsProcessedSimultaneousLinkFamily K S (P' \ P))
    (x : SimultaneousLinkPair O V K) (hxS : x.1 ∉ S)
    (hsafe : TriangleAvoidsGraph (coveredGraph P) (simultaneousLinkPairTriple K x))
    (hconflict : ¬ TriangleAvoidsGraph (coveredGraph P') (simultaneousLinkPairTriple K x)) :
    ∃ y ∈ otherLinkCoordinates K r x, omega y = true := by
  unfold TriangleAvoidsGraph at hconflict
  push Not at hconflict
  obtain ⟨u, hu, v, hv, huv, hcovered⟩ := hconflict
  obtain ⟨T, hTP', huT, hvT, _⟩ := coveredGraph_adj.mp hcovered
  have hTP : T ∉ P := by
    intro hTP
    exact hsafe u hu v hv huv (coveredGraph_adj.mpr ⟨T, hTP, huT, hvT, huv⟩)
  have hnew : T ∈ P' \ P := mem_sdiff.mpr ⟨hTP', hTP⟩
  have hcT := hprocessed.current_center_not_mem hcenter hout hleft hright hxS hnew
  have huc : u ≠ (K x.1).center := fun heq ↦ hcT (heq ▸ huT)
  have hvc : v ≠ (K x.1).center := fun heq ↦ hcT (heq ▸ hvT)
  have hinner {z : V} (hz : z ∈ (simultaneousLinkPairTriple K x).1)
      (hzc : z ≠ (K x.1).center) : z ∈ U := by
    rw [simultaneousLinkPairTriple, mem_linkMatchingTriple_iff] at hz
    rcases hz.resolve_left hzc with hz | hz
    · rw [hz]
      exact hleft x.1 x.2.1.2
    · rw [hz]
      exact hright x.1 x.2.2.2
  have huU := hinner hu huc
  have hvU := hinner hv hvc
  obtain ⟨y, hyS, rfl⟩ := hprocessed T hnew
  have hyres := (mem_union.mp (hsub hTP')).resolve_left hTP
  have hybit := (simultaneousLinkReservoir_mem_coordinate_iff U center K hcenter hout hleft hright
    (candidateFilteredLinkBits K r omega) y).mp hyres
  have hyr := (candidateFilteredLinkBits_true_iff K r omega y).mp hybit
  refine ⟨y, mem_filter.mpr ⟨mem_univ y, ?_, hyr.1, ?_⟩, hyr.2⟩
  · intro hyx
    exact hxS (hyx ▸ hyS)
  · have huy : u ≠ (K y.1).center := by
      intro heq
      exact hout y.1 (by simpa only [heq, hcenter y.1] using huU)
    have hvy : v ≠ (K y.1).center := by
      intro heq
      exact hout y.1 (by simpa only [heq, hcenter y.1] using hvU)
    exact (simultaneousLinkInnerEdge_eq_of_mem_ne_center K y huT hvT huy hvy huv).symm.trans
      (simultaneousLinkInnerEdge_eq_of_mem_ne_center K x hu hv huc hvc huv)

theorem sampled_pair_conflict_left_subset_collisions
    {O V : Type*} [Fintype O] [DecidableEq O] [Fintype V] [DecidableEq V]
    (U : Finset V) (center : O ↪ V) (K : O → BipartiteLink V)
    (hcenter : ∀ o, (K o).center = center o) (hout : ∀ o, center o ∉ U)
    (hleft : ∀ o, (K o).left ⊆ U) (hright : ∀ o, (K o).right ⊆ U)
    (r : ∀ o, ↥(K o).left → ↥(K o).right → Prop) [∀ o, DecidableRel (r o)]
    (omega : SimultaneousLinkPair O V K → Bool) (P P' : TripleSystemOn V) (S : Finset O)
    (hsub : P' ⊆ P ∪ simultaneousLinkReservoir U center K hcenter hout hleft hright
      (candidateFilteredLinkBits K r omega))
    (hprocessed : IsProcessedSimultaneousLinkFamily K S (P' \ P))
    (hsafe : ∀ o a b, r o a b → TriangleAvoidsGraph (coveredGraph P) (simultaneousLinkPairTriple K ⟨o, (a,b)⟩))
    (o : O) (ho : o ∉ S) (a : ↥(K o).left) :
    bipartiteLinkRelevantPairConflictNeighbors
      (fun a b ↦ (a,b) ∈ sampledCandidatePairs (r o) (simultaneousLinkSelectedPairs K omega o)) P' a ⊆
      sampledLinkCollisions K r (fun b ↦ ⟨o, (a,b)⟩) (univ.filter (r o a)) omega := by
  intro b hb
  have hb' : (a,b) ∈ sampledCandidatePairs (r o) (simultaneousLinkSelectedPairs K omega o) ∧
      ¬ TriangleAvoidsGraph (coveredGraph P') (simultaneousLinkPairTriple K ⟨o,(a,b)⟩) := by
    simpa only [bipartiteLinkRelevantPairConflictNeighbors, mem_filter, mem_univ,
      true_and, simultaneousLinkPairTriple] using hb
  have hsample := mem_filter.mp hb'.1
  apply mem_filter.mpr
  refine ⟨mem_filter.mpr ⟨mem_univ b, hsample.2⟩,
    mem_simultaneousLinkSelectedPairs_iff.mp hsample.1, ?_⟩
  exact sampled_link_pair_conflict_witness U center K hcenter hout hleft hright r omega P P' S
    hsub hprocessed ⟨o, (a,b)⟩ ho (hsafe o a b hsample.2) hb'.2

theorem sampled_pair_conflict_right_subset_collisions
    {O V : Type*} [Fintype O] [DecidableEq O] [Fintype V] [DecidableEq V]
    (U : Finset V) (center : O ↪ V) (K : O → BipartiteLink V)
    (hcenter : ∀ o, (K o).center = center o) (hout : ∀ o, center o ∉ U)
    (hleft : ∀ o, (K o).left ⊆ U) (hright : ∀ o, (K o).right ⊆ U)
    (r : ∀ o, ↥(K o).left → ↥(K o).right → Prop) [∀ o, DecidableRel (r o)]
    (omega : SimultaneousLinkPair O V K → Bool) (P P' : TripleSystemOn V) (S : Finset O)
    (hsub : P' ⊆ P ∪ simultaneousLinkReservoir U center K hcenter hout hleft hright
      (candidateFilteredLinkBits K r omega))
    (hprocessed : IsProcessedSimultaneousLinkFamily K S (P' \ P))
    (hsafe : ∀ o a b, r o a b → TriangleAvoidsGraph (coveredGraph P) (simultaneousLinkPairTriple K ⟨o, (a,b)⟩))
    (o : O) (ho : o ∉ S) (b : ↥(K o).right) :
    bipartiteLinkRelevantRightPairConflictNeighbors
      (fun a b ↦ (a,b) ∈ sampledCandidatePairs (r o) (simultaneousLinkSelectedPairs K omega o)) P' b ⊆
      sampledLinkCollisions K r (fun a ↦ ⟨o, (a,b)⟩) (univ.filter (fun a ↦ r o a b)) omega := by
  intro a ha
  have ha' : (a,b) ∈ sampledCandidatePairs (r o) (simultaneousLinkSelectedPairs K omega o) ∧
      ¬ TriangleAvoidsGraph (coveredGraph P') (simultaneousLinkPairTriple K ⟨o,(a,b)⟩) := by
    simpa only [bipartiteLinkRelevantRightPairConflictNeighbors, mem_filter, mem_univ,
      true_and, simultaneousLinkPairTriple] using ha
  have hsample := mem_filter.mp ha'.1
  apply mem_filter.mpr
  refine ⟨mem_filter.mpr ⟨mem_univ a, hsample.2⟩,
    mem_simultaneousLinkSelectedPairs_iff.mp hsample.1, ?_⟩
  exact sampled_link_pair_conflict_witness U center K hcenter hout hleft hright r omega P P' S
    hsub hprocessed ⟨o, (a,b)⟩ ho (hsafe o a b hsample.2) ha'.2

end

end Erdos207
