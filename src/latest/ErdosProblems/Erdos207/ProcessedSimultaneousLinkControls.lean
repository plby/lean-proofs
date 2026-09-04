/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.DynamicDegreeControl
import ErdosProblems.Erdos207.SimultaneousRobustLinkCover

/-!
# Structural controls during a simultaneous link sweep

The robust matching construction processes the outside centers one at a
time.  Its intermediate family therefore contains link triples only at
centers already processed.  This file records the two consequences needed
by the deletion estimate for the next center: its spokes are still
uncovered, and its new covered degree comes only from the fixed preliminary
family.  At an inner endpoint, all additional covered edges lie in the
current stage graph.
-/

namespace Erdos207

open Finset

noncomputable section

/-- A graph degree is the instance-independent finite cardinality of its
neighbor set. -/
lemma SimpleGraph.degree_eq_neighborSet_ncard
    {V : Type*} [Fintype V] {G : SimpleGraph V}
    [DecidableRel G.Adj] (v : V) :
    G.degree v = (G.neighborSet v).ncard := by
  rw [← G.card_neighborSet_eq_degree, Set.fintypeCard_eq_ncard]

/-- Stage triangles avoid every pair already covered by the historical
packing whenever the stage graph lies in that packing's leave. -/
lemma ConsistsOfTriangles.triangleAvoids_coveredGraph_of_le_leave
    {V : Type*} [DecidableEq V]
    {G : SimpleGraph V} {A P : TripleSystemOn V}
    (htri : ConsistsOfTriangles G A) (hold : G ≤ leaveGraph P)
    {T : TripleOn V} (hTA : T ∈ A) :
    TriangleAvoidsGraph (coveredGraph P) T := by
  intro u hu v hv huv hcovered
  have huvG := htri T hTA u hu v hv huv
  exact (leaveGraph_adj.mp (hold huvG)).2 (coveredGraph_adj.mp hcovered)

/-- Any selected subfamily of a stage-triangle family covers no more edges
at a vertex than the stage graph itself. -/
lemma ConsistsOfTriangles.coveredGraph_degree_le_neighborSet_ncard
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {A R : TripleSystemOn V}
    (htri : ConsistsOfTriangles G A) (hRA : R ⊆ A) (v : V) :
    (coveredGraph R).degree v ≤ (G.neighborSet v).ncard := by
  let : DecidableRel G.Adj := Classical.decRel G.Adj
  have hcovered : coveredGraph R ≤ G := by
    intro u w huw
    obtain ⟨T, hTR, huT, hwT, huwn⟩ := coveredGraph_adj.mp huw
    exact htri T (hRA hTR) u huT w hwT huwn
  exact (SimpleGraph.degree_le_of_le hcovered).trans_eq
    (Erdos207.SimpleGraph.degree_eq_neighborSet_ncard (G := G) v)

/-- A link triple belonging to an already processed center cannot contain
the center that is about to be processed. -/
lemma IsProcessedSimultaneousLinkFamily.current_center_not_mem
    {O V : Type*} [DecidableEq O] [DecidableEq V]
    {U : Finset V} {center : O ↪ V} {K : O → BipartiteLink V}
    (hcenter : ∀ o, (K o).center = center o)
    (hout : ∀ o, center o ∉ U)
    (hleft : ∀ o, (K o).left ⊆ U)
    (hright : ∀ o, (K o).right ⊆ U)
    {S : Finset O} {M : TripleSystemOn V}
    (hprocessed : IsProcessedSimultaneousLinkFamily K S M)
    {o : O} (ho : o ∉ S) {T : TripleOn V} (hTM : T ∈ M) :
    (K o).center ∉ T.1 := by
  obtain ⟨x, hxS, rfl⟩ := hprocessed T hTM
  intro hmem
  rw [simultaneousLinkPairTriple, mem_linkMatchingTriple_iff] at hmem
  rcases hmem with hcenters | hendpoint | hendpoint
  · have hox : o = x.1 := center.injective (by
      rw [← hcenter o, ← hcenter x.1]
      exact hcenters)
    subst o
    exact ho hxS
  · apply hout o
    rw [← hcenter o, hendpoint]
    exact hleft x.1 x.2.1.2
  · apply hout o
    rw [← hcenter o, hendpoint]
    exact hright x.1 x.2.2.2

/-- At an unprocessed center, the covered degree in the part added after
`I ∪ D` is at most the degree already contributed by `R`. -/
lemma processedSimultaneousLink_center_degree_le
    {O V : Type*} [Fintype V] [DecidableEq O] [DecidableEq V]
    {U : Finset V} {center : O ↪ V} {K : O → BipartiteLink V}
    (hcenter : ∀ o, (K o).center = center o)
    (hout : ∀ o, center o ∉ U)
    (hleft : ∀ o, (K o).left ⊆ U)
    (hright : ∀ o, (K o).right ⊆ U)
    {I D R P' : TripleSystemOn V} {S : Finset O}
    (hprocessed : IsProcessedSimultaneousLinkFamily K S
      (P' \ (I ∪ (D ∪ R))))
    {o : O} (ho : o ∉ S) :
    (coveredGraph (P' \ (I ∪ D))).degree (K o).center ≤
      (coveredGraph R).degree (K o).center := by
  classical
  apply card_le_card
  intro v hv
  rw [SimpleGraph.mem_neighborFinset] at hv ⊢
  obtain ⟨T, hTnew, hcT, hvT, hcv⟩ := coveredGraph_adj.mp hv
  by_cases hTbase : T ∈ I ∪ (D ∪ R)
  · rcases mem_union.mp hTbase with hTI | hTDR
    · exact ((mem_sdiff.mp hTnew).2 (mem_union_left D hTI)).elim
    · rcases mem_union.mp hTDR with hTD | hTR
      · exact ((mem_sdiff.mp hTnew).2 (mem_union_right I hTD)).elim
      · exact coveredGraph_adj.mpr ⟨T, hTR, hcT, hvT, hcv⟩
  · have hTprocessed : T ∈ P' \ (I ∪ (D ∪ R)) :=
      mem_sdiff.mpr ⟨(mem_sdiff.mp hTnew).1, hTbase⟩
    exact (hprocessed.current_center_not_mem hcenter hout hleft hright
      ho hTprocessed hcT).elim

/-- Every edge covered after `I ∪ D` is either already covered by `R` or is
an edge of the current stage graph. -/
lemma coveredGraph_sdiff_historical_le_reserve_sup_stage
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {A I D R P' : TripleSystemOn V}
    (htri : ConsistsOfTriangles G A)
    (hPsub : P' ⊆ (I ∪ (D ∪ R)) ∪ A) :
    coveredGraph (P' \ (I ∪ D)) ≤ coveredGraph R ⊔ G := by
  intro u v huv
  obtain ⟨T, hTnew, huT, hvT, huvne⟩ := coveredGraph_adj.mp huv
  rcases mem_union.mp (hPsub (mem_sdiff.mp hTnew).1) with hTbase | hTA
  · rcases mem_union.mp hTbase with hTI | hTDR
    · exact ((mem_sdiff.mp hTnew).2 (mem_union_left D hTI)).elim
    · rcases mem_union.mp hTDR with hTD | hTR
      · exact ((mem_sdiff.mp hTnew).2 (mem_union_right I hTD)).elim
      · rw [SimpleGraph.sup_adj]
        exact Or.inl (coveredGraph_adj.mpr ⟨T, hTR, huT, hvT, huvne⟩)
  · rw [SimpleGraph.sup_adj]
    exact Or.inr (htri T hTA u huT v hvT huvne)

/-- The endpoint degree in the new part is bounded by the reserve degree
plus the stage-graph degree. -/
lemma coveredGraph_sdiff_historical_degree_le
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {A I D R P' : TripleSystemOn V}
    (htri : ConsistsOfTriangles G A)
    (hPsub : P' ⊆ (I ∪ (D ∪ R)) ∪ A) (v : V) :
    (coveredGraph (P' \ (I ∪ D))).degree v ≤
      (coveredGraph R).degree v + (G.neighborSet v).ncard := by
  let : DecidableRel G.Adj := Classical.decRel G.Adj
  calc
    (coveredGraph (P' \ (I ∪ D))).degree v ≤
        (coveredGraph R).degree v + G.degree v :=
      SimpleGraph.degree_le_add_of_le_sup
        (coveredGraph_sdiff_historical_le_reserve_sup_stage htri hPsub) v
    _ = (coveredGraph R).degree v + (G.neighborSet v).ncard := by
      rw [Erdos207.SimpleGraph.degree_eq_neighborSet_ncard (G := G) v]

/-- The residual spokes of an unprocessed center remain in the leave of
the intermediate packing. -/
lemma processedSimultaneousLink_leave_sides
    {O V : Type*} [Fintype V] [DecidableEq O] [DecidableEq V]
    {G : SimpleGraph V}
    {U : Finset V} {center : O ↪ V} {K : O → BipartiteLink V}
    (hcenter : ∀ o, (K o).center = center o)
    (hout : ∀ o, center o ∉ U)
    (hleft : ∀ o, (K o).left ⊆ U)
    (hright : ∀ o, (K o).right ⊆ U)
    {I D R P' : TripleSystemOn V} {S : Finset O}
    (hold : G ≤ leaveGraph (I ∪ D))
    (hK : ∀ o, @IsResidualBipartition V _ _ G
      (Classical.decRel G.Adj) R (center o) (K o))
    (hprocessed : IsProcessedSimultaneousLinkFamily K S
      (P' \ (I ∪ (D ∪ R))))
    {o : O} (ho : o ∉ S) :
    (∀ a : ↥(K o).left,
        (leaveGraph P').Adj (K o).center a.1) ∧
      (∀ b : ↥(K o).right,
        (leaveGraph P').Adj (K o).center b.1) := by
  classical
  let : DecidableRel G.Adj := Classical.decRel G.Adj
  have side_leave : ∀ {v : V},
      v ∈ (K o).left ∪ (K o).right →
      (leaveGraph P').Adj (K o).center v := by
    intro v hvside
    have hvres : v ∈ residualNeighbors G R (center o) := by
      rw [← (hK o).2.1]
      exact hvside
    have hvdata := mem_residualNeighbors_iff.mp hvres
    have hG : G.Adj (K o).center v := by
      simpa only [(hK o).1] using hvdata.1
    apply leaveGraph_adj.mpr
    refine ⟨hG.ne, ?_⟩
    rintro ⟨T, hTP', hcT, hvT, hcv⟩
    by_cases hTbase : T ∈ I ∪ (D ∪ R)
    · rcases mem_union.mp hTbase with hTI | hTDR
      · have hnot := (leaveGraph_adj.mp (hold hG)).2
        exact hnot ⟨T, mem_union_left D hTI, hcT, hvT, hcv⟩
      · rcases mem_union.mp hTDR with hTD | hTR
        · have hnot := (leaveGraph_adj.mp (hold hG)).2
          exact hnot ⟨T, mem_union_right I hTD, hcT, hvT, hcv⟩
        · apply hvdata.2
          simpa only [← (hK o).1] using
            (coveredGraph_adj.mpr ⟨T, hTR, hcT, hvT, hcv⟩)
    · have hTprocessed : T ∈ P' \ (I ∪ (D ∪ R)) :=
        mem_sdiff.mpr ⟨hTP', hTbase⟩
      exact (hprocessed.current_center_not_mem hcenter hout hleft hright
        ho hTprocessed hcT).elim
  constructor
  · intro a
    exact side_leave (mem_union_left (K o).right a.2)
  · intro b
    exact side_leave (mem_union_right (K o).left b.2)

/-- Fixed reserve/stage degree budgets discharge all dynamic deletion
controls at the next unprocessed center. -/
theorem processedSimultaneousLink_stateControls
    {O V : Type*} [Fintype V] [DecidableEq O] [DecidableEq V]
    {G : SimpleGraph V}
    {U : Finset V} {center : O ↪ V} {K : O → BipartiteLink V}
    (hcenter : ∀ o, (K o).center = center o)
    (hout : ∀ o, center o ∉ U)
    (hleft : ∀ o, (K o).left ⊆ U)
    (hright : ∀ o, (K o).right ⊆ U)
    {A I D R P' : TripleSystemOn V} {S : Finset O}
    (htri : ConsistsOfTriangles G A)
    (hold : G ≤ leaveGraph (I ∪ D))
    (hK : ∀ o, @IsResidualBipartition V _ _ G
      (Classical.decRel G.Adj) R (center o) (K o))
    (hPsub : P' ⊆ (I ∪ (D ∪ R)) ∪ A)
    (hprocessed : IsProcessedSimultaneousLinkFamily K S
      (P' \ (I ∪ (D ∪ R))))
    {degreeCutoff : ℕ}
    (hbudgetLeft : ∀ o (a : ↥(K o).left),
      (coveredGraph R).degree a.1 +
        (G.neighborSet a.1).ncard ≤ degreeCutoff)
    (hbudgetRight : ∀ o (b : ↥(K o).right),
      (coveredGraph R).degree b.1 +
        (G.neighborSet b.1).ncard ≤ degreeCutoff)
    {o : O} (ho : o ∉ S) :
    (∀ a : ↥(K o).left, (leaveGraph P').Adj (K o).center a.1) ∧
      (∀ b : ↥(K o).right, (leaveGraph P').Adj (K o).center b.1) ∧
      (∀ a : ↥(K o).left,
        (coveredGraph (P' \ (I ∪ D))).degree a.1 ≤ degreeCutoff) ∧
      (∀ b : ↥(K o).right,
        (coveredGraph (P' \ (I ∪ D))).degree b.1 ≤ degreeCutoff) := by
  have hleave := processedSimultaneousLink_leave_sides hcenter hout hleft
    hright hold hK hprocessed ho
  refine ⟨hleave.1, hleave.2, ?_, ?_⟩
  · intro a
    exact (coveredGraph_sdiff_historical_degree_le htri hPsub a.1).trans
      (hbudgetLeft o a)
  · intro b
    exact (coveredGraph_sdiff_historical_degree_le htri hPsub b.1).trans
      (hbudgetRight o b)

end

end Erdos207
