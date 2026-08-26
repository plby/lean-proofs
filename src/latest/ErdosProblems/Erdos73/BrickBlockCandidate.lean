import ErdosProblems.Erdos73.BrickColumnBlocks
import ErdosProblems.Erdos73.StripSelectionState
import ErdosProblems.Erdos73.ExactEdgeExtension

/-! A selected segment gives a breaking block path supported in its own strips and segment. -/

namespace Erdos73
noncomputable section
open scoped Classical

open SimpleGraph Finset Erdos73Infrastructure.SimpleGraph

variable {V : Type*} [Fintype V] {G : SimpleGraph V} {c r m : ℕ}
variable {S : GraphSubdivisionModel (elementaryWall c r) G}
variable {P : Fin m → Erdos73Infrastructure.SimpleGraph.GraphPath G}

theorem SelectedBrickSegment.exists_breaking_block_path
    (col : BipartiteColoringOn G S.vertexSet) (t : SelectedBrickSegment S col.color P)
    (a d : ℕ) (ha : a + d ≤ c - 1) (hr : 2 ≤ r) (hd : 0 < d)
    (hUT : Disjoint t.path.vertexSet (brickColumnBlock S a d ha)) :
    ∃ B : Erdos73Infrastructure.SimpleGraph.GraphPath G,
      IsParityBreakingPath col.color (brickColumnBlock S a d ha) B ∧
      B.vertexSet ⊆ brickStripNetwork S t.rows t.columns ∪ t.path.vertexSet ∧
      GraphPath.actualEdgeGraph B ≤ S.actualEdgeGraph ⊔ GraphPath.actualEdgeGraph t.path := by
  let D := brickStripNetwork S t.rows t.columns
  let T := brickColumnBlock S a d ha
  let K := brickStripNetworkGraph S t.rows t.columns ⊔ GraphPath.actualEdgeGraph t.path
  let L := brickColumnBlockGraph S a d ha
  let J := K ⊔ L
  have hDJ : brickStripNetworkGraph S t.rows t.columns ≤ J := le_sup_of_le_left le_sup_left
  have hUJ : GraphPath.actualEdgeGraph t.path ≤ J := le_sup_of_le_left le_sup_right
  have hLJ : L ≤ J := le_sup_right
  have hJG : J ≤ G := sup_le
    (sup_le ((brickStripNetworkGraph_le S t.rows t.columns).trans S.actualEdgeGraph_le)
      (GraphPath.actualEdgeGraph_le t.path))
    ((brickColumnBlockGraph_le S a d ha).trans S.actualEdgeGraph_le)
  have hD : DeletionOneConnected J D := brickStripNetwork_robust_of_edges S t.rows t.columns
    t.rows_nonempty t.columns_nonempty J hDJ
  have hT : DeletionOneConnected J T := brickColumnBlock_robust_of_edges S a d ha hr hd J hLJ
  have hDT : 2 ≤ (D ∩ T).card :=
    brickStripNetwork_block_overlap S t.rows t.columns t.rows_nonempty a d ha hd
  have hR : D ∪ T ⊆ S.vertexSet := union_subset (brickStripNetwork_subset S t.rows t.columns)
    (brickColumnBlock_subset S a d ha)
  let colR := col.mono_support hR
  have hK : ∀ x y, K.Adj x y → x ∈ D ∪ t.path.vertexSet ∧ y ∈ D ∪ t.path.vertexSet := by
    intro x y hxy
    rcases hxy with hxy | hxy
    · have hh := brickStripNetworkGraph_adj_support S t.rows t.columns hxy
      exact ⟨mem_union_left _ hh.1, mem_union_left _ hh.2⟩
    · have hh := GraphPath.actualEdgeGraph_adj_support t.path hxy
      exact ⟨mem_union_right _ hh.1, mem_union_right _ hh.2⟩
  have hL : ∀ x y, L.Adj x y → x ∈ T ∧ y ∈ T :=
    fun _ _ hxy => brickColumnBlockGraph_adj_support S a d ha hxy
  obtain ⟨B, hB, hBD, hBJ⟩ := exists_exact_edge_network_extension colR t.path t.clean hUT
    J K L hJG hUJ le_rfl hK hL (hD.union hT hDT) hT.two_le_card
  refine ⟨B, hB, hBD, hBJ.trans ?_⟩
  exact sup_le
    (sup_le (le_sup_of_le_left (brickStripNetworkGraph_le S t.rows t.columns)) le_sup_right)
    (le_sup_of_le_left (brickColumnBlockGraph_le S a d ha))

end
end Erdos73
