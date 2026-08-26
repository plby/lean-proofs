import ErdosProblems.Erdos73.BrickBlockCandidate
import ErdosProblems.Erdos73.BrickStripSelection
import ErdosProblems.Erdos73.PathCongestion

/-! Congestion five gives disjoint breaking paths to one untouched actual column block. -/

namespace Erdos73
noncomputable section
open scoped Classical

open SimpleGraph Finset Erdos73Infrastructure.SimpleGraph

variable {V : Type*} [Fintype V] {G : SimpleGraph V} {c r m h : ℕ}
variable {S : GraphSubdivisionModel (elementaryWall c r) G}
variable {P : Fin m → Erdos73Infrastructure.SimpleGraph.GraphPath G}

def BrickStripSelectionState.wallSegmentGraph (col : BipartiteColoringOn G S.vertexSet)
    (st : BrickStripSelectionState S col.color P h) : SimpleGraph V :=
  S.actualEdgeGraph ⊔ ⨆ j, GraphPath.actualEdgeGraph (st.segment j).path

theorem BrickStripSelectionState.wallSegmentGraph_le (col : BipartiteColoringOn G S.vertexSet)
    (st : BrickStripSelectionState S col.color P h) : st.wallSegmentGraph col ≤ G :=
  sup_le S.actualEdgeGraph_le (iSup_le fun j => GraphPath.actualEdgeGraph_le (st.segment j).path)

theorem BrickStripSelectionState.exists_breaking_block_packing
    (col : BipartiteColoringOn G S.vertexSet) (st : BrickStripSelectionState S col.color P h)
    (k d : ℕ) (hr : 2 ≤ r) (hd : 0 < d)
    (hwidth : (6 * h + 1) * d ≤ c - 1) (hnumber : 5 * (2 * k - 2) < h) :
    ∃ a : ℕ, ∃ ha : a + d ≤ c - 1, ∃ B : Fin k → Erdos73Infrastructure.SimpleGraph.GraphPath G,
      (∀ i, IsParityBreakingPath col.color (brickColumnBlock S a d ha) (B i)) ∧
      Pairwise (fun i j => Disjoint (B i).vertexSet (B j).vertexSet) ∧
      (∀ i, GraphPath.actualEdgeGraph (B i) ≤ st.wallSegmentGraph col) ∧
      (∀ j, Disjoint (st.segment j).path.vertexSet (brickColumnBlock S a d ha)) := by
  obtain ⟨a, ha, hfree⟩ := st.exists_free_block d hwidth
  let T := brickColumnBlock S a d ha
  have hUT (j : Fin h) : Disjoint (st.segment j).path.vertexSet T := by
    apply Finset.disjoint_left.mpr
    intro x hxU hxT
    obtain ⟨b, _, hxb⟩ := mem_biUnion.mp hxT
    have hh := hfree j (brickBlockColumnIndex a d ha b) (by
      change a ≤ a + b.val
      omega) (by
      change a + b.val < a + d
      have hb := b.isLt
      omega)
    exact Finset.disjoint_left.mp hh hxU hxb
  have hex (j : Fin h) := (st.segment j).exists_breaking_block_path col a d ha hr hd (hUT j)
  choose B hB hsupport hBedges using hex
  let J := st.wallSegmentGraph col
  have hBJ (j : Fin h) : GraphPath.actualEdgeGraph (B j) ≤ J :=
    (hBedges j).trans (sup_le le_sup_left (le_sup_of_le_right
      (le_iSup (fun j => GraphPath.actualEdgeGraph (st.segment j).path) j)))
  let Q : Fin h → Erdos73Infrastructure.SimpleGraph.GraphPath J := fun j =>
    (B j).transfer J (GraphPath.edges_mem_of_actualEdgeGraph_le (B j) (hBJ j))
  have hQ (j : Fin h) : IsParityBreakingPath col.color T (Q j) :=
    (hB j).transfer J _
  have hcong (x : V) : (Finset.univ.filter (fun j => x ∈ (Q j).vertexSet)).card ≤ 5 := by
    apply le_trans (card_le_card ?_) (st.support_congestion_le_five x)
    intro j hj
    have hx := (mem_filter.mp hj).2
    change x ∈ ((B j).transfer J _).vertexSet at hx
    rw [Erdos73Infrastructure.SimpleGraph.GraphPath.transfer_vertexSet] at hx
    exact mem_filter.mpr ⟨mem_univ _, hsupport j hx⟩
  obtain ⟨R, hR, hdis⟩ := parityBreaking_packing_of_bounded_congestion J col.color T Q hQ k 5
    (by simpa only [Fintype.card_fin] using hnumber) hcong
  have hJG : J ≤ G := st.wallSegmentGraph_le col
  refine ⟨a, ha, fun i => (R i).mapLe hJG, fun i => (hR i).mapLe hJG, ?_, ?_, hUT⟩
  · intro i j hij
    simpa only [Erdos73Infrastructure.SimpleGraph.GraphPath.mapLe_vertexSet] using hdis hij
  · intro i
    rw [GraphPath.actualEdgeGraph_mapLe]
    exact GraphPath.actualEdgeGraph_le (R i)

end
end Erdos73
