import ErdosProblems.Erdos73.BrickColumnSlice
import ErdosProblems.Erdos73.BlockBoundaryBranches

/-! Package the breaking paths on an actual translated wall subdivision, retaining attachments. -/

namespace Erdos73
noncomputable section
open scoped Classical

open SimpleGraph Finset Erdos73Infrastructure.SimpleGraph

variable {V : Type*} [Fintype V] {G : SimpleGraph V} {c r m h : ℕ}
variable {S : GraphSubdivisionModel (elementaryWall c r) G}
variable {P : Fin m → Erdos73Infrastructure.SimpleGraph.GraphPath G}

theorem BrickStripSelectionState.exists_breaking_slice_packing
    (col : BipartiteColoringOn G S.vertexSet) (st : BrickStripSelectionState S col.color P h)
    (k d : ℕ) (hr : 2 ≤ r) (hd : 0 < d)
    (hwidth : (6 * h + 1) * d ≤ c - 1) (hnumber : 5 * (2 * k - 2) < h) :
    ∃ a : ℕ, ∃ hs : a + (d + 1) ≤ c,
      let S' := S.restrictCopy (brickColumnSliceCopy a d hs)
      ∃ B : Fin k → Erdos73Infrastructure.SimpleGraph.GraphPath G,
        (∀ i, IsParityBreakingPath col.color S'.vertexSet (B i)) ∧
        Pairwise (fun i j => Disjoint (B i).vertexSet (B j).vertexSet) ∧
        (∀ i, GraphPath.actualEdgeGraph (B i) ≤ st.wallSegmentGraph col) ∧
        (∀ j, Disjoint (st.segment j).path.vertexSet S'.vertexSet) ∧
        (∀ i, (∃ u, (B i).source = S'.branchVertex u) ∧
          (∃ v, (B i).target = S'.branchVertex v)) ∧
        (∀ i, (B i).source ∈ internalVertexBoundary S.actualEdgeGraph S'.vertexSet ∧
          (B i).target ∈ internalVertexBoundary S.actualEdgeGraph S'.vertexSet) := by
  obtain ⟨a, ha, B, hB, hdis, hBJ, hUT⟩ := st.exists_breaking_block_packing col k d hr hd hwidth hnumber
  have hs : a + (d + 1) ≤ c := by omega
  let S' := S.restrictCopy (brickColumnSliceCopy a d hs)
  have hset : S'.vertexSet = brickColumnBlock S a d ha := brickColumnSlice_vertexSet S a d hs hr hd
  have hB' (i : Fin k) : IsParityBreakingPath col.color S'.vertexSet (B i) := by
    rw [hset]
    exact hB i
  have hlift (x : V) (hx : x ∈ S'.vertexSet) (hxb : ∃ w, x = S.branchVertex w) :
      ∃ u, x = S'.branchVertex u := by
    obtain ⟨w, hw⟩ := hxb
    obtain ⟨u, hu⟩ := (S.branchVertex_mem_restrictCopy_iff (brickColumnSliceCopy a d hs) w).mp
      (hw ▸ hx)
    exact ⟨u, hw.trans (congrArg S.branchVertex hu.symm)⟩
  refine ⟨a, hs, B, hB', hdis, hBJ, ?_, ?_, ?_⟩
  · intro j
    rw [hset]
    exact hUT j
  · intro i
    have hh := st.block_path_endpoints_are_branches col a d ha hUT (B i) (hB i) (hBJ i)
    exact ⟨hlift _ (hB' i).source_mem hh.1, hlift _ (hB' i).target_mem hh.2⟩
  · intro i
    rw [hset]
    exact st.block_path_endpoints_on_wall_boundary col a d ha hUT (B i) (hB i) (hBJ i)

end
end Erdos73
