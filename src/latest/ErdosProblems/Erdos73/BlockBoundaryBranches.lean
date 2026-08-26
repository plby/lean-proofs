import ErdosProblems.Erdos73.BlockBoundaryPaths
import ErdosProblems.Erdos73.SubdivisionBoundary

/-! Endpoints of the breaking block paths are actual pattern branch vertices. -/

namespace Erdos73
noncomputable section
open scoped Classical

open SimpleGraph Finset Erdos73Infrastructure.SimpleGraph

variable {V : Type*} {G : SimpleGraph V} {c r : ℕ}

theorem brickColumnBlock_boundary_is_branch
    (S : GraphSubdivisionModel (elementaryWall c r) G)
    (a d : ℕ) (ha : a + d ≤ c - 1) {x : V}
    (hx : x ∈ internalVertexBoundary S.actualEdgeGraph (brickColumnBlock S a d ha)) :
    ∃ w : ElementaryWallVertex c r, x = S.branchVertex w := by
  obtain ⟨hxT, y, hy, hxy⟩ := mem_filter.mp hx
  obtain ⟨j, _, hxj⟩ := mem_biUnion.mp hxT
  obtain ⟨b, _, hxb⟩ := mem_biUnion.mp hxj
  let k := brickBlockColumnIndex a d ha j
  let f : (cycleGraph 6).Copy (elementaryWall c r) :=
    elementaryBrickFaceCopy b.val (brickFaceColumn b.val k.val)
    (by have hb := b.isLt; omega)
    (by have hk := k.isLt; unfold brickFaceColumn; omega)
    (by unfold brickFaceColumn; omega)
  have hsub : (S.restrictCopy f).vertexSet ⊆ brickColumnBlock S a d ha := by
    intro z hz
    exact mem_biUnion.mpr ⟨j, mem_univ _, mem_biUnion.mpr ⟨b, mem_univ _, hz⟩⟩
  exact S.branch_of_adj_leaving_restrictCopy f _ hsub hxb hxy hy

theorem BrickStripSelectionState.block_path_endpoints_are_branches
    [Fintype V] {m h : ℕ} {S : GraphSubdivisionModel (elementaryWall c r) G}
    {P : Fin m → Erdos73Infrastructure.SimpleGraph.GraphPath G}
    (col : BipartiteColoringOn G S.vertexSet) (st : BrickStripSelectionState S col.color P h)
    (a d : ℕ) (ha : a + d ≤ c - 1)
    (hUT : ∀ j, Disjoint (st.segment j).path.vertexSet (brickColumnBlock S a d ha))
    (B : Erdos73Infrastructure.SimpleGraph.GraphPath G)
    (hB : IsParityBreakingPath col.color (brickColumnBlock S a d ha) B)
    (hBJ : GraphPath.actualEdgeGraph B ≤ st.wallSegmentGraph col) :
    (∃ u : ElementaryWallVertex c r, B.source = S.branchVertex u) ∧
      (∃ v : ElementaryWallVertex c r, B.target = S.branchVertex v) := by
  have hh := st.block_path_endpoints_on_wall_boundary col a d ha hUT B hB hBJ
  exact ⟨brickColumnBlock_boundary_is_branch S a d ha hh.1,
    brickColumnBlock_boundary_is_branch S a d ha hh.2⟩

end
end Erdos73
