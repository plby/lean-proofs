import ErdosProblems.Erdos73.BrickSlicePacking
import ErdosProblems.Erdos73.BrickSliceBoundaryCoordinates

/-! Breaking paths attached at the first or last brick-wall column of an actual subwall. -/

namespace Erdos73
noncomputable section
open scoped Classical

open SimpleGraph Finset

variable {V : Type*} [Fintype V] {G : SimpleGraph V} {c r m h : ℕ}
variable {S : GraphSubdivisionModel (elementaryWall c r) G}
variable {P : Fin m → Erdos73Infrastructure.SimpleGraph.GraphPath G}

theorem BrickStripSelectionState.exists_breaking_slice_handles
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
        (∀ i, ∃ u v : ElementaryWallVertex (d + 1) r,
          (B i).source = S'.branchVertex u ∧ (B i).target = S'.branchVertex v ∧
          (u.val.2.val ≤ 1 ∨ 2 * d ≤ u.val.2.val) ∧
          (v.val.2.val ≤ 1 ∨ 2 * d ≤ v.val.2.val)) := by
  obtain ⟨a, hs, B, hB, hdis, hBJ, hUT, hbranches, hboundary⟩ :=
    st.exists_breaking_slice_packing col k d hr hd hwidth hnumber
  refine ⟨a, hs, B, hB, hdis, hBJ, hUT, ?_⟩
  intro i
  obtain ⟨⟨u, hu⟩, ⟨v, hv⟩⟩ := hbranches i
  exact ⟨u, v, hu, hv,
    brickColumnSlice_boundary_column S a d hs u (hu ▸ (hboundary i).1),
    brickColumnSlice_boundary_column S a d hs v (hv ▸ (hboundary i).2)⟩

end
end Erdos73
