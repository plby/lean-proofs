import ErdosProblems.Erdos633b.BoundaryStarPartition
import ErdosProblems.Erdos633b.SegmentLength

/-! The full straight-angle sum at a tile vertex in an outer open side,
derived from the actual geometric tiling and the verified angular partition. -/

namespace Erdos633b.Tiling

noncomputable instance {T : Triangle} {n : ℕ} (d : Tiling T n) (p : Plane) :
    Fintype (d.VertexPiece p) := Fintype.ofFinite _

theorem vertexAngle_interval_length {T : Triangle} {n : ℕ} (d : Tiling T n)
    (i : Fin 3) {p : Plane} (hp : p ∈ T.openEdge i) (e : d.VertexPiece p) :
    |d.vertexAngleStart i p e - d.vertexAngleEnd i p e| = d.tile.angle e.val.2 := by
  let S : Triangle := d.tile.move (d.place e.val.1)
  have hST : S.support ⊆ T.support := by
    rw [Triangle.support_move]
    exact d.piece_subset e.val.1
  have hS : S.points e.val.2 = p := e.property
  have hA := S.edge_vertex_mem e.val.2 (e.val.2 + 1)
    ((by decide : ∀ j : Fin 3, j + 1 ≠ j) e.val.2)
  have hB := S.edge_vertex_mem e.val.2 (e.val.2 + 2)
    ((by decide : ∀ j : Fin 3, j + 2 ≠ j) e.val.2)
  have hAn : S.points (e.val.2 + 1) ≠ p := by
    intro he
    exact S.ne_vertex_of_mem_edge e.val.2 hA (he.trans hS.symm)
  have hBn : S.points (e.val.2 + 2) ≠ p := by
    intro he
    exact S.ne_vertex_of_mem_edge e.val.2 hB (he.trans hS.symm)
  calc
    _ = |T.boundaryAngle i p (S.points (e.val.2 + 2)) -
        T.boundaryAngle i p (S.points (e.val.2 + 1))| := abs_sub_comm _ _
    _ = EuclideanGeometry.angle (S.points (e.val.2 + 1)) p (S.points (e.val.2 + 2)) :=
      (T.boundaryAngle_difference i hp (hST hA.1) (hST hB.1) hAn hBn).symm
    _ = S.angle e.val.2 := by unfold Triangle.angle; rw [hS]
    _ = d.tile.angle e.val.2 := d.tile.angle_move (d.place e.val.1) e.val.2

theorem boundary_vertex_angle_sum {T : Triangle} {n : ℕ} (d : Tiling T n)
    (i : Fin 3) {p : Plane} (hp : p ∈ T.openEdge i)
    (a : Fin n) (j : Fin 3) (ha : d.place a (d.tile.points j) = p) :
    (∑ e : d.VertexPiece p, d.tile.angle e.val.2) = Real.pi := by
  have hs := real_segment_partition_length_on 0 Real.pi Real.pi_pos.le
    (d.vertexAngleStart i p) (d.vertexAngleEnd i p) (d.vertexAngle_endpoints_ne i hp)
    (d.vertexAngle_intervals_cover i hp a j ha) (d.vertexAngle_open_intervals_disjoint i hp)
  simpa only [d.vertexAngle_interval_length i hp, sub_zero] using hs

end Erdos633b.Tiling
