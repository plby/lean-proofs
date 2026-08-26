import ErdosProblems.Erdos633b.BoundaryAngleRange
import ErdosProblems.Erdos633b.BoundaryRadialInterior
import ErdosProblems.Erdos633b.SmallRadial

/-! The angles of tiles incident at an actual boundary vertex form a finite
partition of [0,pi], with pairwise disjoint open angular intervals. -/

namespace Erdos633b.Tiling

def VertexPiece {T : Triangle} {n : ℕ} (d : Tiling T n) (p : Plane) :=
  {e : Fin n × Fin 3 // d.place e.1 (d.tile.points e.2) = p}

instance {T : Triangle} {n : ℕ} (d : Tiling T n) (p : Plane) : Finite (d.VertexPiece p) := by
  unfold VertexPiece
  infer_instance

theorem vertexPiece_tile_injective {T : Triangle} {n : ℕ} (d : Tiling T n) (p : Plane) :
    Function.Injective (fun e : d.VertexPiece p => e.val.1) := by
  intro e f h
  change e.val.1 = f.val.1 at h
  apply Subtype.ext
  apply Prod.ext h
  apply d.tile.independent.injective
  apply (d.place e.val.1).injective
  exact e.property.trans (by rw [h]; exact f.property.symm)

noncomputable def vertexAngleStart {T : Triangle} {n : ℕ} (d : Tiling T n)
    (i : Fin 3) (p : Plane) (e : d.VertexPiece p) : ℝ :=
  T.boundaryAngle i p (d.place e.val.1 (d.tile.points (e.val.2 + 1)))

noncomputable def vertexAngleEnd {T : Triangle} {n : ℕ} (d : Tiling T n)
    (i : Fin 3) (p : Plane) (e : d.VertexPiece p) : ℝ :=
  T.boundaryAngle i p (d.place e.val.1 (d.tile.points (e.val.2 + 2)))

theorem vertexAngle_endpoints_ne {T : Triangle} {n : ℕ} (d : Tiling T n)
    (i : Fin 3) {p : Plane} (hp : p ∈ T.openEdge i) (e : d.VertexPiece p) :
    d.vertexAngleStart i p e ≠ d.vertexAngleEnd i p e := by
  have hST : (d.tile.move (d.place e.val.1)).support ⊆ T.support := by
    rw [Triangle.support_move]
    exact d.piece_subset e.val.1
  exact T.boundaryAngle_endpoints_ne (d.tile.move (d.place e.val.1)) hST i e.val.2 hp e.property

theorem vertexAngle_intervals_cover {T : Triangle} {n : ℕ} (d : Tiling T n)
    (i : Fin 3) {p : Plane} (hp : p ∈ T.openEdge i)
    (a : Fin n) (j : Fin 3) (ha : d.place a (d.tile.points j) = p) :
    (⋃ e : d.VertexPiece p, segment ℝ (d.vertexAngleStart i p e) (d.vertexAngleEnd i p e)) =
      Set.Icc 0 Real.pi := by
  apply Set.Subset.antisymm
  · intro t ht
    obtain ⟨e, he⟩ := Set.mem_iUnion.mp ht
    exact (convex_Icc (0 : ℝ) Real.pi).segment_subset
      ⟨T.boundaryAngle_nonneg i p _, T.boundaryAngle_le_pi i p _⟩
      ⟨T.boundaryAngle_nonneg i p _, T.boundaryAngle_le_pi i p _⟩ he
  · intro t ht
    obtain ⟨q, hq, hqp, hqt⟩ := T.boundaryAngle_surjective i hp ht
    obtain ⟨ε, hε, hlocal⟩ := d.local_boundary_vertex_cover i
      (T.openEdge_subset_edge i hp) a j ha
    obtain ⟨r, hr, hr1, hxball⟩ := exists_small_radial p q Metric.isOpen_ball
      (Metric.mem_ball_self hε)
    have hxT : AffineMap.homothety p r q ∈ T.support := by
      rw [AffineMap.homothety_eq_lineMap]
      exact T.support_convex.segment_subset (T.openEdge_subset_edge i hp).1 hq
        (lineMap_mem_segment ℝ _ _ ⟨hr.le, hr1.le⟩)
    obtain ⟨b, k, hbk, hxB⟩ := (hlocal _ hxball).mp hxT
    let e : d.VertexPiece p := ⟨(b, k), hbk⟩
    let S : Triangle := d.tile.move (d.place b)
    have hST : S.support ⊆ T.support := by
      rw [Triangle.support_move]
      exact d.piece_subset b
    have hxS : AffineMap.homothety p r q ∈ S.support := by rwa [Triangle.support_move]
    have hxn : AffineMap.homothety p r q ≠ p := by
      intro he
      apply hqp
      apply AffineMap.homothety_injective p hr.ne'
      simpa only [AffineMap.homothety_apply, vsub_self, smul_zero, zero_vadd] using he
    have he := T.boundaryAngle_mem_of_support_shared S hST i k hp hbk hxS hxn
    rw [T.boundaryAngle_radial i p q hr, hqt] at he
    exact Set.mem_iUnion.mpr ⟨e, he⟩

theorem vertexAngle_open_intervals_disjoint {T : Triangle} {n : ℕ} (d : Tiling T n)
    (i : Fin 3) {p : Plane} (hp : p ∈ T.openEdge i) :
    Pairwise fun e f : d.VertexPiece p =>
      Disjoint (openSegment ℝ (d.vertexAngleStart i p e) (d.vertexAngleEnd i p e))
        (openSegment ℝ (d.vertexAngleStart i p f) (d.vertexAngleEnd i p f)) := by
  intro e f hef
  have hk := (d.vertexPiece_tile_injective p).ne hef
  let S : Triangle := d.tile.move (d.place e.val.1)
  let R : Triangle := d.tile.move (d.place f.val.1)
  have hST : S.support ⊆ T.support := by
    rw [Triangle.support_move]
    exact d.piece_subset e.val.1
  have hRT : R.support ⊆ T.support := by
    rw [Triangle.support_move]
    exact d.piece_subset f.val.1
  have hS : S.points e.val.2 = p := e.property
  have hR : R.points f.val.2 = p := f.property
  apply Set.disjoint_left.mpr
  intro t htS htR
  have hsimg : t ∈ T.boundaryAngle i p '' S.openEdge e.val.2 := by
    rw [T.boundaryAngle_image_openEdge S hST i e.val.2 hp hS]
    exact htS
  have hrimg : t ∈ T.boundaryAngle i p '' R.openEdge f.val.2 := by
    rw [T.boundaryAngle_image_openEdge R hRT i f.val.2 hp hR]
    exact htR
  obtain ⟨q, hq, hqt⟩ := hsimg
  obtain ⟨r, hr, hrt⟩ := hrimg
  have hqe := S.openEdge_subset_edge e.val.2 hq
  have hre := R.openEdge_subset_edge f.val.2 hr
  have hqp : q ≠ p := hS ▸ S.ne_vertex_of_mem_edge e.val.2 hqe
  have hrp : r ≠ p := hR ▸ R.ne_vertex_of_mem_edge f.val.2 hre
  have hsame := T.boundaryAngle_sameRay i hp (hST hqe.1) (hRT hre.1) hqp hrp
    (hqt.trans hrt.symm)
  obtain ⟨x, hxS, hxR⟩ := S.interiors_inter_of_sameRay_openEdges R e.val.2 f.val.2 hS hR hq hr hsame
  rw [Triangle.support_move] at hxS hxR
  exact Set.disjoint_left.mp (d.disjoint_interiors hk) hxS hxR

end Erdos633b.Tiling
