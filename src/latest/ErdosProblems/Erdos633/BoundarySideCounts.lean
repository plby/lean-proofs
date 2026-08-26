import ErdosProblems.Erdos633.BoundaryEdges
import Mathlib.MeasureTheory.Measure.Hausdorff

/-!
# Actual boundary-side length counts

The full tile edges on an outer side cover it except for finitely many tile
vertices, and distinct such edges overlap only in that finite set. Their
one-dimensional Hausdorff measures therefore add to the outer side length.
No edge-to-edge hypothesis or assumed boundary-count equation is used.
-/

namespace Erdos633

open MeasureTheory
open scoped BigOperators ENNReal

noncomputable def TriangleDissection.boundaryEdgeIndices {P : Triangle} {N : ℕ}
    (T : TriangleDissection P N) (k : Fin 3) : Finset (Fin N × Fin 3) := by
  classical
  exact Finset.univ.filter fun p => (T.tile p.1).edge p.2 ⊆ P.edge k

theorem TriangleDissection.mem_boundaryEdgeIndices {P : Triangle} {N : ℕ}
    (T : TriangleDissection P N) (k : Fin 3) (p : Fin N × Fin 3) :
    p ∈ T.boundaryEdgeIndices k ↔ (T.tile p.1).edge p.2 ⊆ P.edge k := by
  classical
  simp [TriangleDissection.boundaryEdgeIndices]

theorem TriangleDissection.not_tile_vertex_of_not_vertexFinset {P : Triangle} {N : ℕ}
    (T : TriangleDissection P N) {z : ℂ} (hv : z ∉ T.vertexFinset) (i : Fin N) :
    z ∉ Set.range (T.tile i).vertex := by
  rintro ⟨j, hj⟩
  exact hv ((T.mem_vertexFinset z).mpr ⟨i, j, hj⟩)

theorem TriangleDissection.boundaryEdges_cover_away_from_vertices
    {P : Triangle} {N : ℕ} (T : TriangleDissection P N) (k : Fin 3)
    {z : ℂ} (hv : z ∉ T.vertexFinset) :
    z ∈ P.edge k ↔
      z ∈ ⋃ p : T.boundaryEdgeIndices k, (T.tile p.val.1).edge p.val.2 := by
  classical
  constructor
  · intro hz
    have hzP := P.edge_subset_carrier k hz
    have hcover := hzP
    rw [← T.covers, Set.mem_iUnion] at hcover
    obtain ⟨i, hi⟩ := hcover
    have hnot : z ∉ interior (T.tile i).carrier :=
      fun h => P.edge_not_mem_interior k hz (interior_mono (T.tile_subset i) h)
    obtain ⟨j, hj⟩ := (T.tile i).boundary_nonvertex_mem_openEdge z hi hnot
      (T.not_tile_vertex_of_not_vertexFinset hv i)
    have hsub : (T.tile i).edge j ⊆ P.edge k :=
      P.edge_contains_segment_of_open_point k
        (T.tile_subset i ((T.tile i).edgeStart_mem_carrier j))
        (T.tile_subset i ((T.tile i).edgeEnd_mem_carrier j)) hz hj
    refine Set.mem_iUnion.mpr ⟨⟨(i, j), (T.mem_boundaryEdgeIndices k (i, j)).mpr hsub⟩, ?_⟩
    exact (T.tile i).openEdge_subset_edge j hj
  · intro hz
    obtain ⟨p, hp⟩ := Set.mem_iUnion.mp hz
    exact (T.mem_boundaryEdgeIndices k p.val).mp p.property hp

theorem TriangleDissection.boundaryEdges_inter_subset_vertices
    {P : Triangle} {N : ℕ} (T : TriangleDissection P N) (k : Fin 3)
    {p q : T.boundaryEdgeIndices k} (hpq : p ≠ q) :
    (T.tile p.val.1).edge p.val.2 ∩ (T.tile q.val.1).edge q.val.2 ⊆
      (T.vertexFinset : Set ℂ) := by
  classical
  rintro z ⟨hp, hq⟩
  by_contra hv
  have hzedge := (T.mem_boundaryEdgeIndices k p.val).mp p.property hp
  have hpc := (T.tile p.val.1).edge_subset_carrier p.val.2 hp
  have hqc := (T.tile q.val.1).edge_subset_carrier q.val.2 hq
  have hij : p.val.1 = q.val.1 := T.boundary_nonvertex_tile_unique
    (P.edge_subset_carrier k hzedge) (P.edge_not_mem_interior k hzedge) hv hpc hqc
  have hlabel : p.val.2 = q.val.2 := by
    by_contra hne
    have hp' := (T.tile p.val.1).mem_openEdge_of_not_vertex p.val.2 hp
      (T.not_tile_vertex_of_not_vertexFinset hv p.val.1)
    have hq' := (T.tile q.val.1).mem_openEdge_of_not_vertex q.val.2 hq
      (T.not_tile_vertex_of_not_vertexFinset hv q.val.1)
    rw [← hij] at hq'
    exact Set.disjoint_left.mp ((T.tile p.val.1).openEdges_disjoint hne) hp' hq'
  exact hpq (Subtype.ext (Prod.ext hij hlabel))

theorem Triangle.hausdorffMeasure_edge (P : Triangle) (k : Fin 3) :
    (μH[1] : Measure ℂ) (P.edge k) = ENNReal.ofReal (P.sideLength k) := by
  rw [Triangle.edge, hausdorffMeasure_segment, edist_dist]
  rfl

theorem Triangle.hausdorffMeasure_edge_toReal (P : Triangle) (k : Fin 3) :
    ((μH[1] : Measure ℂ) (P.edge k)).toReal = P.sideLength k := by
  rw [P.hausdorffMeasure_edge, ENNReal.toReal_ofReal (P.sideLength_pos k).le]

theorem Triangle.measurableSet_edge (P : Triangle) (k : Fin 3) : MeasurableSet (P.edge k) := by
  rw [Triangle.edge, segment_eq_image_lineMap]
  exact (isCompact_Icc.image AffineMap.lineMap_continuous).isClosed.measurableSet

open Classical in
theorem TriangleDissection.boundary_side_length_sum {P : Triangle} {N : ℕ}
    (T : TriangleDissection P N) (k : Fin 3) :
    P.sideLength k = ∑ p : T.boundaryEdgeIndices k, (T.tile p.val.1).sideLength p.val.2 := by
  classical
  let μ : Measure ℂ := μH[1]
  let : NullSingletonClass μ := Measure.nullSingletonClass_hausdorff ℂ (by norm_num)
  have hnull : μ (T.vertexFinset : Set ℂ) = 0 := T.vertexFinset.measure_zero μ
  have hae : P.edge k =ᵐ[μ]
      ⋃ p : T.boundaryEdgeIndices k, (T.tile p.val.1).edge p.val.2 := by
    have hv := (T.vertexFinset.finite_toSet.countable).ae_notMem μ
    filter_upwards [hv] with z hz
    exact propext (T.boundaryEdges_cover_away_from_vertices k hz)
  have hd : Pairwise fun p q : T.boundaryEdgeIndices k =>
      AEDisjoint μ ((T.tile p.val.1).edge p.val.2) ((T.tile q.val.1).edge q.val.2) := by
    intro p q hpq
    exact measure_mono_null (T.boundaryEdges_inter_subset_vertices k hpq) hnull
  have hm : ∀ p : T.boundaryEdgeIndices k,
      NullMeasurableSet ((T.tile p.val.1).edge p.val.2) μ :=
    fun p => ((T.tile p.val.1).measurableSet_edge p.val.2).nullMeasurableSet
  have hsum : μ (P.edge k) =
      ∑ p : T.boundaryEdgeIndices k, μ ((T.tile p.val.1).edge p.val.2) := by
    rw [measure_congr hae, measure_iUnion₀ hd hm, tsum_fintype]
  have hfinite (p : T.boundaryEdgeIndices k) : μ ((T.tile p.val.1).edge p.val.2) ≠ ⊤ := by
    rw [Triangle.hausdorffMeasure_edge]
    exact ENNReal.ofReal_ne_top
  have hr := congrArg ENNReal.toReal hsum
  rw [ENNReal.toReal_sum (fun p _ => hfinite p)] at hr
  simpa only [μ, Triangle.hausdorffMeasure_edge_toReal] using hr

theorem Triangle.sideLength_mapIsometry (P : Triangle) (e : ℂ ≃ᵢ ℂ) (k : Fin 3) :
    (P.mapIsometry e).sideLength k = P.sideLength k := by
  fin_cases k
  · exact e.dist_eq P.b P.c
  · exact e.dist_eq P.c P.a
  · exact e.dist_eq P.a P.b

theorem CongruentTiling.labelledTile_sideLength {P R : Triangle} {N : ℕ}
    (T : CongruentTiling P R N) (i : Fin N) (k : Fin 3) :
    (T.labelledTile i).sideLength k = R.sideLength k :=
  R.sideLength_mapIsometry (T.tileIsometry i) k

noncomputable def CongruentTiling.boundarySideCount {P R : Triangle} {N : ℕ}
    (T : CongruentTiling P R N) (k l : Fin 3) : ℕ := by
  classical
  exact (Finset.univ.filter fun p : T.labelledDissection.boundaryEdgeIndices k => p.val.2 = l).card

theorem CongruentTiling.boundarySideCount_sum {P R : Triangle} {N : ℕ}
    (T : CongruentTiling P R N) (k : Fin 3) :
    ∑ l : Fin 3, (T.boundarySideCount k l : ℝ) * R.sideLength l =
      ∑ p : T.labelledDissection.boundaryEdgeIndices k, R.sideLength p.val.2 := by
  classical
  calc
    _ = ∑ l : Fin 3, ∑ p : T.labelledDissection.boundaryEdgeIndices k,
        if p.val.2 = l then R.sideLength l else 0 := by
      apply Finset.sum_congr rfl
      intro l _
      rw [← Finset.sum_filter]
      simp [CongruentTiling.boundarySideCount]
    _ = ∑ p : T.labelledDissection.boundaryEdgeIndices k,
        ∑ l : Fin 3, if p.val.2 = l then R.sideLength l else 0 := Finset.sum_comm
    _ = _ := by simp

/-- Every outer side is a nonnegative integer combination of the three actual
reference side lengths. The coefficients count full geometric tile edges. -/
theorem CongruentTiling.boundary_side_count_equation {P R : Triangle} {N : ℕ}
    (T : CongruentTiling P R N) (k : Fin 3) :
    P.sideLength k = ∑ l : Fin 3, (T.boundarySideCount k l : ℝ) * R.sideLength l := by
  classical
  rw [T.boundarySideCount_sum]
  have h := T.labelledDissection.boundary_side_length_sum k
  change P.sideLength k = ∑ p : T.labelledDissection.boundaryEdgeIndices k,
    (T.labelledTile p.val.1).sideLength p.val.2 at h
  simpa only [T.labelledTile_sideLength] using h

theorem CongruentTiling.boundary_side_count_equation_three {P R : Triangle} {N : ℕ}
    (T : CongruentTiling P R N) (k : Fin 3) :
    P.sideLength k = (T.boundarySideCount k 0 : ℝ) * R.sideLength 0 +
      (T.boundarySideCount k 1 : ℝ) * R.sideLength 1 +
      (T.boundarySideCount k 2 : ℝ) * R.sideLength 2 := by
  have h := T.boundary_side_count_equation k
  norm_num [Fin.sum_univ_succ] at h
  simpa only [← add_assoc] using h

/-- The nonnegative integer eigenvalue equation used in reptile necessity,
extracted from the actual tiling after matching the outer angle labels. -/
theorem CongruentTiling.boundary_matrix_of_permuted_angles
    {P R : Triangle} {N : ℕ} (T : CongruentTiling P R N)
    (h : PermutedTriple P.cornerAngle R.cornerAngle) :
    ∃ k : ℝ, 0 < k ∧ k ^ 2 = N ∧ ∃ D : Fin 3 → Fin 3 → ℕ,
      ∀ i, ∑ j : Fin 3, (D i j : ℝ) * R.sideLength j = k * R.sideLength i := by
  classical
  obtain ⟨e, he⟩ := h
  let Q := P.relabel e
  have hA : Q.angleA = R.angleA := (P.cornerAngle_relabel e 0).trans (he 0)
  have hB : Q.angleB = R.angleB := (P.cornerAngle_relabel e 1).trans (he 1)
  obtain ⟨k, hk, hab, hac, hbc⟩ := Q.scaled_sides_of_angles_eq R hA hB
  obtain ⟨f, hf⟩ := Q.isometry_of_scaled_sides R k hk hab hac hbc
  let U : CongruentTiling Q R N := T.of_carrier_eq (P.relabel_carrier e).symm
  have hscale := U.similarity_scale_squared k hk f hf
  have hside (i : Fin 3) : Q.sideLength i = k * R.sideLength i := by
    have hi : i = 0 ∨ i = 1 ∨ i = 2 := by omega
    rcases hi with rfl | rfl | rfl
    · exact hbc
    · change dist Q.c Q.a = k * dist R.c R.a
      rw [dist_comm Q.c Q.a, dist_comm R.c R.a]
      exact hac
    · exact hab
  refine ⟨k, hk, hscale, U.boundarySideCount, ?_⟩
  intro i
  exact (U.boundary_side_count_equation i).symm.trans (hside i)

end Erdos633
