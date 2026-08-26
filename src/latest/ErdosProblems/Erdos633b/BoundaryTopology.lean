import ErdosProblems.Erdos633b.BoundaryFaces
import ErdosProblems.Erdos633b.LocalIncidence

/-! Open boundary edges and the local inward half-plane forced by a
contained triangle. These facts rule out overlapping outer-boundary edges. -/

namespace Erdos633b

namespace Triangle

def openEdge (T : Triangle) (i : Fin 3) : Set Plane :=
  {p | T.coord i p = 0 ∧ ∀ j, j ≠ i → 0 < T.coord j p}

theorem openEdge_subset_edge (T : Triangle) (i : Fin 3) : T.openEdge i ⊆ T.edge i := by
  rintro p ⟨hi, h⟩
  refine ⟨(T.mem_support_iff_all_coords p).mpr ?_, hi⟩
  intro j
  by_cases hj : j = i
  · simp [hj, hi]
  · exact (h j hj).le

theorem openEdge_eq_openSegment (T : Triangle) (i : Fin 3) :
    T.openEdge i = openSegment ℝ (T.points (i + 1)) (T.points (i + 2)) := by
  have h1 : i + 1 ≠ i := (by decide : ∀ i : Fin 3, i + 1 ≠ i) i
  have h2 : i + 2 ≠ i := (by decide : ∀ i : Fin 3, i + 2 ≠ i) i
  have h12 : i + 1 ≠ i + 2 := (by decide : ∀ i : Fin 3, i + 1 ≠ i + 2) i
  ext p
  constructor
  · intro hp
    have hs : p ∈ segment ℝ (T.points (i + 1)) (T.points (i + 2)) := by
      rw [← T.edge_eq_segment]
      exact T.openEdge_subset_edge i hp
    apply mem_openSegment_of_ne_left_right ?_ ?_ hs
    · intro he
      have h := hp.2 (i + 2) h2
      rw [← he, T.coord_vertex, if_neg h12.symm] at h
      exact lt_irrefl _ h
    · intro he
      have h := hp.2 (i + 1) h1
      rw [← he, T.coord_vertex, if_neg h12] at h
      exact lt_irrefl _ h
  · intro hp
    have hmap (j : Fin 3) : T.coord j p ∈
        openSegment ℝ (T.coord j (T.points (i + 1))) (T.coord j (T.points (i + 2))) := by
      rw [← image_openSegment ℝ (T.coord j)]
      exact ⟨p, hp, rfl⟩
    refine ⟨?_, ?_⟩
    · have h := hmap i
      simpa only [coord_vertex, if_neg h1.symm, if_neg h2.symm,
        openSegment_same, Set.mem_singleton_iff] using h
    · intro j hj
      have hj' := (by decide : ∀ i j : Fin 3,
        j ≠ i → j = i + 1 ∨ j = i + 2) i j hj
      rcases hj' with rfl | rfl
      · have h := hmap (i + 1)
        rw [coord_vertex, coord_vertex, if_pos rfl, if_neg h12, openSegment_symm,
          openSegment_eq_Ioo (by norm_num : (0 : ℝ) < 1)] at h
        exact h.1
      · have h := hmap (i + 2)
        rw [coord_vertex, coord_vertex, if_neg h12.symm, if_pos rfl,
          openSegment_eq_Ioo (by norm_num : (0 : ℝ) < 1)] at h
        exact h.1

theorem edge_vertex_mem (T : Triangle) (i j : Fin 3) (hji : j ≠ i) :
    T.points j ∈ T.edge i := by
  refine ⟨T.vertex_mem_support j, ?_⟩
  simp only [Set.mem_ofPred_eq, coord_vertex, if_neg hji.symm]

theorem coord_factor_of_edge_subset (T S : Triangle) (i j : Fin 3)
    (he : S.edge j ⊆ T.edge i) (p : Plane) :
    T.coord i p = T.coord i (S.points j) * S.coord j p := by
  have h : T.coord i = T.coord i (S.points j) • S.coord j := by
    apply AffineMap.ext_on (S.span_eq_top (by simp [Plane]))
    rintro _ ⟨k, rfl⟩
    change T.coord i (S.points k) = T.coord i (S.points j) * S.coord j (S.points k)
    by_cases hk : k = j
    · simp only [hk, coord_vertex, ite_true, mul_one]
    · have hz := (he (S.edge_vertex_mem j k hk)).2
      simpa only [Set.mem_ofPred_eq, coord_vertex, if_neg (Ne.symm hk), mul_zero] using hz
  exact congrArg (fun f : Plane →ᵃ[ℝ] ℝ => f p) h

theorem coord_factor_pos_of_edge_subset (T S : Triangle) (hST : S.support ⊆ T.support)
    (i j : Fin 3) (he : S.edge j ⊆ T.edge i) : 0 < T.coord i (S.points j) := by
  have hn := T.coord_nonneg (hST (S.vertex_mem_support j)) i
  apply lt_of_le_of_ne hn
  intro hz
  have h := T.coord_factor_of_edge_subset S i j he (T.points i)
  rw [hz.symm, zero_mul, T.coord_vertex, if_pos rfl] at h
  norm_num at h

theorem openEdge_disjoint (T : Triangle) {i j : Fin 3} (hij : i ≠ j) :
    Disjoint (T.openEdge i) (T.openEdge j) := by
  apply Set.disjoint_left.mpr
  intro p hp hq
  have h := hq.2 i hij
  rw [hp.1] at h
  exact lt_irrefl _ h

theorem openEdge_neighborhood (T S : Triangle) (hST : S.support ⊆ T.support)
    (i j : Fin 3) (he : S.edge j ⊆ T.edge i) {p : Plane} (hp : p ∈ S.openEdge j) :
    ∃ U : Set Plane, IsOpen U ∧ p ∈ U ∧ U ∩ interior T.support ⊆ interior S.support := by
  let U : Set Plane := ⋂ k : {k : Fin 3 // k ≠ j}, {x | 0 < S.coord k.val x}
  have hU : IsOpen U := isOpen_iInter_of_finite (fun k =>
    isOpen_lt continuous_const (continuous_barycentric_coord S.affineBasis k.val))
  refine ⟨U, hU, Set.mem_iInter.mpr (fun k => hp.2 k.val k.property), ?_⟩
  rintro x ⟨hxU, hxT⟩
  apply (S.mem_interior_support_iff_all_coords x).mpr
  intro k
  by_cases hk : k = j
  · subst k
    have hpos := (T.mem_interior_support_iff_all_coords x).mp hxT i
    rw [T.coord_factor_of_edge_subset S i j he x] at hpos
    exact pos_of_mul_pos_right hpos (T.coord_factor_pos_of_edge_subset S hST i j he).le
  · exact Set.mem_iInter.mp hxU ⟨k, hk⟩

theorem closure_interior_support (T : Triangle) : closure (interior T.support) = T.support := by
  rw [T.support_convex.closure_interior_eq_closure_of_nonempty_interior
    T.interior_support_nonempty, T.support_isCompact.isClosed.closure_eq]

theorem interiors_inter_of_openEdges_inter (T S R : Triangle)
    (hST : S.support ⊆ T.support) (hRT : R.support ⊆ T.support)
    (i j k : Fin 3) (hS : S.edge j ⊆ T.edge i) (hR : R.edge k ⊆ T.edge i)
    {p : Plane} (hpS : p ∈ S.openEdge j) (hpR : p ∈ R.openEdge k) :
    (interior S.support ∩ interior R.support).Nonempty := by
  obtain ⟨U, hU, hpU, hSU⟩ := T.openEdge_neighborhood S hST i j hS hpS
  obtain ⟨V, hV, hpV, hRV⟩ := T.openEdge_neighborhood R hRT i k hR hpR
  have hpT : p ∈ closure (interior T.support) := by
    rw [T.closure_interior_support]
    exact hST (S.openEdge_subset_edge j hpS).1
  obtain ⟨x, hxUV, hx⟩ := mem_closure_iff.mp hpT (U ∩ V) (hU.inter hV) ⟨hpU, hpV⟩
  exact ⟨x, hSU ⟨hxUV.1, hx⟩, hRV ⟨hxUV.2, hx⟩⟩

end Triangle

namespace Tiling

theorem boundary_openEdges_disjoint {T : Triangle} {n : ℕ} (d : Tiling T n)
    {a b : Fin n} (hab : a ≠ b) (i j k : Fin 3)
    (hS : (d.tile.move (d.place a)).edge j ⊆ T.edge i)
    (hR : (d.tile.move (d.place b)).edge k ⊆ T.edge i) :
    Disjoint ((d.tile.move (d.place a)).openEdge j)
      ((d.tile.move (d.place b)).openEdge k) := by
  let S : Triangle := d.tile.move (d.place a)
  let R : Triangle := d.tile.move (d.place b)
  have hST : S.support ⊆ T.support := by
    rw [Triangle.support_move]
    exact d.piece_subset a
  have hRT : R.support ⊆ T.support := by
    rw [Triangle.support_move]
    exact d.piece_subset b
  apply Set.disjoint_left.mpr
  intro p hpS hpR
  obtain ⟨x, hxS, hxR⟩ := T.interiors_inter_of_openEdges_inter S R hST hRT i j k
    hS hR hpS hpR
  have hd := d.disjoint_interiors hab
  change Disjoint (interior (d.place a '' d.tile.support))
    (interior (d.place b '' d.tile.support)) at hd
  rw [← Triangle.support_move, ← Triangle.support_move] at hd
  exact Set.disjoint_left.mp hd hxS hxR

end Tiling

end Erdos633b
