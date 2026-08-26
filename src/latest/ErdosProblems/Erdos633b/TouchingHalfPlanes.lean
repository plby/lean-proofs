import ErdosProblems.Erdos633b.EdgeDirectionSectors
import ErdosProblems.Erdos633b.SmallRadial

/-! Disjoint triangle interiors force opposite half-planes at a common
open-edge point. The shared edge line is derived, not assumed. -/

namespace Erdos633b.Triangle

theorem coord_nonpos_of_touching_openEdge (S R : Triangle)
    (hd : Disjoint (interior S.support) (interior R.support)) (i : Fin 3) {p : Plane}
    (hpS : p ∈ S.support) (hpR : p ∈ R.openEdge i) :
    ∀ q ∈ S.support, R.coord i q ≤ 0 := by
  have hinside : ∀ q ∈ interior S.support, R.coord i q ≤ 0 := by
    intro q hq
    by_contra hn
    have hpos : 0 < R.coord i q := lt_of_not_ge hn
    let U : Set Plane := ⋂ k : {k : Fin 3 // k ≠ i}, {x | 0 < R.coord k.val x}
    have hU : IsOpen U := isOpen_iInter_of_finite (fun k =>
      isOpen_lt continuous_const (continuous_barycentric_coord R.affineBasis k.val))
    have hpU : p ∈ U := Set.mem_iInter.mpr (fun k => hpR.2 k.val k.property)
    obtain ⟨r, hr, hr1, hxU⟩ := exists_small_radial p q hU hpU
    have hxS := S.radial_interior_mem_interior hpS hq hr hr1
    have hxR : AffineMap.homothety p r q ∈ interior R.support := by
      apply (R.mem_interior_support_iff_all_coords _).mpr
      intro k
      by_cases hk : k = i
      · rw [hk, AffineMap.homothety_eq_lineMap, R.coord_lineMap, hpR.1, mul_zero, zero_add]
        exact mul_pos hr hpos
      · exact Set.mem_iInter.mp hxU ⟨k, hk⟩
    exact Set.disjoint_left.mp hd hxS hxR
  have hclosed : IsClosed {q : Plane | R.coord i q ≤ 0} :=
    isClosed_le (continuous_barycentric_coord R.affineBasis i) continuous_const
  have hsub : interior S.support ⊆ {q : Plane | R.coord i q ≤ 0} := hinside
  have hclosure := closure_minimal hsub hclosed
  rw [S.closure_interior_support] at hclosure
  exact hclosure

theorem coord_zero_at_touching_edge_endpoints (S R : Triangle)
    (hd : Disjoint (interior S.support) (interior R.support)) (i j : Fin 3) {p : Plane}
    (hpS : p ∈ S.openEdge j) (hpR : p ∈ R.openEdge i) :
    R.coord i (S.points (j + 1)) = 0 ∧ R.coord i (S.points (j + 2)) = 0 := by
  have hnonpos := S.coord_nonpos_of_touching_openEdge R hd i (S.openEdge_subset_edge j hpS).1 hpR
  have hA := hnonpos _ (S.vertex_mem_support (j + 1))
  have hB := hnonpos _ (S.vertex_mem_support (j + 2))
  have hp := hpS
  rw [S.openEdge_eq_openSegment, openSegment_eq_image_lineMap] at hp
  obtain ⟨t, ht, htp⟩ := hp
  have hpzero : R.coord i p = 0 := hpR.1
  rw [← htp, R.coord_lineMap] at hpzero
  have htermA : (1 - t) * R.coord i (S.points (j + 1)) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (by linarith [ht.2]) hA
  have htermB : t * R.coord i (S.points (j + 2)) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos ht.1.le hB
  have htermA0 : (1 - t) * R.coord i (S.points (j + 1)) = 0 := by linarith
  have htermB0 : t * R.coord i (S.points (j + 2)) = 0 := by linarith
  exact ⟨(mul_eq_zero.mp htermA0).resolve_left (by linarith [ht.2]),
    (mul_eq_zero.mp htermB0).resolve_left ht.1.ne'⟩

theorem coord_zero_on_touching_edge (S R : Triangle)
    (hd : Disjoint (interior S.support) (interior R.support)) (i j : Fin 3) {p : Plane}
    (hpS : p ∈ S.openEdge j) (hpR : p ∈ R.openEdge i) :
    ∀ q ∈ S.edge j, R.coord i q = 0 := by
  obtain ⟨hA, hB⟩ := S.coord_zero_at_touching_edge_endpoints R hd i j hpS hpR
  intro q hq
  rw [S.edge_eq_segment, segment_eq_image_lineMap] at hq
  obtain ⟨t, _, rfl⟩ := hq
  rw [R.coord_lineMap, hA, hB, mul_zero, mul_zero, add_zero]

theorem coord_neg_at_touching_opposite_vertex (S R : Triangle)
    (hd : Disjoint (interior S.support) (interior R.support)) (i j : Fin 3) {p : Plane}
    (hpS : p ∈ S.openEdge j) (hpR : p ∈ R.openEdge i) :
    R.coord i (S.points j) < 0 := by
  have hle := S.coord_nonpos_of_touching_openEdge R hd i
    (S.openEdge_subset_edge j hpS).1 hpR _ (S.vertex_mem_support j)
  apply lt_of_le_of_ne hle
  intro hz
  obtain ⟨hA, hB⟩ := S.coord_zero_at_touching_edge_endpoints R hd i j hpS hpR
  have hmap : R.coord i = (0 : Plane →ᵃ[ℝ] ℝ) := by
    apply AffineMap.ext_on (S.span_eq_top (by simp [Plane]))
    rintro _ ⟨k, rfl⟩
    change R.coord i (S.points k) = 0
    rcases (by decide : ∀ j k : Fin 3, k = j ∨ k = j + 1 ∨ k = j + 2) j k with h | h | h
    · exact h ▸ hz
    · exact h ▸ hA
    · exact h ▸ hB
  have he := congrArg (fun f : Plane →ᵃ[ℝ] ℝ => f (R.points i)) hmap
  norm_num [R.coord_vertex] at he

end Erdos633b.Triangle
