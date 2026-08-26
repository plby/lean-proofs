import ErdosProblems.Erdos633b.BoundaryAngleImages

/-! A ray through opposite-edge interior points enters both triangle interiors.
The common point is constructed with an explicit positive scale. -/

namespace Erdos633b.Triangle

theorem radial_openEdge_mem_interior (S : Triangle) (j : Fin 3) {q : Plane}
    (hq : q ∈ S.openEdge j) {r : ℝ} (hr : 0 < r) (hr1 : r < 1) :
    AffineMap.homothety (S.points j) r q ∈ interior S.support := by
  apply (S.mem_interior_support_iff_all_coords _).mpr
  intro k
  by_cases hk : k = j
  · rw [hk, S.coord_homothety_vertex, S.coord_vertex, if_pos rfl, hq.1]
    linarith
  · rw [S.coord_homothety_vertex, S.coord_vertex, if_neg hk, sub_zero, add_zero]
    exact mul_pos hr (hq.2 k hk)

theorem interiors_inter_of_sameRay_openEdges (S R : Triangle) (j k : Fin 3)
    {p q r : Plane} (hS : S.points j = p) (hR : R.points k = p)
    (hq : q ∈ S.openEdge j) (hr : r ∈ R.openEdge k)
    (hray : SameRay ℝ (q - p) (r - p)) :
    (interior S.support ∩ interior R.support).Nonempty := by
  have hq0 : q - p ≠ 0 := sub_ne_zero.mpr (hS ▸
    S.ne_vertex_of_mem_edge j (S.openEdge_subset_edge j hq))
  have hr0 : r - p ≠ 0 := sub_ne_zero.mpr (hR ▸
    R.ne_vertex_of_mem_edge k (R.openEdge_subset_edge k hr))
  obtain ⟨c, hc, hcray⟩ := hray.exists_pos_left hq0 hr0
  let e : ℝ := min 1 c / 2
  have he : 0 < e := div_pos (lt_min zero_lt_one hc) (by norm_num)
  have he1 : e < 1 := by
    have hh := min_le_left (1 : ℝ) c
    dsimp [e]
    linarith
  have hec : e < c := by
    have hh := min_le_right (1 : ℝ) c
    dsimp [e]
    linarith
  have heq : AffineMap.homothety p e q = AffineMap.homothety p (e / c) r := by
    simp only [AffineMap.homothety_apply, vsub_eq_sub, vadd_eq_add]
    rw [← hcray, smul_smul, div_mul_cancel₀ e hc.ne']
  have hxS := S.radial_openEdge_mem_interior j hq he he1
  have hxR := R.radial_openEdge_mem_interior k hr (div_pos he hc) ((div_lt_one hc).mpr hec)
  rw [hS] at hxS
  rw [hR, ← heq] at hxR
  exact ⟨_, hxS, hxR⟩

end Erdos633b.Triangle
