import StackExchange.Puzzling139335.N4MiddleInvolutions.FaceBounds.Projection.Support
import StackExchange.Puzzling139335.N4MiddleInvolutions.FaceBounds.Projection.Normal

/-!
# Disjoint projections of supporting segments

Distinct unit outward normals in the same open coordinate half-plane give
supporting segments with disjoint open projections onto the other coordinate.
The certificates concern actual segments of a convex set, with no assumption
about a polygonal or ordered boundary.
-/

open Set

namespace Puzzling139335.N4MiddleInvolutions.FaceBounds

theorem SupportsSegment.disjoint_horizontal_projection_of_same_sign
    {K : Set Plane} {nx ny mx my : ℝ} {a b c d : Plane}
    (h : SupportsSegment K nx ny a b) (g : SupportsSegment K mx my c d)
    (hK : Convex ℝ K) (hn : nx ^ 2 + ny ^ 2 = 1) (hm : mx ^ 2 + my ^ 2 = 1)
    (hne : (nx, ny) ≠ (mx, my)) (hsign : 0 < ny * my) :
    Disjoint (Ioo (min (a 0) (b 0)) (max (a 0) (b 0)))
      (Ioo (min (c 0) (d 0)) (max (c 0) (d 0))) := by
  refine Set.disjoint_left.mpr ?_
  intro x hx hy
  have hab : a 0 ≠ b 0 := by
    intro hab
    simp only [hab, min_self, max_self, mem_Ioo] at hx
    exact lt_asymm hx.1 hx.2
  obtain ⟨p, hp, hpx⟩ := exists_mem_openSegment_of_mem_projection hx
  obtain ⟨q, hq, hqx⟩ := exists_mem_openSegment_of_mem_projection hy
  have hpseg := openSegment_subset_segment ℝ a b hp
  have hqseg := openSegment_subset_segment ℝ c d hq
  have hpq : p = q := h.eq_of_same_horizontal_coordinate g hK hsign hpseg hqseg
    (hpx.trans hqx.symm)
  have hmlevel : supportValue mx my a = supportValue mx my b :=
    g.level_eq_of_openSegment_max h.left_mem h.right_mem hp (by
      rw [hpq]
      exact g.level_eq_of_mem_segment hqseg)
  have htn : nx * (b 0 - a 0) + ny * (b 1 - a 1) = 0 := by
    have hlevel := h.level_eq
    unfold supportValue at hlevel
    linarith
  have htm : mx * (b 0 - a 0) + my * (b 1 - a 1) = 0 := by
    unfold supportValue at hmlevel
    linarith
  have hdx : b 0 - a 0 ≠ 0 := sub_ne_zero.mpr hab.symm
  obtain ⟨hnx, hny⟩ := unit_normal_eq_of_tangent_of_same_sign hn hm hsign hdx htn htm
  exact hne (Prod.ext hnx hny)

theorem SupportsSegment.disjoint_vertical_projection_of_same_sign
    {K : Set Plane} {nx ny mx my : ℝ} {a b c d : Plane}
    (h : SupportsSegment K nx ny a b) (g : SupportsSegment K mx my c d)
    (hK : Convex ℝ K) (hn : nx ^ 2 + ny ^ 2 = 1) (hm : mx ^ 2 + my ^ 2 = 1)
    (hne : (nx, ny) ≠ (mx, my)) (hsign : 0 < nx * mx) :
    Disjoint (Ioo (min (a 1) (b 1)) (max (a 1) (b 1)))
      (Ioo (min (c 1) (d 1)) (max (c 1) (d 1))) := by
  have hne' : (ny, nx) ≠ (my, mx) := by
    intro heq
    exact hne (Prod.ext (congrArg Prod.snd heq) (congrArg Prod.fst heq))
  have hd := h.swap_coordinates.disjoint_horizontal_projection_of_same_sign
    g.swap_coordinates (hK.linear_image swapCoordinates)
    (by linarith : ny ^ 2 + nx ^ 2 = 1) (by linarith : my ^ 2 + mx ^ 2 = 1) hne' hsign
  simpa only [swapCoordinates_apply_zero] using hd

theorem SupportsSegment.disjoint_horizontal_projection_of_pos
    {K : Set Plane} {nx ny mx my : ℝ} {a b c d : Plane}
    (h : SupportsSegment K nx ny a b) (g : SupportsSegment K mx my c d)
    (hK : Convex ℝ K) (hn : nx ^ 2 + ny ^ 2 = 1) (hm : mx ^ 2 + my ^ 2 = 1)
    (hne : (nx, ny) ≠ (mx, my)) (hny : 0 < ny) (hmy : 0 < my) :
    Disjoint (Ioo (min (a 0) (b 0)) (max (a 0) (b 0)))
      (Ioo (min (c 0) (d 0)) (max (c 0) (d 0))) :=
  h.disjoint_horizontal_projection_of_same_sign g hK hn hm hne (mul_pos hny hmy)

theorem SupportsSegment.disjoint_horizontal_projection_of_neg
    {K : Set Plane} {nx ny mx my : ℝ} {a b c d : Plane}
    (h : SupportsSegment K nx ny a b) (g : SupportsSegment K mx my c d)
    (hK : Convex ℝ K) (hn : nx ^ 2 + ny ^ 2 = 1) (hm : mx ^ 2 + my ^ 2 = 1)
    (hne : (nx, ny) ≠ (mx, my)) (hny : ny < 0) (hmy : my < 0) :
    Disjoint (Ioo (min (a 0) (b 0)) (max (a 0) (b 0)))
      (Ioo (min (c 0) (d 0)) (max (c 0) (d 0))) :=
  h.disjoint_horizontal_projection_of_same_sign g hK hn hm hne
    (mul_pos_of_neg_of_neg hny hmy)

theorem SupportsSegment.disjoint_vertical_projection_of_pos
    {K : Set Plane} {nx ny mx my : ℝ} {a b c d : Plane}
    (h : SupportsSegment K nx ny a b) (g : SupportsSegment K mx my c d)
    (hK : Convex ℝ K) (hn : nx ^ 2 + ny ^ 2 = 1) (hm : mx ^ 2 + my ^ 2 = 1)
    (hne : (nx, ny) ≠ (mx, my)) (hnx : 0 < nx) (hmx : 0 < mx) :
    Disjoint (Ioo (min (a 1) (b 1)) (max (a 1) (b 1)))
      (Ioo (min (c 1) (d 1)) (max (c 1) (d 1))) :=
  h.disjoint_vertical_projection_of_same_sign g hK hn hm hne (mul_pos hnx hmx)

theorem SupportsSegment.disjoint_vertical_projection_of_neg
    {K : Set Plane} {nx ny mx my : ℝ} {a b c d : Plane}
    (h : SupportsSegment K nx ny a b) (g : SupportsSegment K mx my c d)
    (hK : Convex ℝ K) (hn : nx ^ 2 + ny ^ 2 = 1) (hm : mx ^ 2 + my ^ 2 = 1)
    (hne : (nx, ny) ≠ (mx, my)) (hnx : nx < 0) (hmx : mx < 0) :
    Disjoint (Ioo (min (a 1) (b 1)) (max (a 1) (b 1)))
      (Ioo (min (c 1) (d 1)) (max (c 1) (d 1))) :=
  h.disjoint_vertical_projection_of_same_sign g hK hn hm hne
    (mul_pos_of_neg_of_neg hnx hmx)

theorem SupportsSegment.horizontal_span_eq_zero_of_normal_y_eq_zero
    {K : Set Plane} {nx ny : ℝ} {a b : Plane}
    (h : SupportsSegment K nx ny a b) (hn : nx ^ 2 + ny ^ 2 = 1) (hy : ny = 0) :
    |a 0 - b 0| = 0 := by
  have hnx : nx ≠ 0 := by
    intro hx
    norm_num [hx, hy] at hn
  have hlevel := h.level_eq
  simp only [supportValue, hy, zero_mul, add_zero] at hlevel
  have hab : a 0 = b 0 := mul_left_cancel₀ hnx hlevel
  simp only [hab, sub_self, abs_zero]

theorem SupportsSegment.vertical_span_eq_zero_of_normal_x_eq_zero
    {K : Set Plane} {nx ny : ℝ} {a b : Plane}
    (h : SupportsSegment K nx ny a b) (hn : nx ^ 2 + ny ^ 2 = 1) (hx : nx = 0) :
    |a 1 - b 1| = 0 := by
  have hz := h.swap_coordinates.horizontal_span_eq_zero_of_normal_y_eq_zero
    (by linarith : ny ^ 2 + nx ^ 2 = 1) hx
  simpa only [swapCoordinates_apply_zero] using hz

end Puzzling139335.N4MiddleInvolutions.FaceBounds
