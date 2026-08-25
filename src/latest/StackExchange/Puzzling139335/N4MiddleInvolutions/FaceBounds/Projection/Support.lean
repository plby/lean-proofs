import StackExchange.Puzzling139335.N4MiddleInvolutions.FaceBounds.Defs

/-! Elementary facts about actual supporting segments and their projections. -/

open Set

namespace Puzzling139335.N4MiddleInvolutions.FaceBounds

theorem supportValue_combo (nx ny u v : ℝ) (a b : Plane) :
    supportValue nx ny (u • a + v • b) =
      u * supportValue nx ny a + v * supportValue nx ny b := by
  change nx * (u * a 0 + v * b 0) + ny * (u * a 1 + v * b 1) = _
  unfold supportValue
  ring

theorem SupportsSegment.level_eq_of_mem_segment {K : Set Plane} {nx ny : ℝ}
    {a b p : Plane} (h : SupportsSegment K nx ny a b) (hp : p ∈ segment ℝ a b) :
    supportValue nx ny p = supportValue nx ny a := by
  obtain ⟨u, v, _, _, huv, rfl⟩ := hp
  rw [supportValue_combo, ← h.level_eq, ← add_mul, huv, one_mul]

/-- Every interior value of a coordinate projection lifts to an actual
point of the open segment. -/
theorem exists_mem_openSegment_of_mem_projection {a b : Plane} {i : Fin 2} {x : ℝ}
    (hx : x ∈ Ioo (min (a i) (b i)) (max (a i) (b i))) :
    ∃ p ∈ openSegment ℝ a b, p i = x := by
  have hab : a i ≠ b i := by
    intro hab
    simp only [hab, min_self, max_self, mem_Ioo] at hx
    exact (lt_asymm hx.1 hx.2)
  let f : Plane →ᵃ[ℝ] ℝ := (EuclideanSpace.proj i).toLinearMap.toAffineMap
  have hx' : x ∈ openSegment ℝ (f a) (f b) := by
    change x ∈ openSegment ℝ (a i) (b i)
    rw [openSegment_eq_Ioo' hab]
    exact hx
  rw [← image_openSegment] at hx'
  exact hx'

/-- A supporting functional attaining its maximum at an interior point
of a segment attains the same value at both endpoints. -/
theorem SupportsSegment.level_eq_of_openSegment_max {K : Set Plane} {nx ny : ℝ}
    {a b c d p : Plane} (h : SupportsSegment K nx ny c d)
    (ha : a ∈ K) (hb : b ∈ K) (hp : p ∈ openSegment ℝ a b)
    (hmax : supportValue nx ny p = supportValue nx ny c) :
    supportValue nx ny a = supportValue nx ny b := by
  obtain ⟨u, v, hu, hv, huv, rfl⟩ := hp
  rw [supportValue_combo] at hmax
  have ha' := h.left_support a ha
  have hb' := h.left_support b hb
  have hweight : (u + v) * supportValue nx ny c = supportValue nx ny c := by
    rw [huv, one_mul]
  have hau : u * (supportValue nx ny c - supportValue nx ny a) = 0 := by
    have hnonneg := mul_nonneg hv.le (sub_nonneg.mpr hb')
    nlinarith [mul_nonneg hu.le (sub_nonneg.mpr ha')]
  have hbv : v * (supportValue nx ny c - supportValue nx ny b) = 0 := by
    have hnonneg := mul_nonneg hu.le (sub_nonneg.mpr ha')
    nlinarith [mul_nonneg hv.le (sub_nonneg.mpr hb')]
  have hac := (mul_eq_zero.mp hau).resolve_left hu.ne'
  have hbc := (mul_eq_zero.mp hbv).resolve_left hv.ne'
  linarith

private theorem eq_of_same_sign_mul_le {r s a b : ℝ} (hsign : 0 < r * s)
    (hr : r * a ≤ r * b) (hs : s * b ≤ s * a) : a = b := by
  rcases mul_pos_iff.mp hsign with ⟨hrpos, hspos⟩ | ⟨hrneg, hsneg⟩
  · exact le_antisymm (le_of_mul_le_mul_left hr hrpos) (le_of_mul_le_mul_left hs hspos)
  · exact le_antisymm ((mul_le_mul_left_of_neg hsneg).mp hs)
      ((mul_le_mul_left_of_neg hrneg).mp hr)

/-- On either the upper or lower supporting graph, a common horizontal
coordinate forces two supporting-segment points to coincide. -/
theorem SupportsSegment.eq_of_same_horizontal_coordinate {K : Set Plane}
    {nx ny mx my : ℝ} {a b c d p q : Plane}
    (h : SupportsSegment K nx ny a b) (g : SupportsSegment K mx my c d)
    (hK : Convex ℝ K) (hsign : 0 < ny * my)
    (hp : p ∈ segment ℝ a b) (hq : q ∈ segment ℝ c d)
    (hcoord : p 0 = q 0) : p = q := by
  have hpK := h.segment_subset hK hp
  have hqK := g.segment_subset hK hq
  have hn := h.left_support q hqK
  have hm := g.left_support p hpK
  rw [← h.level_eq_of_mem_segment hp] at hn
  rw [← g.level_eq_of_mem_segment hq] at hm
  unfold supportValue at hn hm
  rw [hcoord] at hn hm
  have hy : q 1 = p 1 := eq_of_same_sign_mul_le hsign (by linarith) (by linarith)
  ext i
  fin_cases i
  · exact hcoord
  · exact hy.symm

/-- Coordinate interchange as a linear map, for reusing horizontal
projection statements vertically. -/
def swapCoordinates : Plane →ₗ[ℝ] Plane where
  toFun p := !₂[p 1, p 0]
  map_add' p q := by ext i; fin_cases i <;> rfl
  map_smul' r p := by ext i; fin_cases i <;> rfl

@[simp] theorem swapCoordinates_apply_zero (p : Plane) : swapCoordinates p 0 = p 1 := rfl

@[simp] theorem swapCoordinates_apply_one (p : Plane) : swapCoordinates p 1 = p 0 := rfl

@[simp] theorem supportValue_swapCoordinates (nx ny : ℝ) (p : Plane) :
    supportValue ny nx (swapCoordinates p) = supportValue nx ny p := by
  unfold supportValue
  simp only [swapCoordinates_apply_zero, swapCoordinates_apply_one]
  ring

theorem SupportsSegment.swap_coordinates {K : Set Plane} {nx ny : ℝ} {a b : Plane}
    (h : SupportsSegment K nx ny a b) :
    SupportsSegment (swapCoordinates '' K) ny nx (swapCoordinates a) (swapCoordinates b) := by
  refine ⟨mem_image_of_mem _ h.left_mem, mem_image_of_mem _ h.right_mem, ?_, ?_⟩
  · rintro _ ⟨p, hp, rfl⟩
    simpa only [supportValue_swapCoordinates] using h.left_support p hp
  · rintro _ ⟨p, hp, rfl⟩
    simpa only [supportValue_swapCoordinates] using h.right_support p hp

end Puzzling139335.N4MiddleInvolutions.FaceBounds
