import StackExchange.Puzzling139335.N4MiddleInvolutions.FaceBounds.Normals.Defs
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.Convex.Hull

/-! Actual affine-isometry transport of supporting segments and their outward normals. -/

open Set

namespace Puzzling139335.N4MiddleInvolutions.FaceBounds

/-- A supporting segment remains supporting after passing to the convex
hull: each supporting halfplane is convex. -/
theorem SupportsSegment.convexHull {K : Set Plane} {nx ny : ℝ} {a b : Plane}
    (h : SupportsSegment K nx ny a b) :
    SupportsSegment (convexHull ℝ K) nx ny a b := by
  have hlinear : IsLinearMap ℝ (supportValue nx ny) := by
    constructor
    · intro p q
      simp only [supportValue, PiLp.add_apply]
      ring
    · intro t p
      simp only [supportValue, PiLp.smul_apply, smul_eq_mul]
      ring
  refine ⟨subset_convexHull ℝ K h.left_mem,
    subset_convexHull ℝ K h.right_mem, ?_, ?_⟩
  · intro p hp
    exact convexHull_min (t := {q | supportValue nx ny q ≤ supportValue nx ny a})
      (fun q hq => h.left_support q hq)
      (convex_halfSpace_le hlinear _) hp
  · intro p hp
    exact convexHull_min (t := {q | supportValue nx ny q ≤ supportValue nx ny b})
      (fun q hq => h.right_support q hq)
      (convex_halfSpace_le hlinear _) hp

theorem supportValue_eq_inner (n p : Plane) :
    supportValue (n 0) (n 1) p = inner ℝ n p := by
  simp [supportValue, EuclideanSpace.inner_eq_star_dotProduct, dotProduct,
    Fin.sum_univ_two, mul_comm]

theorem supportValue_vector_eq_inner (nx ny : ℝ) (p : Plane) :
    supportValue nx ny p = inner ℝ (!₂[nx, ny] : Plane) p := by
  simpa using supportValue_eq_inner (!₂[nx, ny] : Plane) p

/-- An affine isometry transports outward normals by its linear isometry. -/
noncomputable def normalImage (e : Plane ≃ᵃⁱ[ℝ] Plane) (nx ny : ℝ) : Plane :=
  e.linearIsometryEquiv (!₂[nx, ny] : Plane)

theorem supportValue_image_sub (e : Plane ≃ᵃⁱ[ℝ] Plane) (nx ny : ℝ)
    (p q : Plane) :
    supportValue (normalImage e nx ny 0) (normalImage e nx ny 1) (e p) -
      supportValue (normalImage e nx ny 0) (normalImage e nx ny 1) (e q) =
        supportValue nx ny p - supportValue nx ny q := by
  have hmap : e p - e q = e.linearIsometryEquiv (p - q) := (e.map_vsub p q).symm
  calc
    _ = inner ℝ (normalImage e nx ny) (e p - e q) := by
      rw [inner_sub_right, supportValue_eq_inner, supportValue_eq_inner]
    _ = inner ℝ (!₂[nx, ny] : Plane) (p - q) := by
      rw [hmap]
      exact e.linearIsometryEquiv.inner_map_map _ _
    _ = _ := by
      rw [inner_sub_right, ← supportValue_vector_eq_inner,
        ← supportValue_vector_eq_inner]

theorem SupportsSegment.image_affineIsometry {K : Set Plane} {nx ny : ℝ}
    {a b : Plane} (h : SupportsSegment K nx ny a b) (e : Plane ≃ᵃⁱ[ℝ] Plane) :
    SupportsSegment (e '' K) (normalImage e nx ny 0) (normalImage e nx ny 1)
      (e a) (e b) := by
  refine ⟨mem_image_of_mem e h.left_mem, mem_image_of_mem e h.right_mem, ?_, ?_⟩
  · rintro _ ⟨p, hp, rfl⟩
    have heq := supportValue_image_sub e nx ny p a
    have hle := h.left_support p hp
    linarith
  · rintro _ ⟨p, hp, rfl⟩
    have heq := supportValue_image_sub e nx ny p b
    have hle := h.right_support p hp
    linarith

theorem normalImage_unit (e : Plane ≃ᵃⁱ[ℝ] Plane) {nx ny : ℝ}
    (hnorm : nx ^ 2 + ny ^ 2 = 1) :
    normalImage e nx ny 0 ^ 2 + normalImage e nx ny 1 ^ 2 = 1 := by
  have hinner := e.linearIsometryEquiv.inner_map_map
    (!₂[nx, ny] : Plane) (!₂[nx, ny] : Plane)
  simp only [← supportValue_eq_inner, supportValue, Matrix.cons_val_zero,
    Matrix.cons_val_one] at hinner
  have heq : normalImage e nx ny 0 ^ 2 + normalImage e nx ny 1 ^ 2 =
      nx ^ 2 + ny ^ 2 := by
    simpa only [normalImage, pow_two] using hinner
  exact heq.trans hnorm

theorem SupportsSegment.normal_dot_direction_eq_zero {K : Set Plane}
    {nx ny : ℝ} {a b : Plane} (h : SupportsSegment K nx ny a b) :
    nx * (a 0 - b 0) + ny * (a 1 - b 1) = 0 := by
  have hlevel := h.level_eq
  unfold supportValue at hlevel
  nlinarith only [hlevel]

theorem SupportsSegment.normal_coordinates_ne_zero_of_oblique {K : Set Plane}
    {nx ny : ℝ} {a b : Plane} (h : SupportsSegment K nx ny a b)
    (hnorm : nx ^ 2 + ny ^ 2 = 1) (hx : a 0 ≠ b 0) (hy : a 1 ≠ b 1) :
    nx ≠ 0 ∧ ny ≠ 0 := by
  have hdot := h.normal_dot_direction_eq_zero
  constructor
  · intro hnx
    rw [hnx, zero_mul, zero_add] at hdot
    have hny := (mul_eq_zero.mp hdot).resolve_right (sub_ne_zero.mpr hy)
    norm_num [hnx, hny] at hnorm
  · intro hny
    rw [hny, zero_mul, add_zero] at hdot
    have hnx := (mul_eq_zero.mp hdot).resolve_right (sub_ne_zero.mpr hx)
    norm_num [hnx, hny] at hnorm

theorem mem_supportingNormalsAtLeast_image_affineIsometry
    (e : Plane ≃ᵃⁱ[ℝ] Plane) {K : Set Plane} {nx ny δ : ℝ}
    (hn : (nx, ny) ∈ supportingNormalsAtLeast K δ) :
    (normalImage e nx ny 0, normalImage e nx ny 1) ∈
      supportingNormalsAtLeast (e '' K) δ := by
  obtain ⟨hnorm, a, b, hface, hlen⟩ := hn
  refine ⟨normalImage_unit e hnorm, e a, e b, hface.image_affineIsometry e, ?_⟩
  simpa only [e.isometry.dist_eq] using hlen

end Puzzling139335.N4MiddleInvolutions.FaceBounds
