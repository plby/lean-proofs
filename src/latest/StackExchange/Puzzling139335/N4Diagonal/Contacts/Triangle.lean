import StackExchange.Puzzling139335.N4Diagonal.Defs
import StackExchange.Puzzling139335.N4Midline.Contacts.Algebra

/-!
# Strict coordinate bounds in the triangular prototype

Every point of the lower half-square except its two outer corners has norm
strictly less than one. The actual prototype contains neither outer corner,
so all of its unit-direction projections are strictly below one.
-/

open Set

namespace Puzzling139335.N4Diagonal

open ThreeCorners

theorem norm_lt_one_of_lowerTriangle {x : Plane} (hx : x ∈ lowerTriangle)
    (hxone : x ≠ corner 1) (hxthree : x ≠ corner 3) : ‖x‖ < 1 := by
  have hnorm : ‖x‖ ^ 2 = x 0 ^ 2 + x 1 ^ 2 := by
    simpa only [Fin.sum_univ_two] using EuclideanSpace.real_norm_sq_eq x
  have hsum : 0 ≤ x 0 + x 1 := add_nonneg hx.1 hx.2.1
  have hsum_sq : (x 0 + x 1) ^ 2 ≤ (1 : ℝ) ^ 2 :=
    (sq_le_sq₀ hsum zero_le_one).mpr hx.2.2
  have hprod : 0 ≤ x 0 * x 1 := mul_nonneg hx.1 hx.2.1
  have hnorm_le : ‖x‖ ≤ 1 :=
    (sq_le_sq₀ (norm_nonneg x) zero_le_one).mp (by nlinarith)
  by_contra hnot
  have hnorm_one : ‖x‖ = 1 := le_antisymm hnorm_le (not_lt.mp hnot)
  have hprod_zero : x 0 * x 1 = 0 := by nlinarith
  rcases mul_eq_zero.mp hprod_zero with hxzero | hyzero
  · have hyone : x 1 = 1 :=
      (sq_eq_sq₀ hx.2.1 zero_le_one).mp (by nlinarith)
    apply hxthree
    ext i
    fin_cases i <;> simp [corner, hxzero, hyone]
  · have hxone' : x 0 = 1 :=
      (sq_eq_sq₀ hx.1 zero_le_one).mp (by nlinarith)
    apply hxone
    ext i
    fin_cases i <;> simp [corner, hxone', hyzero]

namespace Model

theorem norm_lt_one (m : Model) {x : Plane} (hx : x ∈ m.P) : ‖x‖ < 1 := by
  apply norm_lt_one_of_lowerTriangle (m.triangle hx)
  · intro hcorner
    have hj := m.origin_only_corner 1 (hcorner ▸ hx)
    norm_num [Fin.ext_iff] at hj
  · intro hcorner
    have hj := m.origin_only_corner 3 (hcorner ▸ hx)
    norm_num [Fin.ext_iff] at hj

theorem coordinate_lt_one (m : Model) {x : Plane} (hx : x ∈ m.P) (i : Fin 2) :
    x i < 1 := by
  have hcoord : |x i| ≤ ‖x‖ := by simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le x i
  exact lt_of_le_of_lt ((le_abs_self _).trans hcoord) (m.norm_lt_one hx)

theorem ray_inner_lt_one (m : Model) (t : ℝ) {x : Plane} (hx : x ∈ m.P) :
    inner ℝ (ray t) x < 1 := by
  have hinner := real_inner_le_norm (ray t) x
  rw [norm_ray, one_mul] at hinner
  exact hinner.trans_lt (m.norm_lt_one hx)

theorem ray_inner_nonneg (m : Model) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) (Real.pi / 2)) {x : Plane} (hx : x ∈ m.P) :
    0 ≤ inner ℝ (ray t) x := by
  have hcos : 0 ≤ Real.cos t := Real.cos_nonneg_of_mem_Icc
    ⟨by linarith [ht.1, Real.pi_pos], ht.2⟩
  have hsin : 0 ≤ Real.sin t := Real.sin_nonneg_of_nonneg_of_le_pi ht.1
    (by linarith [ht.2, Real.pi_pos])
  rw [Schoenflies.Plane.inner_eq, ray_zero, ray_one]
  exact add_nonneg (mul_nonneg hcos (m.triangle hx).1)
    (mul_nonneg hsin (m.triangle hx).2.1)

/-- The incoming support level `b` is strictly below one. -/
theorem first_scalar_lt_one (m : Model) : inner ℝ (ray m.θ) m.p < 1 :=
  m.ray_inner_lt_one m.θ m.p_mem

/-- The outgoing support level `d` is strictly below one. -/
theorem last_scalar_lt_one (m : Model) : inner ℝ (ray m.β) m.q < 1 :=
  m.ray_inner_lt_one m.β m.q_mem

theorem first_negative_ray_projection_lt_one (m : Model) {x : Plane} (hx : x ∈ m.P) :
    inner ℝ (-ray m.θ) (x - m.p) < 1 := by
  rw [inner_neg_left, inner_sub_right]
  linarith [m.ray_inner_nonneg m.theta_bounds hx, m.first_scalar_lt_one]

theorem last_negative_ray_projection_lt_one (m : Model) {x : Plane} (hx : x ∈ m.P) :
    inner ℝ (-ray m.β) (x - m.q) < 1 := by
  rw [inner_neg_left, inner_sub_right]
  linarith [m.ray_inner_nonneg ⟨m.beta_nonneg, m.beta_bounds.2⟩ hx,
    m.last_scalar_lt_one]

theorem first_negative_ray_contact_empty (m : Model) :
    N4Midline.levelOneContact m.P m.p (-ray m.θ) = ∅ := by
  apply eq_empty_iff_forall_notMem.mpr
  rintro x ⟨hx, hlevel⟩
  exact (ne_of_lt (m.first_negative_ray_projection_lt_one hx)) hlevel

theorem last_negative_ray_contact_empty (m : Model) :
    N4Midline.levelOneContact m.P m.q (-ray m.β) = ∅ := by
  apply eq_empty_iff_forall_notMem.mpr
  rintro x ⟨hx, hlevel⟩
  exact (ne_of_lt (m.last_negative_ray_projection_lt_one hx)) hlevel

theorem first_second_coordinate_zero (m : Model) (hθ : m.θ = 0) : m.p 1 = 0 := by
  have hp := (m.first_support 0 m.origin_mem).1
  simp only [hθ, Schoenflies.Plane.inner_eq, perpRay_zero, perpRay_one,
    Real.sin_zero, Real.cos_zero, PiLp.sub_apply, PiLp.zero_apply] at hp
  linarith [(m.triangle m.p_mem).2.1]

theorem last_first_coordinate_zero (m : Model) (hβ : m.β = Real.pi / 2) : m.q 0 = 0 := by
  have hq := (m.last_support 0 m.origin_mem).2
  simp only [hβ, Schoenflies.Plane.inner_eq, perpRay_zero, perpRay_one,
    Real.sin_pi_div_two, Real.cos_pi_div_two, PiLp.sub_apply, PiLp.zero_apply] at hq
  linarith [(m.triangle m.q_mem).1]

theorem first_perp_contact_empty_at_zero (m : Model) (hθ : m.θ = 0) :
    N4Midline.levelOneContact m.P m.p (perpRay m.θ) = ∅ := by
  apply eq_empty_iff_forall_notMem.mpr
  rintro x ⟨hx, hlevel⟩
  have hcoord := m.coordinate_lt_one hx 1
  have hp := m.first_second_coordinate_zero hθ
  simp only [hθ, Schoenflies.Plane.inner_eq, perpRay_zero, perpRay_one,
    Real.sin_zero, Real.cos_zero, PiLp.sub_apply, hp] at hlevel
  linarith

theorem last_negative_perp_contact_empty_at_half_pi (m : Model)
    (hβ : m.β = Real.pi / 2) :
    N4Midline.levelOneContact m.P m.q (-perpRay m.β) = ∅ := by
  apply eq_empty_iff_forall_notMem.mpr
  rintro x ⟨hx, hlevel⟩
  have hcoord := m.coordinate_lt_one hx 0
  have hq := m.last_first_coordinate_zero hβ
  simp only [hβ, inner_neg_left, Schoenflies.Plane.inner_eq, perpRay_zero, perpRay_one,
    Real.sin_pi_div_two, Real.cos_pi_div_two, PiLp.sub_apply, hq] at hlevel
  linarith

end Model

end Puzzling139335.N4Diagonal
