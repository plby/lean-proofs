import StackExchange.Puzzling139335.ThreeCorners.Rays
import Mathlib.Geometry.Euclidean.Angle.Unoriented.Basic

/-!
# The width of a sector between angular rays

Positive radial scaling leaves the unoriented angle unchanged.  On an
ordered interval of length at most `π`, the angle between two unit rays
is therefore the difference of their angular parameters.
-/

open Set

namespace Puzzling139335.N6.TripleSectors.Angles

theorem ray_inner_eq_cos_sub (α β : ℝ) :
    inner ℝ (ThreeCorners.ray α) (ThreeCorners.ray β) =
      Real.cos (β - α) := by
  simp only [Schoenflies.Plane.inner_eq, ThreeCorners.ray_zero,
    ThreeCorners.ray_one, Real.cos_sub]
  ring

/-- When the angular difference lies in `[0, π]`, it is the unoriented angle. -/
theorem ray_angle_eq_sub {α β : ℝ}
    (hαβ : α ≤ β) (hwidth : β - α ≤ Real.pi) :
    InnerProductGeometry.angle (ThreeCorners.ray α) (ThreeCorners.ray β) =
      β - α := by
  rw [InnerProductGeometry.angle, ray_inner_eq_cos_sub,
    ThreeCorners.norm_ray, ThreeCorners.norm_ray, one_mul, div_one]
  exact Real.arccos_cos (sub_nonneg.mpr hαβ) hwidth

/-- The geometric angle of two positively scaled, ordered first-quadrant
rays is exactly the width of the angular interval. -/
theorem angle_eq_sub {r s α β : ℝ} {a b : Plane}
    (hr : 0 < r) (hs : 0 < s)
    (hα : α ∈ Icc (0 : ℝ) (Real.pi / 2))
    (hβ : β ∈ Icc (0 : ℝ) (Real.pi / 2))
    (hαβ : α ≤ β)
    (ha : a = r • ThreeCorners.ray α)
    (hb : b = s • ThreeCorners.ray β) :
    InnerProductGeometry.angle a b = β - α := by
  rw [ha, hb, InnerProductGeometry.angle_smul_left_of_pos _ _ hr,
    InnerProductGeometry.angle_smul_right_of_pos _ _ hs]
  exact ray_angle_eq_sub hαβ (by linarith [hα.1, hβ.2, Real.pi_pos])

/-- The norm-scaled form, convenient for nonzero endpoint vectors. -/
theorem angle_eq_sub_of_norm {α β : ℝ} {a b : Plane}
    (ha0 : a ≠ 0) (hb0 : b ≠ 0)
    (hα : α ∈ Icc (0 : ℝ) (Real.pi / 2))
    (hβ : β ∈ Icc (0 : ℝ) (Real.pi / 2))
    (hαβ : α ≤ β)
    (ha : a = ‖a‖ • ThreeCorners.ray α)
    (hb : b = ‖b‖ • ThreeCorners.ray β) :
    InnerProductGeometry.angle a b = β - α :=
  angle_eq_sub (norm_pos_iff.mpr ha0) (norm_pos_iff.mpr hb0) hα hβ hαβ ha hb

end Puzzling139335.N6.TripleSectors.Angles
