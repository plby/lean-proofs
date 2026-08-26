import ErdosProblems.Erdos633b.Geometry
import ErdosProblems.Erdos633b.CornerRays
import Mathlib.Geometry.Euclidean.Angle.Oriented.Rotation

/-! A circle-valued direction coordinate, and common interior points on a ray. -/

namespace Erdos633b

local instance : Fact (Module.finrank ℝ Plane = 2) := ⟨by simp [Plane]⟩

noncomputable def direction (o : Orientation ℝ Plane (Fin 2)) (u p q : Plane) : Real.Angle :=
  o.oangle u (q - p)

theorem direction_sameRay (o : Orientation ℝ Plane (Fin 2)) {u p q r : Plane}
    (hu : u ≠ 0) (hq : q ≠ p) (hr : r ≠ p)
    (h : direction o u p q = direction o u p r) : SameRay ℝ (q - p) (r - p) := by
  have he := o.oangle_sub_left hu (sub_ne_zero.mpr hq) (sub_ne_zero.mpr hr)
  change direction o u p r - direction o u p q = o.oangle (q - p) (r - p) at he
  rw [h, sub_self] at he
  exact o.oangle_eq_zero_iff_sameRay.mp he.symm

theorem direction_of_sameRay (o : Orientation ℝ Plane (Fin 2)) {u p q r : Plane}
    (hu : u ≠ 0) (hq : q ≠ p) (hr : r ≠ p)
    (h : SameRay ℝ (q - p) (r - p)) : direction o u p q = direction o u p r := by
  have he := o.oangle_add hu (sub_ne_zero.mpr hq) (sub_ne_zero.mpr hr)
  rw [o.oangle_eq_zero_iff_sameRay.mpr h, add_zero] at he
  exact he

theorem direction_homothety (o : Orientation ℝ Plane (Fin 2)) (u p q : Plane)
    {r : ℝ} (hr : 0 < r) :
    direction o u p (AffineMap.homothety p r q) = direction o u p q := by
  simp only [direction, AffineMap.homothety_apply, vsub_eq_sub, vadd_eq_add, add_sub_cancel_right]
  exact o.oangle_smul_right_of_pos u (q - p) hr

theorem exists_point_direction (o : Orientation ℝ Plane (Fin 2)) {u : Plane} (hu : u ≠ 0)
    (p : Plane) (a : Real.Angle) : ∃ q, q ≠ p ∧ direction o u p q = a := by
  refine ⟨o.rotation a u + p, ?_, ?_⟩
  · intro h
    have hz : o.rotation a u = 0 := by simpa using h
    exact hu ((o.rotation a).map_eq_zero_iff.mp hz)
  · simp only [direction, add_sub_cancel_right]
    exact o.oangle_rotation_self_right hu a

namespace Triangle

theorem radial_interior_mem_interior (S : Triangle) {p q : Plane}
    (hp : p ∈ S.support) (hq : q ∈ interior S.support) {r : ℝ} (hr : 0 < r) (hr1 : r < 1) :
    AffineMap.homothety p r q ∈ interior S.support := by
  have h := S.support_convex.combo_self_interior_mem_interior hp hq
    (show 0 ≤ 1 - r from by linarith) hr (by ring : (1 - r) + r = 1)
  convert h using 1
  simp only [AffineMap.homothety_apply, vsub_eq_sub, vadd_eq_add]
  module

theorem interiors_inter_of_sameRay (S R : Triangle) {p q r : Plane}
    (hpS : p ∈ S.support) (hpR : p ∈ R.support)
    (hq : q ∈ interior S.support) (hr : r ∈ interior R.support)
    (hqp : q ≠ p) (hrp : r ≠ p) (hray : SameRay ℝ (q - p) (r - p)) :
    (interior S.support ∩ interior R.support).Nonempty := by
  obtain ⟨c, hc, hcray⟩ := hray.exists_pos_left (sub_ne_zero.mpr hqp) (sub_ne_zero.mpr hrp)
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
  have hxS := S.radial_interior_mem_interior hpS hq he he1
  have hxR := R.radial_interior_mem_interior hpR hr (div_pos he hc) ((div_lt_one hc).mpr hec)
  rw [← heq] at hxR
  exact ⟨_, hxS, hxR⟩

end Triangle

end Erdos633b
