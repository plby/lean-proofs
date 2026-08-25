import StackExchange.Puzzling139335.SegmentCrossing.Algebra
import Mathlib.Geometry.Euclidean.Angle.Unoriented.Basic

/-!
# Matching two independent boundary rays

An origin-fixing Euclidean congruence cannot send two independent vectors
to the same ray.  Consequently, if each image is on one of two positive
rays, the two images match those rays in one of the two possible orders.
The resulting unoriented opening angle is unchanged.
-/

open Set

namespace Puzzling139335.N6.TripleSectors.Angles.Congruence

noncomputable section

open SegmentCrossing InnerProductGeometry

theorem linearIsometryEquiv_apply_of_fix_zero
    (e : Plane ≃ᵃⁱ[ℝ] Plane) (hzero : e 0 = 0) (x : Plane) :
    e.linearIsometryEquiv x = e x := by
  simpa only [vsub_eq_sub, sub_zero, hzero] using e.map_vsub x 0

theorem angle_map_of_fix_zero (e : Plane ≃ᵃⁱ[ℝ] Plane)
    (hzero : e 0 = 0) (a b : Plane) : angle (e a) (e b) = angle a b := by
  simpa only [LinearIsometryEquiv.coe_toLinearIsometry,
    linearIsometryEquiv_apply_of_fix_zero e hzero] using
    e.linearIsometryEquiv.toLinearIsometry.angle_map a b

theorem norm_map_of_fix_zero (e : Plane ≃ᵃⁱ[ℝ] Plane)
    (hzero : e 0 = 0) (a : Plane) : ‖e a‖ = ‖a‖ := by
  rw [← linearIsometryEquiv_apply_of_fix_zero e hzero]
  exact e.linearIsometryEquiv.norm_map a

/-- A positive multiple determines the same unit direction, so the actual
congruence sends normalized endpoints exactly to normalized endpoints. -/
theorem map_normalized_of_pos_smul (e : Plane ≃ᵃⁱ[ℝ] Plane)
    (hzero : e 0 = 0) {a c : Plane} {s : ℝ} (hs : 0 < s)
    (ha : e a = s • c) : e (‖a‖⁻¹ • a) = ‖c‖⁻¹ • c := by
  have hnorm : ‖a‖ = s * ‖c‖ := by
    rw [← norm_map_of_fix_zero e hzero a, ha, norm_smul, Real.norm_eq_abs,
      abs_of_pos hs]
  rw [← linearIsometryEquiv_apply_of_fix_zero e hzero, map_smul,
    linearIsometryEquiv_apply_of_fix_zero e hzero, ha, smul_smul, hnorm]
  congr 1
  rw [mul_inv_rev, mul_assoc, inv_mul_cancel₀ hs.ne', mul_one]

theorem not_same_image_ray (e : Plane ≃ᵃⁱ[ℝ] Plane)
    (hzero : e 0 = 0) {a b c : Plane} (hab : det a b ≠ 0)
    {s t : ℝ} (hs : s ≠ 0) (ha : e a = s • c) (hb : e b = t • c) : False := by
  have hparallel : t • a = s • b := by
    apply e.linearIsometryEquiv.injective
    rw [map_smul, map_smul]
    simp only [linearIsometryEquiv_apply_of_fix_zero e hzero, ha, hb,
      smul_smul, mul_comm]
  have hdet := congrArg (det a) hparallel
  simp only [det_smul_right, det_self, mul_zero] at hdet
  exact hab ((mul_eq_zero.mp hdet.symm).resolve_left hs)

/-- No order on the two target rays is presupposed. -/
theorem image_rays_match (e : Plane ≃ᵃⁱ[ℝ] Plane) (hzero : e 0 = 0)
    {a b c d : Plane} (hab : det a b ≠ 0)
    (ha : (∃ s : ℝ, 0 < s ∧ e a = s • c) ∨
      (∃ s : ℝ, 0 < s ∧ e a = s • d))
    (hb : (∃ t : ℝ, 0 < t ∧ e b = t • c) ∨
      (∃ t : ℝ, 0 < t ∧ e b = t • d)) :
    (∃ s t : ℝ, 0 < s ∧ 0 < t ∧ e a = s • c ∧ e b = t • d) ∨
      (∃ s t : ℝ, 0 < s ∧ 0 < t ∧ e a = s • d ∧ e b = t • c) := by
  rcases ha with ⟨s, hs, ha⟩ | ⟨s, hs, ha⟩ <;>
    rcases hb with ⟨t, ht, hb⟩ | ⟨t, ht, hb⟩
  · exact (not_same_image_ray e hzero hab hs.ne' ha hb).elim
  · exact Or.inl ⟨s, t, hs, ht, ha, hb⟩
  · exact Or.inr ⟨s, t, hs, ht, ha, hb⟩
  · exact (not_same_image_ray e hzero hab hs.ne' ha hb).elim

/-- The unordered endpoint pair on the unit circle is transported exactly. -/
theorem normalized_image_rays_match (e : Plane ≃ᵃⁱ[ℝ] Plane)
    (hzero : e 0 = 0) {a b c d : Plane} (hab : det a b ≠ 0)
    (ha : (∃ s : ℝ, 0 < s ∧ e a = s • c) ∨
      (∃ s : ℝ, 0 < s ∧ e a = s • d))
    (hb : (∃ t : ℝ, 0 < t ∧ e b = t • c) ∨
      (∃ t : ℝ, 0 < t ∧ e b = t • d)) :
    (e (‖a‖⁻¹ • a) = ‖c‖⁻¹ • c ∧ e (‖b‖⁻¹ • b) = ‖d‖⁻¹ • d) ∨
      (e (‖a‖⁻¹ • a) = ‖d‖⁻¹ • d ∧ e (‖b‖⁻¹ • b) = ‖c‖⁻¹ • c) := by
  rcases image_rays_match e hzero hab ha hb with
    ⟨s, t, hs, ht, ha, hb⟩ | ⟨s, t, hs, ht, ha, hb⟩
  · exact Or.inl ⟨map_normalized_of_pos_smul e hzero hs ha,
      map_normalized_of_pos_smul e hzero ht hb⟩
  · exact Or.inr ⟨map_normalized_of_pos_smul e hzero hs ha,
      map_normalized_of_pos_smul e hzero ht hb⟩

/-- Positive ray membership, derived from the actual germs elsewhere, is
sufficient to identify the unoriented sector angle under congruence. -/
theorem angle_eq_of_image_rays (e : Plane ≃ᵃⁱ[ℝ] Plane) (hzero : e 0 = 0)
    {a b c d : Plane} (hab : det a b ≠ 0)
    (ha : (∃ s : ℝ, 0 < s ∧ e a = s • c) ∨
      (∃ s : ℝ, 0 < s ∧ e a = s • d))
    (hb : (∃ t : ℝ, 0 < t ∧ e b = t • c) ∨
      (∃ t : ℝ, 0 < t ∧ e b = t • d)) : angle a b = angle c d := by
  rw [← angle_map_of_fix_zero e hzero]
  rcases image_rays_match e hzero hab ha hb with
    ⟨s, t, hs, ht, ha, hb⟩ | ⟨s, t, hs, ht, ha, hb⟩
  · rw [ha, hb, angle_smul_left_of_pos _ _ hs, angle_smul_right_of_pos _ _ ht]
  · rw [ha, hb, angle_smul_left_of_pos _ _ hs, angle_smul_right_of_pos _ _ ht,
      angle_comm]

end

end Puzzling139335.N6.TripleSectors.Angles.Congruence
