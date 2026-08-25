import StackExchange.Puzzling139335.N6.TripleSectors.LocalSector
import StackExchange.Puzzling139335.ThreeCorners.Rays

/-!
# Angular representation of a first-quadrant sector

The unit rays are the existing `ThreeCorners.ray`.  First-quadrant endpoint
vectors have canonical angles in `[0, π / 2]`, and the determinant side tests
become precisely the corresponding open or closed angle interval tests.
-/

open Set

namespace Puzzling139335.N6.TripleSectors.Angles

noncomputable section

open LocalSector

theorem norm_ray (θ : ℝ) : ‖ThreeCorners.ray θ‖ = 1 :=
  ThreeCorners.norm_ray θ

theorem ray_ne_zero (θ : ℝ) : ThreeCorners.ray θ ≠ 0 := by
  intro hzero
  have hn := norm_ray θ
  rw [hzero, norm_zero] at hn
  exact zero_ne_one hn

theorem exists_firstQuadrant_unit_angle {x y : ℝ}
    (hunit : x ^ 2 + y ^ 2 = 1) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    ∃ α : ℝ, α ∈ Icc 0 (Real.pi / 2) ∧ Real.cos α = x ∧ Real.sin α = y := by
  have hxlower : -1 ≤ x := by linarith
  have hxupper : x ≤ 1 := by nlinarith [sq_nonneg y]
  refine ⟨Real.arccos x,
    ⟨Real.arccos_nonneg x, Real.arccos_le_pi_div_two.mpr hx⟩,
    Real.cos_arccos hxlower hxupper, ?_⟩
  rw [Real.sin_arccos, show 1 - x ^ 2 = y ^ 2 by linarith,
    Real.sqrt_sq_eq_abs, abs_of_nonneg hy]

/-- Every nonzero vector in the first quadrant has an angle in its closed
quarter circle, with its Euclidean norm as the scale. -/
theorem exists_firstQuadrant_angle {a : Plane} (ha : a ≠ 0)
    (ha0 : 0 ≤ a 0) (ha1 : 0 ≤ a 1) :
    ∃ α : ℝ, α ∈ Icc 0 (Real.pi / 2) ∧ a = ‖a‖ • ThreeCorners.ray α := by
  have hn : ‖a‖ ≠ 0 := norm_ne_zero_iff.mpr ha
  have hsq : ‖a‖ ^ 2 = a 0 ^ 2 + a 1 ^ 2 := by
    simp only [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two]
  have hunit : (a 0 / ‖a‖) ^ 2 + (a 1 / ‖a‖) ^ 2 = (1 : ℝ) := by
    rw [div_pow, div_pow, ← add_div, ← hsq, div_self (pow_ne_zero 2 hn)]
  obtain ⟨α, hα, hcos, hsin⟩ := exists_firstQuadrant_unit_angle hunit
    (div_nonneg ha0 (norm_nonneg a)) (div_nonneg ha1 (norm_nonneg a))
  refine ⟨α, hα, ?_⟩
  ext i
  fin_cases i
  · change a 0 = ‖a‖ * Real.cos α
    rw [hcos]
    field_simp
  · change a 1 = ‖a‖ * Real.sin α
    rw [hsin]
    field_simp

theorem det_ray_ray (α β : ℝ) :
    det (ThreeCorners.ray α) (ThreeCorners.ray β) = Real.sin (β - α) := by
  change Real.cos α * Real.sin β - Real.sin α * Real.cos β = Real.sin (β - α)
  rw [Real.sin_sub]
  ring

theorem sin_sub_pos_iff {α β : ℝ}
    (hα : α ∈ Icc 0 (Real.pi / 2)) (hβ : β ∈ Icc 0 (Real.pi / 2)) :
    0 < Real.sin (β - α) ↔ α < β := by
  have hzero : (0 : ℝ) ∈ Icc (-(Real.pi / 2)) (Real.pi / 2) := by
    constructor <;> linarith [Real.pi_pos]
  have hsub : β - α ∈ Icc (-(Real.pi / 2)) (Real.pi / 2) := by
    constructor <;> linarith [hα.1, hα.2, hβ.1, hβ.2]
  simpa only [Real.sin_zero, sub_pos] using
    (Real.strictMonoOn_sin.lt_iff_lt hzero hsub)

theorem sin_sub_nonneg_iff {α β : ℝ}
    (hα : α ∈ Icc 0 (Real.pi / 2)) (hβ : β ∈ Icc 0 (Real.pi / 2)) :
    0 ≤ Real.sin (β - α) ↔ α ≤ β := by
  have hzero : (0 : ℝ) ∈ Icc (-(Real.pi / 2)) (Real.pi / 2) := by
    constructor <;> linarith [Real.pi_pos]
  have hsub : β - α ∈ Icc (-(Real.pi / 2)) (Real.pi / 2) := by
    constructor <;> linarith [hα.1, hα.2, hβ.1, hβ.2]
  simpa only [Real.sin_zero, sub_nonneg] using
    (Real.strictMonoOn_sin.le_iff_le hzero hsub)

theorem det_smul_ray_smul_ray (r s α β : ℝ) :
    det (r • ThreeCorners.ray α) (s • ThreeCorners.ray β) =
      r * s * Real.sin (β - α) := by
  change SegmentCrossing.det _ _ = _
  rw [SegmentCrossing.det_smul_left, SegmentCrossing.det_smul_right]
  change r * (s * det (ThreeCorners.ray α) (ThreeCorners.ray β)) = _
  rw [det_ray_ray]
  ring

/-- Positively scaled first-quadrant rays have positive determinant exactly
when their angles are strictly ordered. -/
theorem det_pos_iff_angle_lt {a b : Plane} {α β r s : ℝ}
    (hr : 0 < r) (hs : 0 < s)
    (hα : α ∈ Icc 0 (Real.pi / 2)) (hβ : β ∈ Icc 0 (Real.pi / 2))
    (ha : a = r • ThreeCorners.ray α) (hb : b = s • ThreeCorners.ray β) :
    0 < det a b ↔ α < β := by
  rw [ha, hb, det_smul_ray_smul_ray, mul_pos_iff_of_pos_left (mul_pos hr hs)]
  exact sin_sub_pos_iff hα hβ

theorem det_nonneg_iff_angle_le {a b : Plane} {α β r s : ℝ}
    (hr : 0 < r) (hs : 0 < s)
    (hα : α ∈ Icc 0 (Real.pi / 2)) (hβ : β ∈ Icc 0 (Real.pi / 2))
    (ha : a = r • ThreeCorners.ray α) (hb : b = s • ThreeCorners.ray β) :
    0 ≤ det a b ↔ α ≤ β := by
  rw [ha, hb, det_smul_ray_smul_ray, mul_nonneg_iff_of_pos_left (mul_pos hr hs)]
  exact sin_sub_nonneg_iff hα hβ

theorem angle_lt_of_det_pos {a b : Plane} {α β : ℝ}
    (hα : α ∈ Icc 0 (Real.pi / 2)) (hβ : β ∈ Icc 0 (Real.pi / 2))
    (ha : a = ‖a‖ • ThreeCorners.ray α) (hb : b = ‖b‖ • ThreeCorners.ray β)
    (hdet : 0 < det a b) : α < β := by
  have hane : a ≠ 0 := SegmentCrossing.left_ne_zero_of_det_ne_zero (ne_of_gt hdet)
  have hbne : b ≠ 0 := SegmentCrossing.right_ne_zero_of_det_ne_zero (ne_of_gt hdet)
  exact (det_pos_iff_angle_lt (norm_pos_iff.mpr hane) (norm_pos_iff.mpr hbne)
    hα hβ ha hb).mp hdet

/-- Unit rays lie in the open determinant sector exactly at angles strictly
between its endpoint angles. -/
theorem ray_mem_openSector_iff {a b : Plane} {α β θ r s : ℝ}
    (hr : 0 < r) (hs : 0 < s)
    (hα : α ∈ Icc 0 (Real.pi / 2)) (hβ : β ∈ Icc 0 (Real.pi / 2))
    (hθ : θ ∈ Icc 0 (Real.pi / 2))
    (ha : a = r • ThreeCorners.ray α) (hb : b = s • ThreeCorners.ray β) :
    ThreeCorners.ray θ ∈ openSector a b ↔ α < θ ∧ θ < β := by
  change (0 < det a (ThreeCorners.ray θ) ∧ 0 < det (ThreeCorners.ray θ) b) ↔ _
  rw [det_pos_iff_angle_lt hr zero_lt_one hα hθ ha (by simp),
    det_pos_iff_angle_lt zero_lt_one hs hθ hβ (by simp) hb]

/-- The closed determinant wedge is the closed interval of ray angles. -/
theorem ray_mem_closedSector_iff {a b : Plane} {α β θ r s : ℝ}
    (hr : 0 < r) (hs : 0 < s)
    (hα : α ∈ Icc 0 (Real.pi / 2)) (hβ : β ∈ Icc 0 (Real.pi / 2))
    (hθ : θ ∈ Icc 0 (Real.pi / 2))
    (ha : a = r • ThreeCorners.ray α) (hb : b = s • ThreeCorners.ray β) :
    (0 ≤ det a (ThreeCorners.ray θ) ∧ 0 ≤ det (ThreeCorners.ray θ) b) ↔
      α ≤ θ ∧ θ ≤ β := by
  rw [det_nonneg_iff_angle_le hr zero_lt_one hα hθ ha (by simp),
    det_nonneg_iff_angle_le zero_lt_one hs hθ hβ (by simp) hb]

theorem smul_ray_mem_openSector_iff {a b : Plane} {α β θ r s t : ℝ}
    (hr : 0 < r) (hs : 0 < s) (ht : 0 < t)
    (hα : α ∈ Icc 0 (Real.pi / 2)) (hβ : β ∈ Icc 0 (Real.pi / 2))
    (hθ : θ ∈ Icc 0 (Real.pi / 2))
    (ha : a = r • ThreeCorners.ray α) (hb : b = s • ThreeCorners.ray β) :
    t • ThreeCorners.ray θ ∈ openSector a b ↔ α < θ ∧ θ < β := by
  change (0 < det a (t • ThreeCorners.ray θ) ∧
    0 < det (t • ThreeCorners.ray θ) b) ↔ _
  rw [det_pos_iff_angle_lt hr ht hα hθ ha rfl,
    det_pos_iff_angle_lt ht hs hθ hβ rfl hb]

theorem smul_ray_mem_closedSector_iff {a b : Plane} {α β θ r s t : ℝ}
    (hr : 0 < r) (hs : 0 < s) (ht : 0 < t)
    (hα : α ∈ Icc 0 (Real.pi / 2)) (hβ : β ∈ Icc 0 (Real.pi / 2))
    (hθ : θ ∈ Icc 0 (Real.pi / 2))
    (ha : a = r • ThreeCorners.ray α) (hb : b = s • ThreeCorners.ray β) :
    (0 ≤ det a (t • ThreeCorners.ray θ) ∧
      0 ≤ det (t • ThreeCorners.ray θ) b) ↔ α ≤ θ ∧ θ ≤ β := by
  rw [det_nonneg_iff_angle_le hr ht hα hθ ha rfl,
    det_nonneg_iff_angle_le ht hs hθ hβ rfl hb]

end

end Puzzling139335.N6.TripleSectors.Angles
