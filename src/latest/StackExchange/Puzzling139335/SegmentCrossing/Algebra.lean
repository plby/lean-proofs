import StackExchange.Puzzling139335.Definitions
import Mathlib.Analysis.Convex.Segment
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

/-!
# Algebra of transverse segment intersections

The determinant and affine parameterization below use the two coordinates of
the Euclidean plane. Cramer's rule identifies the intersection of the supporting
lines; strict bounds on both parameters place it in both open segments.
-/

open Set

namespace Puzzling139335.SegmentCrossing

noncomputable section

/-- The signed determinant of two planar vectors. -/
def det (u v : Plane) : ℝ := u 0 * v 1 - u 1 * v 0

/-- The affine parameterization of the line through `A` and `B`. -/
def point (A B : Plane) (t : ℝ) : Plane := A + t • (B - A)

@[simp] theorem det_zero_left (v : Plane) : det 0 v = 0 := by
  simp [det]

@[simp] theorem det_zero_right (u : Plane) : det u 0 = 0 := by
  simp [det]

@[simp] theorem det_self (u : Plane) : det u u = 0 := by
  simp [det, mul_comm]

theorem det_swap (u v : Plane) : det v u = -det u v := by
  simp only [det]
  ring

theorem det_add_left (u v w : Plane) : det (u + v) w = det u w + det v w := by
  simp only [det, PiLp.add_apply]
  ring

theorem det_add_right (u v w : Plane) : det u (v + w) = det u v + det u w := by
  simp only [det, PiLp.add_apply]
  ring

theorem det_sub_left (u v w : Plane) : det (u - v) w = det u w - det v w := by
  simp only [det, PiLp.sub_apply]
  ring

theorem det_sub_right (u v w : Plane) : det u (v - w) = det u v - det u w := by
  simp only [det, PiLp.sub_apply]
  ring

theorem det_smul_left (t : ℝ) (u v : Plane) : det (t • u) v = t * det u v := by
  simp only [det, PiLp.smul_apply, smul_eq_mul]
  ring

theorem det_smul_right (t : ℝ) (u v : Plane) : det u (t • v) = t * det u v := by
  simp only [det, PiLp.smul_apply, smul_eq_mul]
  ring

theorem left_ne_zero_of_det_ne_zero {u v : Plane} (h : det u v ≠ 0) : u ≠ 0 := by
  intro hu
  simp [hu] at h

theorem right_ne_zero_of_det_ne_zero {u v : Plane} (h : det u v ≠ 0) : v ≠ 0 := by
  intro hv
  simp [hv] at h

/-- Nonzero determinant makes the two coefficients of a vanishing linear
combination zero. -/
theorem eq_zero_of_smul_add_eq_zero {u v : Plane} (h : det u v ≠ 0)
    {s t : ℝ} (hst : s • u + t • v = 0) : s = 0 ∧ t = 0 := by
  have hs : s * det u v = 0 := by
    have := congrArg (fun w => det w v) hst
    simpa [det_add_left, det_smul_left] using this
  have ht : t * det u v = 0 := by
    have := congrArg (fun w => det u w) hst
    simpa [det_add_right, det_smul_right] using this
  exact ⟨(mul_eq_zero.mp hs).resolve_right h, (mul_eq_zero.mp ht).resolve_right h⟩

/-- The determinant identity underlying Cramer's rule. -/
theorem cramer_identity (u v w : Plane) :
    det w v • u - det w u • v = det u v • w := by
  ext i
  fin_cases i <;> simp [det] <;> ring

/-- Cramer's rule for the two affine lines. -/
theorem point_eq_of_cramer {A B C D : Plane}
    (hΔ : det (B - A) (D - C) ≠ 0) :
    point A B (det (C - A) (D - C) / det (B - A) (D - C)) =
      point C D (det (C - A) (B - A) / det (B - A) (D - C)) := by
  have h := congrArg (fun w : Plane => (det (B - A) (D - C))⁻¹ • w)
    (cramer_identity (B - A) (D - C) (C - A))
  simp only [smul_sub, smul_smul, ← div_eq_inv_mul, inv_mul_cancel₀ hΔ, one_smul] at h
  dsimp [point]
  simp only [smul_sub]
  rw [(sub_eq_iff_eq_add).mp h]
  abel

/-- A parameter strictly between zero and one gives a point of the open segment. -/
theorem point_mem_openSegment {A B : Plane} {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    point A B t ∈ openSegment ℝ A B := by
  rw [openSegment_eq_image']
  exact ⟨t, ht, rfl⟩

/-- Equality at two interior parameters is an actual open-segment intersection. -/
theorem openSegment_inter_nonempty_of_point_eq {A B C D : Plane} {t u : ℝ}
    (ht : t ∈ Ioo (0 : ℝ) 1) (hu : u ∈ Ioo (0 : ℝ) 1)
    (h : point A B t = point C D u) :
    (openSegment ℝ A B ∩ openSegment ℝ C D).Nonempty := by
  refine ⟨point A B t, point_mem_openSegment ht, ?_⟩
  rw [h]
  exact point_mem_openSegment hu

/-- Cramer's rule with both parameters in `(0,1)` gives an interior intersection. -/
theorem openSegment_inter_nonempty_of_cramer {A B C D : Plane}
    (hΔ : det (B - A) (D - C) ≠ 0)
    (ht : det (C - A) (D - C) / det (B - A) (D - C) ∈ Ioo (0 : ℝ) 1)
    (hu : det (C - A) (B - A) / det (B - A) (D - C) ∈ Ioo (0 : ℝ) 1) :
    (openSegment ℝ A B ∩ openSegment ℝ C D).Nonempty :=
  openSegment_inter_nonempty_of_point_eq ht hu (point_eq_of_cramer hΔ)

end

end Puzzling139335.SegmentCrossing
