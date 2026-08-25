import StackExchange.Puzzling139335.N4Midline.HalfContainment
import StackExchange.Puzzling139335.ThreeCorners.Rays

/-!
# Angle restrictions for a piece in a half-square

The midpoint of the two inward unit rays is the point that an enclosing
unit-square frame sends to the center.  Its first coordinate rules out
the upper-left family of supporting frames and restricts the remaining
frame to the open third quadrant.
-/

open Set

namespace Puzzling139335.N4Midline

noncomputable section

open ThreeCorners

/-- The center of the unit-square frame based at `V` with first inward
ray at angle `θ`. -/
def frameCenter (V : Plane) (θ : ℝ) : Plane :=
  V + (1 / 2 : ℝ) • (ray θ + perpRay θ)

@[simp] theorem frameCenter_zero (V : Plane) (θ : ℝ) :
    frameCenter V θ 0 = V 0 + (Real.cos θ - Real.sin θ) / 2 := by
  simp [frameCenter, ray, perpRay]
  ring

@[simp] theorem frameCenter_one (V : Plane) (θ : ℝ) :
    frameCenter V θ 1 = V 1 + (Real.sin θ + Real.cos θ) / 2 := by
  simp [frameCenter, ray, perpRay]
  ring

theorem interior_leftHalfSquare :
    interior leftHalfSquare =
      {p : Plane | p 0 ∈ Ioo (0 : ℝ) (1 / 2) ∧ p 1 ∈ Ioo (0 : ℝ) 1} := by
  have hzero : (fun p : Plane => p 0) ⁻¹' interior (Icc (0 : ℝ) (1 / 2)) =
      interior ((fun p : Plane => p 0) ⁻¹' Icc (0 : ℝ) (1 / 2)) :=
    IsOpenMap.preimage_interior_eq_interior_preimage
      (PiLp.isOpenMap_apply (p := 2) (β := fun _ : Fin 2 => ℝ) 0)
      (PiLp.continuous_apply 2 (fun _ : Fin 2 => ℝ) 0) _
  have hone : (fun p : Plane => p 1) ⁻¹' interior (Icc (0 : ℝ) 1) =
      interior ((fun p : Plane => p 1) ⁻¹' Icc (0 : ℝ) 1) :=
    IsOpenMap.preimage_interior_eq_interior_preimage
      (PiLp.isOpenMap_apply (p := 2) (β := fun _ : Fin 2 => ℝ) 1)
      (PiLp.continuous_apply 2 (fun _ : Fin 2 => ℝ) 1) _
  change interior (((fun p : Plane => p 0) ⁻¹' Icc (0 : ℝ) (1 / 2)) ∩
    ((fun p : Plane => p 1) ⁻¹' Icc (0 : ℝ) 1)) = _
  rw [interior_inter, ← hzero, ← hone, interior_Icc, interior_Icc]
  rfl

/-- A point interior to any subset of the closed half-square has strict
coordinate bounds. -/
theorem interior_coordinates_of_subset_leftHalfSquare {P : Set Plane}
    (hP : P ⊆ leftHalfSquare) {p : Plane} (hp : p ∈ interior P) :
    p 0 ∈ Ioo (0 : ℝ) (1 / 2) ∧ p 1 ∈ Ioo (0 : ℝ) 1 := by
  have hmem := interior_mono hP hp
  rwa [interior_leftHalfSquare] at hmem

/-- In the closed second quadrant the sum of the nonnegative magnitudes
of the sine and cosine is at least one. -/
theorem cos_sub_sin_le_neg_one {θ : ℝ}
    (hθ : θ ∈ Icc (Real.pi / 2) Real.pi) :
    Real.cos θ - Real.sin θ ≤ -1 := by
  have hs : 0 ≤ Real.sin θ :=
    Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [Real.pi_pos, hθ.1]) hθ.2
  have hc : Real.cos θ ≤ 0 :=
    Real.cos_nonpos_of_pi_div_two_le_of_le hθ.1 (by linarith [hθ.2, Real.pi_pos])
  have hsq : (1 : ℝ) ^ 2 ≤ (Real.sin θ - Real.cos θ) ^ 2 := by
    nlinarith [Real.sin_sq_add_cos_sq θ, mul_nonneg hs (neg_nonneg.mpr hc)]
  have hsum : 1 ≤ Real.sin θ - Real.cos θ :=
    (sq_le_sq₀ (by norm_num) (by linarith : 0 ≤ Real.sin θ - Real.cos θ)).mp hsq
  linarith

theorem frameCenter_zero_nonpos {B : Plane} (hB : B ∈ leftHalfSquare)
    {θ : ℝ} (hθ : θ ∈ Icc (Real.pi / 2) Real.pi) :
    frameCenter B θ 0 ≤ 0 := by
  rw [frameCenter_zero]
  have hb := hB.1.2
  have htrig := cos_sub_sin_le_neg_one hθ
  linarith

theorem frameCenter_not_mem_interior_left {P : Set Plane}
    (hP : P ⊆ leftHalfSquare) {B : Plane} (hB : B ∈ leftHalfSquare)
    {θ : ℝ} (hθ : θ ∈ Icc (Real.pi / 2) Real.pi) :
    frameCenter B θ ∉ interior P := by
  intro hmem
  have hpos := (interior_coordinates_of_subset_leftHalfSquare hP hmem).1.1
  exact (not_lt_of_ge (frameCenter_zero_nonpos hB hθ)) hpos

/-- The endpoint angle `3π/2` places the frame center at or to the right
of the midline and so cannot place it in the interior of the piece. -/
theorem frameCenter_three_pi_div_two_not_mem_interior_left {P : Set Plane}
    (hP : P ⊆ leftHalfSquare) {C : Plane} (hC : C ∈ leftHalfSquare) :
    frameCenter C (3 * Real.pi / 2) ∉ interior P := by
  intro hmem
  have hlt := (interior_coordinates_of_subset_leftHalfSquare hP hmem).1.2
  have hang : (3 * Real.pi / 2 : ℝ) = Real.pi + Real.pi / 2 := by ring
  rw [frameCenter_zero, hang, Real.cos_add_pi_div_two, Real.sin_add_pi_div_two,
    Real.sin_pi, Real.cos_pi] at hlt
  have hc := hC.1.1
  linarith

/-- If the second supporting frame contains the center in the piece,
the ordered angles are forced into the strict ranges needed by the
contact estimates. -/
theorem ordered_angles_of_frameCenter_mem_interior {P : Set Plane}
    (hP : P ⊆ leftHalfSquare) {C : Plane} (hC : C ∈ P)
    {θ φ : ℝ} (hθ : θ ∈ Icc (Real.pi / 2) Real.pi)
    (horder : θ + Real.pi / 2 ≤ φ) (hφ : φ ≤ 3 * Real.pi / 2)
    (hcenter : frameCenter C φ ∈ interior P) :
    φ ∈ Ioo Real.pi (3 * Real.pi / 2) ∧ θ < Real.pi ∧
      φ - θ ∈ Ico (Real.pi / 2) Real.pi := by
  have hφlower : Real.pi ≤ φ := by linarith [hθ.1]
  have hφne : φ ≠ Real.pi := by
    intro heq
    subst φ
    exact frameCenter_not_mem_interior_left hP (hP hC)
      ⟨by linarith [Real.pi_pos], le_rfl⟩ hcenter
  have hφstrict : Real.pi < φ := lt_of_le_of_ne hφlower hφne.symm
  have hφneUpper : φ ≠ 3 * Real.pi / 2 := by
    intro heq
    subst φ
    exact frameCenter_three_pi_div_two_not_mem_interior_left hP (hP hC) hcenter
  have hφupper : φ < 3 * Real.pi / 2 := lt_of_le_of_ne hφ hφneUpper
  refine ⟨⟨hφstrict, hφupper⟩, ?_, ?_, ?_⟩ <;> linarith [hθ.1]

theorem sin_pos_of_left_frame_angle {θ : ℝ}
    (hθ : θ ∈ Ico (Real.pi / 2) Real.pi) : 0 < Real.sin θ :=
  Real.sin_pos_of_pos_of_lt_pi (by linarith [Real.pi_pos, hθ.1]) hθ.2

theorem cos_neg_of_strict_left_frame_angle {θ : ℝ}
    (hθ : θ ∈ Ioo (Real.pi / 2) Real.pi) : Real.cos θ < 0 :=
  Real.cos_neg_of_pi_div_two_lt_of_lt hθ.1 (by linarith [Real.pi_pos, hθ.2])

theorem sin_neg_of_right_frame_angle {φ : ℝ}
    (hφ : φ ∈ Ioo Real.pi (3 * Real.pi / 2)) : Real.sin φ < 0 := by
  have hpos : 0 < Real.sin (φ - Real.pi) :=
    Real.sin_pos_of_pos_of_lt_pi (sub_pos.mpr hφ.1) (by linarith [Real.pi_pos, hφ.2])
  have heq : φ = (φ - Real.pi) + Real.pi := by ring
  rw [heq, Real.sin_add_pi]
  exact neg_neg_of_pos hpos

theorem cos_neg_of_right_frame_angle {φ : ℝ}
    (hφ : φ ∈ Ioo Real.pi (3 * Real.pi / 2)) : Real.cos φ < 0 :=
  Real.cos_neg_of_pi_div_two_lt_of_lt (by linarith [Real.pi_pos, hφ.1])
    (by linarith [hφ.2])

theorem sin_pos_of_frame_angle_gap {δ : ℝ}
    (hδ : δ ∈ Ico (Real.pi / 2) Real.pi) : 0 < Real.sin δ :=
  sin_pos_of_left_frame_angle hδ

theorem cos_neg_of_strict_frame_angle_gap {δ : ℝ}
    (hδ : δ ∈ Ioo (Real.pi / 2) Real.pi) : Real.cos δ < 0 :=
  cos_neg_of_strict_left_frame_angle hδ

end

end Puzzling139335.N4Midline
