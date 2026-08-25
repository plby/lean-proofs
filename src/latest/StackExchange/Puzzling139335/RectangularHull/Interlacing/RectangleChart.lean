import StackExchange.Puzzling139335.Definitions
import Mathlib.Topology.Homeomorph.Lemmas

/-!
# Normalizing an axis rectangle

Positive coordinate scalings give a plane homeomorphism carrying a
nondegenerate axis rectangle to the unit square, with the four corners in
their usual order.
-/

open Set

namespace Puzzling139335.RectangularHull

noncomputable section

/-- The closed rectangle with horizontal bounds `l`, `r` and vertical bounds
`b`, `t`. -/
def axisRectangle (l r b t : ℝ) : Set Plane :=
  {p | l ≤ p 0 ∧ p 0 ≤ r ∧ b ≤ p 1 ∧ p 1 ≤ t}

/-- Translate and independently scale the two coordinates to normalize an
axis rectangle. -/
def rectangleChart (l r b t : ℝ) (hlr : l < r) (hbt : b < t) : Plane ≃ₜ Plane where
  toFun p := Schoenflies.Plane.mk ((p 0 - l) / (r - l)) ((p 1 - b) / (t - b))
  invFun p := Schoenflies.Plane.mk (p 0 * (r - l) + l) (p 1 * (t - b) + b)
  left_inv p := by
    have hw : r - l ≠ 0 := ne_of_gt (sub_pos.mpr hlr)
    have hh : t - b ≠ 0 := ne_of_gt (sub_pos.mpr hbt)
    ext i
    fin_cases i <;> simp [hw, hh]
  right_inv p := by
    have hw : r - l ≠ 0 := ne_of_gt (sub_pos.mpr hlr)
    have hh : t - b ≠ 0 := ne_of_gt (sub_pos.mpr hbt)
    ext i
    fin_cases i <;> simp [hw, hh]
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

@[simp] theorem rectangleChart_apply {l r b t : ℝ} (hlr : l < r) (hbt : b < t)
    (p : Plane) : rectangleChart l r b t hlr hbt p =
      Schoenflies.Plane.mk ((p 0 - l) / (r - l)) ((p 1 - b) / (t - b)) := rfl

@[simp] theorem rectangleChart_symm_apply {l r b t : ℝ} (hlr : l < r) (hbt : b < t)
    (p : Plane) : (rectangleChart l r b t hlr hbt).symm p =
      Schoenflies.Plane.mk (p 0 * (r - l) + l) (p 1 * (t - b) + b) := rfl

private theorem normalized_mem_Icc_iff {a b x : ℝ} (hab : a < b) :
    (x - a) / (b - a) ∈ Icc (0 : ℝ) 1 ↔ a ≤ x ∧ x ≤ b := by
  have hw : 0 < b - a := sub_pos.mpr hab
  rw [mem_Icc, le_div_iff₀ hw, div_le_iff₀ hw]
  simp only [zero_mul, one_mul]
  constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> linarith

/-- A point normalizes into the unit square precisely when it belongs to the
original rectangle. -/
theorem rectangleChart_mem_unitSquare_iff {l r b t : ℝ} (hlr : l < r) (hbt : b < t)
    (p : Plane) : rectangleChart l r b t hlr hbt p ∈ unitSquare ↔
      p ∈ axisRectangle l r b t := by
  change ((p 0 - l) / (r - l) ∈ Icc (0 : ℝ) 1 ∧
    (p 1 - b) / (t - b) ∈ Icc (0 : ℝ) 1) ↔
    l ≤ p 0 ∧ p 0 ≤ r ∧ b ≤ p 1 ∧ p 1 ≤ t
  rw [normalized_mem_Icc_iff hlr, normalized_mem_Icc_iff hbt]
  exact and_assoc

/-- The normalization maps the full closed rectangle onto the unit square. -/
theorem rectangleChart_image_rectangle {l r b t : ℝ} (hlr : l < r) (hbt : b < t) :
    rectangleChart l r b t hlr hbt '' axisRectangle l r b t = unitSquare := by
  ext p
  constructor
  · rintro ⟨q, hq, rfl⟩
    exact (rectangleChart_mem_unitSquare_iff hlr hbt q).mpr hq
  · intro hp
    let e := rectangleChart l r b t hlr hbt
    refine ⟨e.symm p, ?_, e.apply_symm_apply p⟩
    exact (rectangleChart_mem_unitSquare_iff hlr hbt (e.symm p)).mp (by
      change e (e.symm p) ∈ unitSquare
      simpa only [e.apply_symm_apply] using hp)

@[simp] theorem rectangleChart_bottomLeft {l r b t : ℝ} (hlr : l < r) (hbt : b < t) :
    rectangleChart l r b t hlr hbt (Schoenflies.Plane.mk l b) =
      Schoenflies.Plane.mk 0 0 := by
  simp

@[simp] theorem rectangleChart_bottomRight {l r b t : ℝ} (hlr : l < r) (hbt : b < t) :
    rectangleChart l r b t hlr hbt (Schoenflies.Plane.mk r b) =
      Schoenflies.Plane.mk 1 0 := by
  simp [ne_of_gt (sub_pos.mpr hlr)]

@[simp] theorem rectangleChart_topRight {l r b t : ℝ} (hlr : l < r) (hbt : b < t) :
    rectangleChart l r b t hlr hbt (Schoenflies.Plane.mk r t) =
      Schoenflies.Plane.mk 1 1 := by
  simp [ne_of_gt (sub_pos.mpr hlr), ne_of_gt (sub_pos.mpr hbt)]

@[simp] theorem rectangleChart_topLeft {l r b t : ℝ} (hlr : l < r) (hbt : b < t) :
    rectangleChart l r b t hlr hbt (Schoenflies.Plane.mk l t) =
      Schoenflies.Plane.mk 0 1 := by
  simp [ne_of_gt (sub_pos.mpr hbt)]

end

end Puzzling139335.RectangularHull
