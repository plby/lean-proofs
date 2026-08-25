import StackExchange.Puzzling139335.N7Geometry.Defs
import Mathlib

/-!
# Metric bounds for the opposite-parity triple-corner configuration

These statements use the actual triangular source region and the explicit thirty-degree
rotation. They do not assume a hull-angle classification or a boundary separation theorem.
-/

namespace Puzzling139335.TripleCornerBounds

open N7Geometry (c)

noncomputable section

/-- The triangular source bound between the horizontal and thirty-degree rays. -/
def triangle : Set Plane :=
  {p | 0 ≤ p 1 ∧ Real.sqrt 3 * p 1 ≤ p 0 ∧ p 0 ≤ 1}

/-- Counterclockwise rotation by thirty degrees about the source origin. -/
def R30 (p : Plane) : Plane :=
  !₂[c * p 0 - p 1 / 2, p 0 / 2 + c * p 1]

/-- The unique source point whose rotated image can lie on the square's top side. -/
def topVertex : Plane := !₂[1, 1 / Real.sqrt 3]

private theorem sqrt_three_pos : 0 < Real.sqrt (3 : ℝ) := by positivity

private theorem sqrt_three_sq : (Real.sqrt (3 : ℝ)) ^ 2 = 3 :=
  Real.sq_sqrt (by norm_num)

private theorem cosine30_pos : 0 < c := div_pos sqrt_three_pos (by norm_num)

private theorem cosine30_lt_one : c < 1 := by
  dsimp [N7Geometry.c]
  nlinarith only [sqrt_three_sq, sq_nonneg (Real.sqrt (3 : ℝ) - 2)]

/-- The source's maximum height is strictly less than the cosine of thirty degrees. -/
theorem inv_sqrt_three_lt_c : 1 / Real.sqrt (3 : ℝ) < c := by
  apply (div_lt_iff₀ sqrt_three_pos).mpr
  dsimp [N7Geometry.c]
  nlinarith only [sqrt_three_sq]

/-- The rotated triangular source does not meet the right side of the square. -/
theorem rotated_x_lt_one {p : Plane} (hp : p ∈ triangle) : (R30 p) 0 < 1 := by
  rcases hp with ⟨hy, hxy, hx⟩
  have hcx := mul_le_mul_of_nonneg_left hx cosine30_pos.le
  change c * p 0 - p 1 / 2 < 1
  nlinarith only [hcx, hy, cosine30_lt_one]

/-- The rotated triangular source lies at height at most one. -/
theorem rotated_y_le_one {p : Plane} (hp : p ∈ triangle) : (R30 p) 1 ≤ 1 := by
  rcases hp with ⟨hy, hxy, hx⟩
  change p 0 / 2 + c * p 1 ≤ 1
  dsimp [N7Geometry.c]
  nlinarith only [hxy, hx]

/-- Reaching height one forces equality in both source-coordinate bounds. -/
theorem rotated_y_eq_one_coordinates {p : Plane} (hp : p ∈ triangle)
    (hrot : (R30 p) 1 = 1) : p 0 = 1 ∧ Real.sqrt 3 * p 1 = 1 := by
  rcases hp with ⟨hy, hxy, hx⟩
  change p 0 / 2 + c * p 1 = 1 at hrot
  dsimp [N7Geometry.c] at hrot
  have hx_one : p 0 = 1 := by nlinarith only [hrot, hxy, hx]
  exact ⟨hx_one, by nlinarith only [hrot, hx_one]⟩

/-- The only source point that can rotate onto the top side is `(1,1/√3)`. -/
theorem eq_topVertex_of_rotated_y_eq_one {p : Plane} (hp : p ∈ triangle)
    (hrot : (R30 p) 1 = 1) : p = topVertex := by
  obtain ⟨hx, hyprod⟩ := rotated_y_eq_one_coordinates hp hrot
  have hy : p 1 = 1 / Real.sqrt 3 :=
    (eq_div_iff (ne_of_gt sqrt_three_pos)).mpr (by simpa only [mul_comm] using hyprod)
  ext i
  fin_cases i
  · simpa [topVertex] using hx
  · simpa [topVertex] using hy

/-- A set contained in the source triangle has no rotated point on the right-side line. -/
theorem not_mem_rotated_image_of_x_eq_one {P : Set Plane} (hP : P ⊆ triangle)
    {v : Plane} (hx : v 0 = 1) : v ∉ R30 '' P := by
  rintro ⟨p, hp, rfl⟩
  have hlt := rotated_x_lt_one (hP hp)
  linarith only [hlt, hx]

/-- A rotated point on the top-side line forces the exceptional source vertex to belong
to the actual source set. No exclusion of that vertex is assumed here. -/
theorem topVertex_mem_of_rotated_image_y_eq_one {P : Set Plane} (hP : P ⊆ triangle)
    {v : Plane} (hv : v ∈ R30 '' P) (hy : v 1 = 1) : topVertex ∈ P := by
  rcases hv with ⟨p, hp, rfl⟩
  have heq := eq_topVertex_of_rotated_y_eq_one (hP hp) hy
  simpa only [heq] using hp

/-- An arm beginning at height `r` with remaining length `1-r` reaches height at least
`c` whenever its vertical direction cosine is at least `c`. -/
theorem support_arm_lower_bound {r cosine : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1)
    (hcosine : c ≤ cosine) : c ≤ r + (1 - r) * cosine := by
  have hremaining := mul_nonneg (sub_nonneg.mpr hr1) (sub_nonneg.mpr hcosine)
  have hrise := mul_nonneg hr0 (sub_nonneg.mpr cosine30_lt_one.le)
  nlinarith only [hremaining, hrise]

/-- The arm-height requirement contradicts the height bound of the triangular source. -/
theorem support_arm_impossible {r cosine Cy : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1)
    (hcosine : c ≤ cosine) (hCy_lower : r + (1 - r) * cosine ≤ Cy)
    (hCy_upper : Cy ≤ 1 / Real.sqrt 3) : False := by
  have hlower := support_arm_lower_bound hr0 hr1 hcosine
  linarith only [hlower, hCy_lower, hCy_upper, inv_sqrt_three_lt_c]

/-- The untranslated-coordinate placement in the exceptional zero-turn case. -/
def straightPlacement (h : ℝ) (p : Plane) : Plane := !₂[p 0, 1 - h + p 1]

/-- The coordinate-exchanging placement in the exceptional zero-turn case. -/
def swappedPlacement (h : ℝ) (p : Plane) : Plane := !₂[1 - h + p 1, p 0]

theorem straightPlacement_corner (h : ℝ) :
    straightPlacement h !₂[1, h] = corner 2 := by
  ext i
  fin_cases i <;> simp [straightPlacement, corner]

theorem swappedPlacement_corner (h : ℝ) :
    swappedPlacement h !₂[1, h] = corner 2 := by
  ext i
  fin_cases i <;> simp [swappedPlacement, corner]

/-- The first exceptional placement sends the origin to a strict point of the left side. -/
theorem straightPlacement_origin_on_open_left {h : ℝ} (hpos : 0 < h) (hlt : h < 1) :
    (straightPlacement h 0) 0 = 0 ∧ 0 < (straightPlacement h 0) 1 ∧
      (straightPlacement h 0) 1 < 1 := by
  refine ⟨rfl, ?_, ?_⟩
  · simpa [straightPlacement] using (show (0 : ℝ) < 1 - h by linarith only [hlt])
  · simpa [straightPlacement] using (show 1 - h < 1 by linarith only [hpos])

/-- The second exceptional placement sends the origin to a strict point of the bottom side. -/
theorem swappedPlacement_origin_on_open_bottom {h : ℝ} (hpos : 0 < h) (hlt : h < 1) :
    (swappedPlacement h 0) 1 = 0 ∧ 0 < (swappedPlacement h 0) 0 ∧
      (swappedPlacement h 0) 0 < 1 := by
  refine ⟨rfl, ?_, ?_⟩
  · simpa [swappedPlacement] using (show (0 : ℝ) < 1 - h by linarith only [hlt])
  · simpa [swappedPlacement] using (show 1 - h < 1 by linarith only [hpos])

end

end Puzzling139335.TripleCornerBounds
