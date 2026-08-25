import StackExchange.Puzzling139335.ProperRotation.Defs

/-!
# Finite scalar constraints for the supported proper placements

`Model` records source-box and strip containment for the four distinguished source points
and the endpoints of the two supported faces. It has no center-preimage constraints.
-/

namespace Puzzling139335.ProperRotation

namespace Data

noncomputable def aGap (p : Data) : ℝ := 1 / 2 - p.a
noncomputable def bGap (p : Data) : ℝ := 1 / 2 - p.b
def x1 (p : Data) : ℝ := -p.c * p.u - p.s * p.v
def y1 (p : Data) : ℝ := p.s * p.u - p.c * p.v
def x2 (p : Data) : ℝ := p.d * p.w - p.q * p.z
def y2 (p : Data) : ℝ := p.q * p.w + p.d * p.z

@[simp] theorem aGap_flip (p : Data) : p.flip.aGap = p.bGap := rfl
@[simp] theorem bGap_flip (p : Data) : p.flip.bGap = p.aGap := rfl

theorem x1_flip {p : Data} (hcircle : p.d ^ 2 + p.q ^ 2 = 1) :
    p.flip.x1 = 1 - p.x2 := by
  dsimp [x1, x2, flip]
  nlinarith only [hcircle]

@[simp] theorem y1_flip (p : Data) : p.flip.y1 = p.y2 := by
  dsimp [y1, y2, flip]
  ring

theorem x2_flip {p : Data} (hcircle : p.c ^ 2 + p.s ^ 2 = 1) :
    p.flip.x2 = 1 - p.x1 := by
  dsimp [x1, x2, flip]
  nlinarith only [hcircle]

@[simp] theorem y2_flip (p : Data) : p.flip.y2 = p.y1 := by
  dsimp [y1, y2, flip]
  ring

end Data

/-- A point belongs to the source rectangle and the two inverse-image strips. -/
structure PointValid (p : Data) (x y : ℝ) : Prop where
  x_nonneg : 0 ≤ x
  x_le_one : x ≤ 1
  y_nonneg : 0 ≤ y
  y_le_half : y ≤ 1 / 2
  normal1_lower : p.u - 1 ≤ -p.c * x + p.s * y
  normal1_upper : -p.c * x + p.s * y ≤ p.u
  tangent1_lower : p.v - 1 / 2 ≤ -p.s * x - p.c * y
  tangent1_upper : -p.s * x - p.c * y ≤ p.v + 1 / 2
  normal2_lower : p.w - 1 ≤ p.d * x + p.q * y
  normal2_upper : p.d * x + p.q * y ≤ p.w
  tangent2_lower : p.z - 1 / 2 ≤ -p.q * x + p.d * y
  tangent2_upper : -p.q * x + p.d * y ≤ p.z + 1 / 2

namespace PointValid

/-- Reflection in the source's vertical midline exchanges the two strip systems. -/
theorem flip {p : Data} {x y : ℝ} (h : PointValid p x y) :
    PointValid p.flip (1 - x) y := by
  constructor
  · linarith only [h.x_le_one]
  · linarith only [h.x_nonneg]
  · exact h.y_nonneg
  · exact h.y_le_half
  · dsimp [Data.flip]
    nlinarith only [h.normal2_lower]
  · dsimp [Data.flip]
    nlinarith only [h.normal2_upper]
  · dsimp [Data.flip]
    nlinarith only [h.tangent2_upper]
  · dsimp [Data.flip]
    nlinarith only [h.tangent2_lower]
  · dsimp [Data.flip]
    nlinarith only [h.normal1_lower]
  · dsimp [Data.flip]
    nlinarith only [h.normal1_upper]
  · dsimp [Data.flip]
    nlinarith only [h.tangent1_upper]
  · dsimp [Data.flip]
    nlinarith only [h.tangent1_lower]

end PointValid

/-- The finite source and face-endpoint constraints for two proper placements. -/
structure Model (p : Data) : Prop where
  c_pos : 0 < p.c
  s_pos : 0 < p.s
  d_pos : 0 < p.d
  q_pos : 0 < p.q
  cs_circle : p.c ^ 2 + p.s ^ 2 = 1
  dq_circle : p.d ^ 2 + p.q ^ 2 = 1
  a_pos : 0 < p.a
  a_lt_half : p.a < 1 / 2
  b_pos : 0 < p.b
  b_lt_half : p.b < 1 / 2
  origin : PointValid p 0 0
  base_right : PointValid p 1 0
  left_top : PointValid p 0 p.a
  right_top : PointValid p 1 p.b
  face1_minus : PointValid p (p.x1 - p.bGap * p.s) (p.y1 - p.bGap * p.c)
  face1_plus : PointValid p (p.x1 + p.bGap * p.s) (p.y1 + p.bGap * p.c)
  face2_minus : PointValid p (p.x2 + p.aGap * p.q) (p.y2 - p.aGap * p.d)
  face2_plus : PointValid p (p.x2 - p.aGap * p.q) (p.y2 + p.aGap * p.d)

namespace Model

/-- All eight point constraints are preserved by reflection and exchange of the placements. -/
theorem flip {p : Data} (h : Model p) : Model p.flip := by
  refine
    { c_pos := h.d_pos
      s_pos := h.q_pos
      d_pos := h.c_pos
      q_pos := h.s_pos
      cs_circle := h.dq_circle
      dq_circle := h.cs_circle
      a_pos := h.b_pos
      a_lt_half := h.b_lt_half
      b_pos := h.a_pos
      b_lt_half := h.a_lt_half
      origin := ?_
      base_right := ?_
      left_top := ?_
      right_top := ?_
      face1_minus := ?_
      face1_plus := ?_
      face2_minus := ?_
      face2_plus := ?_ }
  · simpa only [sub_self] using h.base_right.flip
  · simpa only [sub_zero] using h.origin.flip
  · change PointValid p.flip 0 p.b
    simpa only [sub_self] using h.right_top.flip
  · change PointValid p.flip 1 p.a
    simpa only [sub_zero] using h.left_top.flip
  · change PointValid p.flip
      (p.flip.x1 - p.aGap * p.q) (p.flip.y1 - p.aGap * p.d)
    rw [Data.x1_flip h.dq_circle, Data.y1_flip]
    convert h.face2_minus.flip using 1
    ring
  · change PointValid p.flip
      (p.flip.x1 + p.aGap * p.q) (p.flip.y1 + p.aGap * p.d)
    rw [Data.x1_flip h.dq_circle, Data.y1_flip]
    convert h.face2_plus.flip using 1
    ring
  · change PointValid p.flip
      (p.flip.x2 + p.bGap * p.s) (p.flip.y2 - p.bGap * p.c)
    rw [Data.x2_flip h.cs_circle, Data.y2_flip]
    convert h.face1_minus.flip using 1
    ring
  · change PointValid p.flip
      (p.flip.x2 - p.bGap * p.s) (p.flip.y2 + p.bGap * p.c)
    rw [Data.x2_flip h.cs_circle, Data.y2_flip]
    convert h.face1_plus.flip using 1
    ring

theorem aGap_pos {p : Data} (h : Model p) : 0 < p.aGap := by
  exact sub_pos.mpr h.a_lt_half

theorem bGap_pos {p : Data} (h : Model p) : 0 < p.bGap := by
  exact sub_pos.mpr h.b_lt_half

theorem s_lt_one {p : Data} (h : Model p) : p.s < 1 := by
  nlinarith only [h.cs_circle, sq_nonneg (p.s - 1), mul_pos h.c_pos h.c_pos]

theorem q_lt_one {p : Data} (h : Model p) : p.q < 1 := by
  nlinarith only [h.dq_circle, sq_nonneg (p.q - 1), mul_pos h.d_pos h.d_pos]

/-- The first supported face and the left source endpoint bound the first gap. -/
theorem first_height {p : Data} (h : Model p) : 2 * p.bGap * p.c ≤ p.aGap := by
  have hu : p.u = p.s * p.y1 - p.c * p.x1 := by
    dsimp [Data.x1, Data.y1]
    linear_combination -p.u * h.cs_circle
  have hsupp : p.s * p.a + p.c * p.x1 ≤ p.s * p.y1 := by
    nlinarith only [h.left_top.normal1_upper, hu]
  have hx : p.bGap * p.s ≤ p.x1 := by
    linarith only [h.face1_minus.x_nonneg]
  have hcx := mul_le_mul_of_nonneg_left hx h.c_pos.le
  have hsy : p.s * (p.a + p.bGap * p.c) ≤ p.s * p.y1 := by
    nlinarith only [hsupp, hcx]
  have hy : p.a + p.bGap * p.c ≤ p.y1 := le_of_mul_le_mul_left hsy h.s_pos
  dsimp [Data.aGap]
  linarith only [hy, h.face1_plus.y_le_half]

/-- The second height bound is the reflection of the first. -/
theorem second_height {p : Data} (h : Model p) : 2 * p.aGap * p.d ≤ p.bGap := by
  exact h.flip.first_height

/-- At least one of the two positive cosines is at most one half. -/
theorem cos_product_le {p : Data} (h : Model p) : 4 * p.c * p.d ≤ 1 := by
  have hprod : (2 * p.bGap * p.c) * (2 * p.aGap * p.d) ≤ p.aGap * p.bGap :=
    mul_le_mul h.first_height h.second_height
      (mul_nonneg (mul_nonneg (by norm_num) h.aGap_pos.le) h.d_pos.le) h.aGap_pos.le
  have hscale : (4 * p.c * p.d) * (p.aGap * p.bGap) ≤ 1 * (p.aGap * p.bGap) := by
    nlinarith only [hprod]
  exact le_of_mul_le_mul_right hscale (mul_pos h.aGap_pos h.bGap_pos)

end Model

end Puzzling139335.ProperRotation
