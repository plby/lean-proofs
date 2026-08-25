import StackExchange.Puzzling139335.N4HalfLeg.Defs

/-!
# Vertical budgets for actual acute supporting faces

Each lower endpoint lies above the actual right-side source contact. Two
faces with distinct acute unit normals are vertically ordered by their
support inequalities. Their vertical spans therefore share the same
half-square height budget, without a convex-boundary ordering argument.
-/

open Set

namespace Puzzling139335.N4HalfLeg

open SourceFaceBridge

/-- Distinct unit normals with positive first coordinate have nonzero
determinant. The excluded opposite-normal case cannot have that sign. -/
theorem normal_det_ne_zero {c₁ s₁ c₂ s₂ : ℝ}
    (hc₁ : 0 < c₁) (hc₂ : 0 < c₂)
    (hunit₁ : c₁ ^ 2 + s₁ ^ 2 = 1) (hunit₂ : c₂ ^ 2 + s₂ ^ 2 = 1)
    (hne : (c₁, s₁) ≠ (c₂, s₂)) : c₁ * s₂ - s₁ * c₂ ≠ 0 := by
  intro hdet
  have hcross : c₁ * s₂ = s₁ * c₂ := sub_eq_zero.mp hdet
  have hcrossSq := congrArg (fun t : ℝ => t ^ 2) hcross
  have hunit₁mul := congrArg (fun t : ℝ => c₂ ^ 2 * t) hunit₁
  have hunit₂mul := congrArg (fun t : ℝ => c₁ ^ 2 * t) hunit₂
  have hcSq : c₁ ^ 2 = c₂ ^ 2 := by
    nlinarith only [hcrossSq, hunit₁mul, hunit₂mul]
  have hc : c₁ = c₂ := (sq_eq_sq₀ hc₁.le hc₂.le).mp hcSq
  have hs : s₁ = s₂ := by
    apply mul_left_cancel₀ hc₁.ne'
    rw [← hc] at hdet
    nlinarith only [hdet]
  exact hne (Prod.ext hc hs)

namespace SourceFace

variable {P : Set Plane} {c s c₁ s₁ c₂ s₂ b : ℝ}

/-- An acute supporting point lies at least as high as any actual source
point on the right side of the half-square. -/
theorem lower_height_ge (F : SourceFace P c s) (hP : P ⊆ lowerHalfSquare)
    (hB : point 1 b ∈ P) : b ≤ F.lower 1 := by
  have hsupport := F.lower_support.2 (point 1 b) hB
  simp only [point_zero, point_one, mul_one] at hsupport
  have hx : c * F.lower 0 ≤ c := by
    simpa only [mul_one] using
      mul_le_mul_of_nonneg_left (hP F.lower_mem).1.2 F.c_pos.le
  have hy : s * b ≤ s * F.lower 1 := by linarith only [hsupport, hx]
  exact le_of_mul_le_mul_left hy F.s_pos

/-- One actual support span fits between the right-side contact height
and the top of the lower half-square. -/
theorem vertical_budget (F : SourceFace P c s) (hP : P ⊆ lowerHalfSquare)
    (hB : point 1 b ∈ P) : c * F.length ≤ (1 / 2 : ℝ) - b := by
  linarith only [F.vertical_span, F.lower_height_ge hP hB,
    (hP F.upper_mem).2.2]

/-- Positively ordered acute normals put the entire first support span
below the lower endpoint of the second support span. -/
theorem upper_height_le_lower_of_det_pos (F : SourceFace P c₁ s₁)
    (G : SourceFace P c₂ s₂) (hdet : 0 < c₁ * s₂ - s₁ * c₂) :
    F.upper 1 ≤ G.lower 1 := by
  have hF := F.upper_support.2 G.lower G.lower_mem
  have hG := G.lower_support.2 F.upper F.upper_mem
  have hproj : 0 ≤ (c₁ * s₂ - s₁ * c₂) * (G.lower 1 - F.upper 1) := by
    nlinarith only [mul_le_mul_of_nonneg_left hF G.c_pos.le,
      mul_le_mul_of_nonneg_left hG F.c_pos.le]
  exact sub_nonneg.mp (nonneg_of_mul_nonneg_right hproj hdet)

/-- Two support spans with distinct acute normals share one vertical
budget. This follows directly from their actual endpoint supports. -/
theorem pair_vertical_budget (F : SourceFace P c₁ s₁) (G : SourceFace P c₂ s₂)
    (hP : P ⊆ lowerHalfSquare) (hB : point 1 b ∈ P)
    (hne : (c₁, s₁) ≠ (c₂, s₂)) :
    c₁ * F.length + c₂ * G.length ≤ (1 / 2 : ℝ) - b := by
  have hdet := normal_det_ne_zero F.c_pos G.c_pos F.normal_unit G.normal_unit hne
  rcases lt_or_gt_of_ne hdet with hneg | hpos
  · have horder : G.upper 1 ≤ F.lower 1 :=
      G.upper_height_le_lower_of_det_pos F (by nlinarith only [hneg])
    linarith only [F.vertical_span, G.vertical_span, horder,
      G.lower_height_ge hP hB, (hP F.upper_mem).2.2]
  · have horder := F.upper_height_le_lower_of_det_pos G hpos
    linarith only [F.vertical_span, G.vertical_span, horder,
      F.lower_height_ge hP hB, (hP G.upper_mem).2.2]

/-- One acute face cannot have the contact length demanded by the two
remaining half-leg intervals. -/
theorem not_length_ge (F : SourceFace P c s) (hP : P ⊆ lowerHalfSquare)
    (hB : point 1 b ∈ P) (hb : b < (1 / 2 : ℝ))
    (hlength : 1 - 2 * b ≤ F.length) : False := by
  have hbudget := F.vertical_budget hP hB
  have hstrict := mul_lt_mul_of_pos_right F.c_gt_four_fifths F.length_pos
  linarith only [hbudget, hstrict, hlength, hb]

/-- Two distinct acute faces cannot jointly have the required remaining
contact length, because both project by more than four fifths. -/
theorem not_total_length_ge (F : SourceFace P c₁ s₁) (G : SourceFace P c₂ s₂)
    (hP : P ⊆ lowerHalfSquare) (hB : point 1 b ∈ P) (hb : b < (1 / 2 : ℝ))
    (hne : (c₁, s₁) ≠ (c₂, s₂))
    (hlength : 1 - 2 * b ≤ F.length + G.length) : False := by
  have hbudget := F.pair_vertical_budget G hP hB hne
  have hstrictF := mul_lt_mul_of_pos_right F.c_gt_four_fifths F.length_pos
  have hstrictG := mul_lt_mul_of_pos_right G.c_gt_four_fifths G.length_pos
  linarith only [hbudget, hstrictF, hstrictG, hlength, hb]

end SourceFace

end Puzzling139335.N4HalfLeg
