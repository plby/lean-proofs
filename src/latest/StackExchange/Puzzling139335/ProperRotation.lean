import StackExchange.Puzzling139335.ProperRotation.Model
import StackExchange.Puzzling139335.ProperRotation.LargeFirstAngle
import StackExchange.Puzzling139335.ProperRotation.LargeSecondAngle
import StackExchange.Puzzling139335.ProperRotation.AcuteSumBounds
import StackExchange.Puzzling139335.ProperRotation.Complement

/-!
# Proper-rotation crossing inequalities

The source model records finitely many point and support-strip inequalities.
Its first two crossing bounds hold without any assumption on the sum of
the direction angles.  When the angle sum is at most a right angle, all
four crossing bounds follow from the scalar model alone.

For an obtuse sum, the remaining geometric input is made explicit as two
distinct source contacts with each supporting half-plane.  The theorem
`Model.strict_crossing` then supplies all four strict bounds.  No boundary
or topological theorem is assumed in this scalar development.
-/

namespace Puzzling139335.ProperRotation

namespace Model

theorem delta_pos {p : Data} (h : Model p) : 0 < p.delta :=
  add_pos (mul_pos h.s_pos h.d_pos) (mul_pos h.c_pos h.q_pos)

theorem first_v_lower {p : Data} (h : Model p) : -(1 / 2 : ℝ) ≤ p.v := by
  linarith only [h.origin.tangent1_upper]

theorem first_v_upper {p : Data} (h : Model p) :
    p.v ≤ 1 / 2 - p.s - p.c * p.b := by
  nlinarith only [h.right_top.tangent1_lower]

theorem left_support {p : Data} (h : Model p) : p.s * p.a ≤ p.u := by
  nlinarith only [h.left_top.normal1_upper]

theorem right_support {p : Data} (h : Model p) : p.d + p.q * p.b ≤ p.w := by
  nlinarith only [h.right_top.normal2_upper]

theorem second_z_upper {p : Data} (h : Model p) : p.z ≤ 1 / 2 - p.q := by
  nlinarith only [h.base_right.tangent2_lower]

theorem second_z_lower_left {p : Data} (h : Model p) : p.d * p.a - 1 / 2 ≤ p.z := by
  nlinarith only [h.left_top.tangent2_upper]

theorem first_face_upper {p : Data} (h : Model p) :
    p.s * p.u - p.c * p.v + p.c * (1 / 2 - p.b) ≤ 1 / 2 := by
  have hrow := h.face1_plus.y_le_half
  dsimp [Data.y1, Data.bGap] at hrow
  nlinarith only [hrow]

theorem second_face_upper {p : Data} (h : Model p) :
    p.q * p.w + p.d * p.z + p.d * (1 / 2 - p.a) ≤ 1 / 2 := by
  have hrow := h.face2_plus.y_le_half
  dsimp [Data.y2, Data.aGap] at hrow
  nlinarith only [hrow]

theorem first_center_bounds {p : Data} (h : Model p) :
    0 ≤ p.x1 ∧ 0 ≤ p.y1 ∧ p.y1 ≤ 1 / 2 := by
  have hBs := mul_pos h.bGap_pos h.s_pos
  have hBc := mul_pos h.bGap_pos h.c_pos
  refine ⟨?_, ?_, ?_⟩
  · linarith only [h.face1_minus.x_nonneg, hBs]
  · linarith only [h.face1_minus.y_nonneg, hBc]
  · linarith only [h.face1_plus.y_le_half, hBc]

/-- The first intersection numerator is positive for every supported source model. -/
theorem ns_pos {p : Data} (h : Model p) : 0 < p.ns := by
  by_cases hc : p.c ≤ 1 / 2
  · exact ns_pos_of_cos_le_half p.c p.s p.d p.q p.a p.b p.u p.v p.w p.z
      h.c_pos hc h.s_pos h.cs_circle h.d_pos h.q_pos h.dq_circle
      h.a_pos h.b_pos h.first_v_lower h.first_v_upper h.left_support
      h.first_face_upper h.second_face_upper
  · have hc' : (1 / 2 : ℝ) < p.c := lt_of_not_ge hc
    have hd : p.d ≤ 1 / 2 := by
      by_contra! hd'
      have hp := mul_pos (sub_pos.mpr hc') (sub_pos.mpr hd')
      nlinarith only [h.cos_product_le, hc', hd', hp]
    obtain ⟨hx, hy, hy'⟩ := h.first_center_bounds
    exact ns_pos_of_second_cos_le_half
      (c := p.c) (s := p.s) (d := p.d) (q := p.q) (a := p.a)
      (u := p.u) (v := p.v) (w := p.w) (z := p.z) (X := p.x1) (Y := p.y1)
      h.c_pos h.s_pos h.s_lt_one h.d_pos hd h.q_pos h.cs_circle h.dq_circle
      rfl rfl hx hy hy' h.second_z_upper
      (by linarith only [h.second_z_lower_left]) h.second_face_upper

/-- Reflection exchanges the missing upper bound with the proved positivity bound. -/
theorem nt_lt_delta {p : Data} (h : Model p) : p.nt < p.delta := by
  have hf := h.flip.ns_pos
  rw [Data.ns_flip] at hf
  linarith only [hf]

/-- The second source height gives the rational lower bound needed in the acute-sum case. -/
theorem a_gt_two_ninths {p : Data} (h : Model p) (hd : (9 / 10 : ℝ) < p.d) :
    2 / 9 < p.a := by
  have hh := h.second_height
  dsimp [Data.aGap, Data.bGap] at hh
  by_contra! ha
  have hcoef : 0 < 1 - 2 * p.a := by linarith only [ha]
  have hp := mul_pos (sub_pos.mpr hd) hcoef
  nlinarith only [hh, h.b_pos, ha, hp]

/-- Quantitative complementary bounds, after ordering the acute direction angles. -/
theorem ordered_acute_sum_separation {p : Data} (h : Model p)
    (horder : p.c ≤ p.d) (hacute : 0 ≤ p.cosSum) :
    3 / 20 < p.nt ∧ 9 / 100 < p.delta - p.ns := by
  obtain ⟨hc, hs, hd, hsd, hdelta, hsum⟩ :=
    ordered_acute_sum_bounds p.c p.s p.d p.q
      h.c_pos h.s_pos h.d_pos h.q_pos h.cs_circle h.dq_circle
      horder h.cos_product_le hacute
  have ha := h.a_gt_two_ninths hd
  constructor
  · exact nt_lower_bound_of_coarse_bounds p.c p.s p.d p.q p.a p.b p.u p.v p.w p.z
      h.c_pos hc hs h.s_lt_one h.d_pos h.q_pos ha h.b_pos.le hdelta
      h.left_support h.right_support h.first_v_upper h.second_z_upper
  · exact ns_upper_gap_of_coarse_bounds p.c p.s p.d p.q p.a p.b p.u p.v p.w p.z
      h.c_pos hs hd h.q_pos ha h.b_pos.le hsd hsum
      h.left_support h.right_support h.first_v_lower h.second_z_lower_left

/-- All four crossing inequalities in the acute-sum case, without an ordering assumption. -/
theorem crossing_of_cosSum_nonneg {p : Data} (h : Model p) (hacute : 0 ≤ p.cosSum) :
    0 < p.ns ∧ p.ns < p.delta ∧ 0 < p.nt ∧ p.nt < p.delta := by
  refine ⟨h.ns_pos, ?_, ?_, h.nt_lt_delta⟩
  · by_cases horder : p.c ≤ p.d
    · have hc := (h.ordered_acute_sum_separation horder hacute).2
      linarith only [hc]
    · have horder' : p.flip.c ≤ p.flip.d := (lt_of_not_ge horder).le
      have hacute' : 0 ≤ p.flip.cosSum := by simpa only [Data.cosSum_flip] using hacute
      have hc := (h.flip.ordered_acute_sum_separation horder' hacute').1
      rw [Data.nt_flip] at hc
      linarith only [hc]
  · by_cases horder : p.c ≤ p.d
    · have hc := (h.ordered_acute_sum_separation horder hacute).1
      linarith only [hc]
    · have horder' : p.flip.c ≤ p.flip.d := (lt_of_not_ge horder).le
      have hacute' : 0 ≤ p.flip.cosSum := by simpa only [Data.cosSum_flip] using hacute
      have hc := (h.flip.ordered_acute_sum_separation horder' hacute').2
      rw [Data.delta_flip, Data.ns_flip] at hc
      linarith only [hc]

end Model

/-- Two distinct points of the second source lie in the first base's inward
supporting half-plane. This is a scalar consequence of two actual common points. -/
def TwoLeftContacts (p : Data) : Prop :=
  ∃ x₁ y₁ x₂ y₂ : ℝ,
    0 ≤ x₁ ∧ 0 ≤ y₁ ∧ 0 ≤ x₂ ∧ 0 ≤ y₂ ∧
    (x₁, y₁) ≠ (x₂, y₂) ∧
    0 ≤ p.nt - p.delta * x₁ + p.cosSum * y₁ ∧
    0 ≤ p.nt - p.delta * x₂ + p.cosSum * y₂

/-- Two distinct points of the first source lie in the second base's inward
supporting half-plane. -/
def TwoRightContacts (p : Data) : Prop :=
  ∃ x₁ y₁ x₂ y₂ : ℝ,
    x₁ ≤ 1 ∧ 0 ≤ y₁ ∧ x₂ ≤ 1 ∧ 0 ≤ y₂ ∧
    (x₁, y₁) ≠ (x₂, y₂) ∧
    0 ≤ -p.ns + p.delta * x₁ + p.cosSum * y₁ ∧
    0 ≤ -p.ns + p.delta * x₂ + p.cosSum * y₂

namespace Model

/-- In the obtuse-sum case, two actual source contacts with each supporting
half-plane supply precisely the remaining scalar inequalities. -/
theorem crossing_of_cosSum_neg {p : Data} (h : Model p) (hobtuse : p.cosSum < 0)
    (hleft : TwoLeftContacts p) (hright : TwoRightContacts p) :
    0 < p.ns ∧ p.ns < p.delta ∧ 0 < p.nt ∧ p.nt < p.delta := by
  obtain ⟨lx₁, ly₁, lx₂, ly₂, hlx₁, hly₁, hlx₂, hly₂, hlne, hl₁, hl₂⟩ := hleft
  obtain ⟨rx₁, ry₁, rx₂, ry₂, hrx₁, hry₁, hrx₂, hry₂, hrne, hr₁, hr₂⟩ := hright
  exact ⟨h.ns_pos,
    right_numerator_lt_of_two_contacts p.ns p.delta p.cosSum rx₁ ry₁ rx₂ ry₂
      h.delta_pos hobtuse hrx₁ hry₁ hrx₂ hry₂ hrne hr₁ hr₂,
    left_numerator_pos_of_two_contacts p.nt p.delta p.cosSum lx₁ ly₁ lx₂ ly₂
      h.delta_pos hobtuse hlx₁ hly₁ hlx₂ hly₂ hlne hl₁ hl₂,
    h.nt_lt_delta⟩

/-- The complete scalar crossing conclusion, with the geometric common-contact
input kept explicit and separate from the finite source model. -/
theorem strict_crossing {p : Data} (h : Model p)
    (hleft : TwoLeftContacts p) (hright : TwoRightContacts p) :
    0 < p.ns ∧ p.ns < p.delta ∧ 0 < p.nt ∧ p.nt < p.delta := by
  by_cases hacute : 0 ≤ p.cosSum
  · exact h.crossing_of_cosSum_nonneg hacute
  · exact h.crossing_of_cosSum_neg (lt_of_not_ge hacute) hleft hright

/-- The actual Cramer intersection parameters lie strictly inside both unit segments. -/
theorem strict_intersection_parameters {p : Data} (h : Model p)
    (hleft : TwoLeftContacts p) (hright : TwoRightContacts p) :
    0 < p.ns / p.delta ∧ p.ns / p.delta < 1 ∧
      0 < p.nt / p.delta ∧ p.nt / p.delta < 1 := by
  obtain ⟨hns, hns', hnt, hnt'⟩ := h.strict_crossing hleft hright
  refine ⟨div_pos hns h.delta_pos, ?_, div_pos hnt h.delta_pos, ?_⟩
  · exact (div_lt_one h.delta_pos).mpr hns'
  · exact (div_lt_one h.delta_pos).mpr hnt'

end Model

namespace Data

/-- Cramer's rule gives equality of the two parametrized base points. -/
theorem intersection_point_eq (p : Data) (hΔ : p.delta ≠ 0) :
    (p.u + (p.ns / p.delta) * p.c,
      1 / 2 + p.v + (p.ns / p.delta) * p.s) =
    (1 - p.w + (p.nt / p.delta) * p.d,
      1 / 2 - p.z - (p.nt / p.delta) * p.q) := by
  apply Prod.ext
  · field_simp [hΔ]
    dsimp [ns, nt, delta]
    ring
  · field_simp [hΔ]
    dsimp [ns, nt, delta]
    ring

end Data

end Puzzling139335.ProperRotation
