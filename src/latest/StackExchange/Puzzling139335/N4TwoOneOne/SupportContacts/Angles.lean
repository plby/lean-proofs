import StackExchange.Puzzling139335.N4TwoOneOne.Defs
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Tactic

/-!
# Angle parameters obtained from actual unit normals

The prefix and suffix parameters below are constructed from the normal
coordinates. Their angular bounds follow from explicit support inequalities.
-/

namespace Puzzling139335.N4TwoOneOne.SupportContacts

noncomputable section

/-- A unit normal in the open first quadrant has an acute angle parameter. -/
theorem exists_acute_angle_of_unit {a b : ℝ}
    (hunit : a ^ 2 + b ^ 2 = 1) (ha : 0 < a) (hb : 0 < b) :
    ∃ φ : ℝ, 0 < φ ∧ φ < Real.pi / 2 ∧ a = Real.cos φ ∧ b = Real.sin φ := by
  have hb1 : b < 1 := by
    nlinarith only [hunit, sq_pos_of_pos ha, sq_nonneg (b - 1)]
  have hsin : Real.sin (Real.arcsin b) = b :=
    Real.sin_arcsin (by linarith only [hb]) hb1.le
  have hcos : 0 ≤ Real.cos (Real.arcsin b) := Real.cos_arcsin_nonneg b
  have hcircle := Real.sin_sq_add_cos_sq (Real.arcsin b)
  rw [hsin] at hcircle
  have hfactor : (a - Real.cos (Real.arcsin b)) *
      (a + Real.cos (Real.arcsin b)) = 0 := by
    nlinarith only [hunit, hcircle]
  have hsum : a + Real.cos (Real.arcsin b) ≠ 0 :=
    ne_of_gt (add_pos_of_pos_of_nonneg ha hcos)
  refine ⟨Real.arcsin b, Real.arcsin_pos.mpr hb,
    Real.arcsin_lt_pi_div_two.mpr hb1, ?_, hsin.symm⟩
  exact sub_eq_zero.mp ((mul_eq_zero.mp hfactor).resolve_right hsum)

/-- The cross-product inequality orders an acute angle against a nonnegative one. -/
theorem acute_angle_le_of_cross_le {φ θ : ℝ}
    (hφ : φ < Real.pi / 2) (hθ : 0 ≤ θ)
    (hcross : Real.sin φ * Real.cos θ ≤ Real.cos φ * Real.sin θ) : φ ≤ θ := by
  by_contra h
  have hdiff0 : 0 < φ - θ := sub_pos.mpr (lt_of_not_ge h)
  have hdiffπ : φ - θ < Real.pi := by
    linarith only [hφ, hθ, Real.pi_pos]
  have hsin := Real.sin_pos_of_pos_of_lt_pi hdiff0 hdiffπ
  rw [Real.sin_sub] at hsin
  linarith only [hcross, hsin]

/-- The incoming support inequality places a positive normal in the prefix interval. -/
theorem exists_prefix_angle {a b θ : ℝ}
    (hθ0 : 0 < θ) (_hθπ : θ < Real.pi / 2)
    (hunit : a ^ 2 + b ^ 2 = 1) (ha : 0 < a) (hb : 0 < b)
    (hbound : b * Real.cos θ ≤ a * Real.sin θ) :
    ∃ φ : ℝ, 0 < φ ∧ φ ≤ θ ∧ a = Real.cos φ ∧ b = Real.sin φ := by
  obtain ⟨φ, hφ0, hφπ, hcos, hsin⟩ := exists_acute_angle_of_unit hunit ha hb
  have hφθ : φ ≤ θ := by
    apply acute_angle_le_of_cross_le hφπ hθ0.le
    simpa only [← hcos, ← hsin] using hbound
  exact ⟨φ, hφ0, hφθ, hcos, hsin⟩

/-- The outgoing support inequality places a negative-horizontal normal in the suffix interval. -/
theorem exists_suffix_angle {a b θ : ℝ}
    (_hθ0 : 0 < θ) (hθπ : θ < Real.pi / 2)
    (hunit : a ^ 2 + b ^ 2 = 1) (ha : a < 0) (hb : 0 < b)
    (hbound : b * Real.sin θ ≤ (-a) * Real.cos θ) :
    ∃ φ : ℝ, θ ≤ φ ∧ φ < Real.pi / 2 ∧ a = -Real.sin φ ∧ b = Real.cos φ := by
  have hunit' : b ^ 2 + (-a) ^ 2 = 1 := by nlinarith only [hunit]
  obtain ⟨φ, hφ0, hφπ, hcos, hsin⟩ :=
    exists_acute_angle_of_unit hunit' hb (neg_pos.mpr ha)
  have hθφ : θ ≤ φ := by
    apply acute_angle_le_of_cross_le hθπ hφ0.le
    simpa only [← hcos, ← hsin, mul_comm] using hbound
  exact ⟨φ, hθφ, hφπ, by linarith only [hsin], hcos⟩

end

end Puzzling139335.N4TwoOneOne.SupportContacts
