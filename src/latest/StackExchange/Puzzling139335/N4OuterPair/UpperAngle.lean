import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Tactic.Linarith

/-!
# An angle for a nonvertical upper unit vector

The parameter is the ordinary real arccosine. Positivity of the second
coordinate rules out both endpoints of its range, and the unit-circle
equation identifies its positive sine without a square-root choice.
-/

namespace Puzzling139335.N4OuterPair

/-- Every upper unit vector with nonzero horizontal component has an angle
strictly between zero and pi and distinct from the vertical angle. -/
theorem exists_upper_angle (c s : ℝ) (hs : 0 < s)
    (hcircle : c ^ 2 + s ^ 2 = 1) (hc : c ≠ 0) :
    ∃ θ : ℝ, 0 < θ ∧ θ < Real.pi ∧ θ ≠ Real.pi / 2 ∧
      Real.cos θ = c ∧ Real.sin θ = s := by
  have hcLower : -1 < c := by
    nlinarith only [hcircle, sq_pos_of_pos hs, sq_nonneg (c + 1)]
  have hcUpper : c < 1 := by
    nlinarith only [hcircle, sq_pos_of_pos hs, sq_nonneg (c - 1)]
  have hθ0 : 0 < Real.arccos c := Real.arccos_pos.mpr hcUpper
  have hθπ : Real.arccos c < Real.pi := Real.arccos_lt_pi.mpr hcLower
  have hcos : Real.cos (Real.arccos c) = c := Real.cos_arccos hcLower.le hcUpper.le
  refine ⟨Real.arccos c, hθ0, hθπ, ?_, hcos, ?_⟩
  · intro hhalf
    exact hc (Real.arccos_eq_pi_div_two.mp hhalf)
  · have hsin : 0 < Real.sin (Real.arccos c) :=
      Real.sin_pos_of_mem_Ioo ⟨hθ0, hθπ⟩
    have hθcircle := Real.cos_sq_add_sin_sq (Real.arccos c)
    rw [hcos] at hθcircle
    apply (sq_eq_sq₀ hsin.le hs.le).mp
    nlinarith only [hcircle, hθcircle]

end Puzzling139335.N4OuterPair
