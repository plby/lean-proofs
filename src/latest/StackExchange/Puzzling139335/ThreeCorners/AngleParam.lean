import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse

/-!
# Angles on the left semicircle

A unit vector with nonpositive first coordinate has an angle in the closed
interval from `π / 2` to `3π / 2`. The construction chooses `arccos x` above
the horizontal axis and its reflection below that axis.
-/

namespace Puzzling139335.ThreeCorners

/-- Every unit vector in the left semicircle has an angle between `π / 2`
and `3π / 2`, including both endpoints. -/
theorem exists_angle_left_semicircle {x y : ℝ} (hunit : x ^ 2 + y ^ 2 = 1)
    (hx : x ≤ 0) :
    ∃ θ : ℝ, θ ∈ Set.Icc (Real.pi / 2) (3 * Real.pi / 2) ∧
      Real.cos θ = x ∧ Real.sin θ = y := by
  have hx_lower : -1 ≤ x := by nlinarith [sq_nonneg (x + 1), sq_nonneg y]
  have hx_upper : x ≤ 1 := by linarith
  have hangle_lower : Real.pi / 2 ≤ Real.arccos x := by
    simpa only [Real.arccos_zero] using Real.arccos_le_arccos hx
  have hangle_upper := Real.arccos_le_pi x
  have hcos := Real.cos_arccos hx_lower hx_upper
  have hsin : Real.sin (Real.arccos x) = |y| := by
    rw [Real.sin_arccos, show 1 - x ^ 2 = y ^ 2 by linarith, Real.sqrt_sq_eq_abs]
  by_cases hy : 0 ≤ y
  · refine ⟨Real.arccos x, ⟨hangle_lower, ?_⟩, hcos, ?_⟩
    · linarith [Real.pi_pos]
    · simpa only [abs_of_nonneg hy] using hsin
  · have hy_nonpos : y ≤ 0 := le_of_lt (lt_of_not_ge hy)
    refine ⟨2 * Real.pi - Real.arccos x, ⟨?_, ?_⟩, ?_, ?_⟩
    · linarith [Real.pi_pos]
    · linarith
    · rw [Real.cos_two_pi_sub, hcos]
    · rw [Real.sin_two_pi_sub, hsin, abs_of_nonpos hy_nonpos]
      ring

end Puzzling139335.ThreeCorners
