import StackExchange.Puzzling139335.ThreeCorners.AngularOrder

/-!
# Bounds on the second-quadrant inward rays

For an angle between π/2 and π, its cosine is nonpositive and its sine is
nonnegative. The difference of these two coordinates is at most -1, with
equality precisely at the two endpoints.
-/

namespace Puzzling139335.ThreeCorners

/-- Cosine is nonpositive throughout the closed second quadrant. -/
theorem cos_nonpos_of_mem_second_quadrant {θ : ℝ}
    (hθ : θ ∈ Set.Icc (Real.pi / 2) Real.pi) : Real.cos θ ≤ 0 :=
  Real.cos_nonpos_of_pi_div_two_le_of_le hθ.1 (by linarith [hθ.2, Real.pi_pos])

/-- Sine is nonnegative throughout the closed second quadrant. -/
theorem sin_nonneg_of_mem_second_quadrant {θ : ℝ}
    (hθ : θ ∈ Set.Icc (Real.pi / 2) Real.pi) : 0 ≤ Real.sin θ :=
  Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1, Real.pi_pos]) hθ.2

/-- Once the angle is strictly beyond π/2, its cosine is strictly negative. -/
theorem cos_neg_of_half_pi_lt_of_le_pi {θ : ℝ}
    (hlo : Real.pi / 2 < θ) (hhi : θ ≤ Real.pi) : Real.cos θ < 0 :=
  Real.cos_neg_of_pi_div_two_lt_of_lt hlo (by linarith [Real.pi_pos])

/-- The horizontal coordinate of the sum of the two inward rays is at
most -1 in the closed second quadrant. -/
theorem cos_sub_sin_le_neg_one {θ : ℝ}
    (hθ : θ ∈ Set.Icc (Real.pi / 2) Real.pi) : Real.cos θ - Real.sin θ ≤ -1 := by
  have hc := cos_nonpos_of_mem_second_quadrant hθ
  have hs := sin_nonneg_of_mem_second_quadrant hθ
  have hsum : 0 ≤ Real.sin θ - Real.cos θ := sub_nonneg.mpr (hc.trans hs)
  have hsq : (1 : ℝ) ^ 2 ≤ (Real.sin θ - Real.cos θ) ^ 2 := by
    nlinarith [Real.sin_sq_add_cos_sq θ, mul_nonpos_of_nonpos_of_nonneg hc hs]
  have hbound := (sq_le_sq₀ zero_le_one hsum).mp hsq
  linarith

/-- Away from both endpoint angles the horizontal-coordinate bound is strict. -/
theorem cos_sub_sin_lt_neg_one {θ : ℝ}
    (hθ : θ ∈ Set.Ioo (Real.pi / 2) Real.pi) : Real.cos θ - Real.sin θ < -1 := by
  have hc := cos_neg_of_half_pi_lt_of_le_pi hθ.1 hθ.2.le
  have hs : 0 < Real.sin θ :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1, Real.pi_pos]) hθ.2
  have hsum : 0 ≤ Real.sin θ - Real.cos θ := by linarith
  have hsq : (1 : ℝ) ^ 2 < (Real.sin θ - Real.cos θ) ^ 2 := by
    nlinarith [Real.sin_sq_add_cos_sq θ, mul_neg_of_neg_of_pos hc hs]
  have hbound := (sq_lt_sq₀ zero_le_one hsum).mp hsq
  linarith

/-- The bound is attained exactly when one of the inward rays is vertical. -/
theorem cos_sub_sin_eq_neg_one_iff {θ : ℝ}
    (hθ : θ ∈ Set.Icc (Real.pi / 2) Real.pi) :
    Real.cos θ - Real.sin θ = -1 ↔ θ = Real.pi / 2 ∨ θ = Real.pi := by
  constructor
  · intro heq
    by_cases hlo : θ = Real.pi / 2
    · exact Or.inl hlo
    by_cases hhi : θ = Real.pi
    · exact Or.inr hhi
    have hstrict := cos_sub_sin_lt_neg_one
      ⟨lt_of_le_of_ne hθ.1 (Ne.symm hlo), lt_of_le_of_ne hθ.2 hhi⟩
    linarith
  · rintro (rfl | rfl) <;> simp

end Puzzling139335.ThreeCorners
