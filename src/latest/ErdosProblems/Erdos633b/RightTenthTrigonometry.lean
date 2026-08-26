import ErdosProblems.Erdos633b.SharedAngleMetric

/-! Exact algebraic and order data for the pi/10 right tile and a second
real root of its Eisenstein quartic. -/

namespace Erdos633b

theorem tenth_sine_pos : 0 < Real.sin (Real.pi / 10) := by
  apply Real.sin_pos_of_pos_of_lt_pi <;> linarith [Real.pi_pos]

theorem tenth_sine_lt_half : Real.sin (Real.pi / 10) < 1 / 2 := by
  have h := Real.sin_lt_sin_of_lt_of_le_pi_div_two
    (show -(Real.pi / 2) ≤ Real.pi / 10 by linarith [Real.pi_pos])
    (show Real.pi / 6 ≤ Real.pi / 2 by linarith [Real.pi_pos])
    (show Real.pi / 10 < Real.pi / 6 by linarith [Real.pi_pos])
  simpa only [Real.sin_pi_div_six] using h

theorem tenth_cosine_pos : 0 < Real.cos (Real.pi / 10) := by
  apply Real.cos_pos_of_mem_Ioo
  constructor <;> linarith [Real.pi_pos]

theorem tenth_sine_quadratic :
    4 * Real.sin (Real.pi / 10) ^ 2 + 2 * Real.sin (Real.pi / 10) = 1 := by
  have h := sin_three_mul_eq (Real.pi / 10)
  rw [show 3 * (Real.pi / 10) = Real.pi / 2 - 2 * (Real.pi / 10) by ring,
    Real.sin_pi_div_two_sub, Real.cos_two_mul] at h
  have hf : (Real.sin (Real.pi / 10) - 1) *
      (4 * Real.sin (Real.pi / 10) ^ 2 + 2 * Real.sin (Real.pi / 10) - 1) = 0 := by
    linear_combination h - 2 * Real.sin_sq_add_cos_sq (Real.pi / 10)
  have hn : Real.sin (Real.pi / 10) - 1 ≠ 0 := by linarith [tenth_sine_lt_half]
  have hz := (mul_eq_zero.mp hf).resolve_left hn
  linarith

theorem tenth_polynomial_data (a b : ℝ) (hq : 4 * a ^ 2 + 2 * a = 1)
    (hu : a ^ 2 + b ^ 2 = 1) :
    a = ((2 * b) ^ 2 - 3) / 2 ∧
      (2 * b) ^ 4 - 5 * (2 * b) ^ 2 + 5 = 0 := by
  have he : (2 * b) ^ 2 = 3 + 2 * a := by nlinarith
  constructor
  · linarith
  · have hs := congrArg (fun x : ℝ => x ^ 2) he
    nlinarith

theorem tenth_sine_polynomial : Real.sin (Real.pi / 10) =
    ((2 * Real.cos (Real.pi / 10)) ^ 2 - 3) / 2 :=
  (tenth_polynomial_data _ _ tenth_sine_quadratic
    (Real.sin_sq_add_cos_sq (Real.pi / 10))).1

theorem tenth_cosine_quartic : (2 * Real.cos (Real.pi / 10)) ^ 4 -
    5 * (2 * Real.cos (Real.pi / 10)) ^ 2 + 5 = 0 :=
  (tenth_polynomial_data _ _ tenth_sine_quadratic
    (Real.sin_sq_add_cos_sq (Real.pi / 10))).2

theorem tenth_sine_triple : Real.sin (3 * (Real.pi / 10)) =
    Real.sin (Real.pi / 10) + 1 / 2 := by
  rw [sin_three_mul_eq]
  linear_combination -(Real.sin (Real.pi / 10) - 1 / 2) * tenth_sine_quadratic

theorem tenth_sine_six : Real.sin (6 * (Real.pi / 10)) = Real.cos (Real.pi / 10) := by
  rw [show 6 * (Real.pi / 10) = Real.pi / 2 + Real.pi / 10 by ring,
    Real.sin_add, Real.sin_pi_div_two, Real.cos_pi_div_two]
  ring

theorem tenth_sine_seven : Real.sin (7 * (Real.pi / 10)) =
    Real.sin (Real.pi / 10) + 1 / 2 := by
  rw [show 7 * (Real.pi / 10) = Real.pi - 3 * (Real.pi / 10) by ring,
    Real.sin_pi_sub, tenth_sine_triple]

theorem tenth_negative_conjugate (a : ℝ) (ha : 0 < a) (ha2 : a < 1 / 2)
    (hq : 4 * a ^ 2 + 2 * a = 1) :
    ∃ a' b' : ℝ, 0 < b' ∧ a' + 1 / 2 < 0 ∧ a ^ 2 < a' ^ 2 ∧
      a' ^ 2 + b' ^ 2 = 1 ∧ 4 * a' ^ 2 + 2 * a' = 1 := by
  let a' := -a - 1 / 2
  have hq' : 4 * a' ^ 2 + 2 * a' = 1 := by dsimp [a']; nlinarith
  have hsmall : a' ^ 2 < 1 := by dsimp [a']; nlinarith
  refine ⟨a', Real.sqrt (1 - a' ^ 2), Real.sqrt_pos.mpr (by linarith), ?_, ?_, ?_, hq'⟩
  · dsimp [a']; linarith
  · dsimp [a']; nlinarith
  · rw [Real.sq_sqrt (by linarith : 0 ≤ 1 - a' ^ 2)]
    ring

end Erdos633b
