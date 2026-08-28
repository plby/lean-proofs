import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Tactic

/-!
# Upper-half-plane directions for a higher-order monomial

Every nonzero complex multiple of a monomial of degree at least two takes a
strictly lower-half-plane value along some unit direction in the upper half
plane. The proof chooses its direction explicitly using the principal
argument and the complex exponential.
-/

noncomputable section

open Complex

namespace Wikipedia.HopfProblem.RiemannMapping

private theorem im_mul_exp_real (c : ℂ) (θ : ℝ) :
    (c * Complex.exp ((θ : ℂ) * I)).im =
      ‖c‖ * Real.sin (c.arg + θ) := by
  calc
    (c * Complex.exp ((θ : ℂ) * I)).im =
        (((‖c‖ : ℝ) : ℂ) *
          (Complex.exp ((c.arg : ℂ) * I) * Complex.exp ((θ : ℂ) * I))).im := by
      rw [← mul_assoc, Complex.norm_mul_exp_arg_mul_I]
    _ = (((‖c‖ : ℝ) : ℂ) *
        Complex.exp (((c.arg + θ : ℝ) : ℂ) * I)).im := by
      rw [← Complex.exp_add]
      congr 3
      push_cast
      ring
    _ = ‖c‖ * Real.sin (c.arg + θ) := by
      rw [Complex.im_ofReal_mul, Complex.exp_ofReal_mul_I_im]

private theorem im_mul_exp_real_pow (c : ℂ) (θ : ℝ) (n : ℕ) :
    (c * Complex.exp ((θ : ℂ) * I) ^ n).im =
      ‖c‖ * Real.sin (c.arg + (n : ℝ) * θ) := by
  rw [← Complex.exp_nat_mul]
  have h : (n : ℂ) * ((θ : ℂ) * I) = (((n : ℝ) * θ : ℝ) : ℂ) * I := by
    push_cast
    ring
  rw [h]
  exact im_mul_exp_real c ((n : ℝ) * θ)

/-- A nonzero complex coefficient times a monomial of degree at least two
has a strictly negative imaginary part in some upper-half-plane unit
direction. -/
theorem exists_unit_upperHalf_power_direction
    {c : ℂ} (hc : c ≠ 0) {n : ℕ} (hn : 2 ≤ n) :
    ∃ v : ℂ, ‖v‖ = 1 ∧ 0 < v.im ∧ (c * v ^ n).im < 0 := by
  have hn₂ : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hn₀ : (0 : ℝ) < n := by linarith
  have hc₀ : 0 < ‖c‖ := norm_pos_iff.mpr hc
  have hπ : 0 < Real.pi := Real.pi_pos
  have ha₁ : -Real.pi < c.arg := Complex.neg_pi_lt_arg c
  have ha₂ : c.arg ≤ Real.pi := Complex.arg_le_pi c
  have hπn : 2 * Real.pi ≤ Real.pi * n := by nlinarith
  by_cases ha : -(Real.pi / 2) < c.arg
  · let θ : ℝ := (3 * Real.pi / 2 - c.arg) / n
    have hθ₀ : 0 < θ := div_pos (by linarith) hn₀
    have hθπ : θ < Real.pi := by
      apply (div_lt_iff₀ hn₀).mpr
      linarith
    have hphase : c.arg + (n : ℝ) * θ = 3 * Real.pi / 2 := by
      dsimp [θ]
      rw [mul_comm (n : ℝ), div_mul_cancel₀ _ hn₀.ne']
      ring
    refine ⟨Complex.exp ((θ : ℂ) * I), Complex.norm_exp_ofReal_mul_I θ, ?_, ?_⟩
    · rw [Complex.exp_ofReal_mul_I_im]
      exact Real.sin_pos_of_pos_of_lt_pi hθ₀ hθπ
    · rw [im_mul_exp_real_pow, hphase]
      rw [show 3 * Real.pi / 2 = Real.pi / 2 + Real.pi by ring,
        Real.sin_add_pi, Real.sin_pi_div_two]
      linarith
  · have ha' : c.arg ≤ -(Real.pi / 2) := le_of_not_gt ha
    let θ : ℝ := (-Real.pi / 4 - c.arg) / n
    have hθ₀ : 0 < θ := div_pos (by linarith) hn₀
    have hθπ : θ < Real.pi := by
      apply (div_lt_iff₀ hn₀).mpr
      linarith
    have hphase : c.arg + (n : ℝ) * θ = -Real.pi / 4 := by
      dsimp [θ]
      rw [mul_comm (n : ℝ), div_mul_cancel₀ _ hn₀.ne']
      ring
    refine ⟨Complex.exp ((θ : ℂ) * I), Complex.norm_exp_ofReal_mul_I θ, ?_, ?_⟩
    · rw [Complex.exp_ofReal_mul_I_im]
      exact Real.sin_pos_of_pos_of_lt_pi hθ₀ hθπ
    · rw [im_mul_exp_real_pow, hphase]
      exact mul_neg_of_pos_of_neg hc₀
        (Real.sin_neg_of_neg_of_neg_pi_lt (by linarith) (by linarith))

/-- The direction-only form of `exists_unit_upperHalf_power_direction`. -/
theorem exists_upperHalf_power_direction
    {c : ℂ} (hc : c ≠ 0) {n : ℕ} (hn : 2 ≤ n) :
    ∃ v : ℂ, 0 < v.im ∧ (c * v ^ n).im < 0 := by
  obtain ⟨v, _, hv, hcv⟩ := exists_unit_upperHalf_power_direction hc hn
  exact ⟨v, hv, hcv⟩

end Wikipedia.HopfProblem.RiemannMapping
