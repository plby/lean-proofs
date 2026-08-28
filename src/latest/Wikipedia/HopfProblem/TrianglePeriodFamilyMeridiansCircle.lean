import Wikipedia.HopfProblem.SpecialPeriodsLocal

/-!
# Circle coordinates for the geometric meridians

The real parameter makes one positive turn in the complex unit circle.
Its fractional turns give the roots used in the elliptic meridian lifts,
while reversal gives the opposite orientation.
-/

noncomputable section

namespace Wikipedia.HopfProblem.TrianglePeriodFamily.Meridians

/-- One positively oriented complex turn per unit of real time. -/
def turn (t : ℝ) : ℂ := Complex.exp (2 * Real.pi * Complex.I * (t : ℂ))

@[fun_prop] theorem continuous_turn : Continuous turn := by
  unfold turn
  fun_prop

@[simp] theorem norm_turn (t : ℝ) : ‖turn t‖ = 1 := by
  rw [turn, Complex.norm_exp]
  simp

theorem turn_ne_zero (t : ℝ) : turn t ≠ 0 := Complex.exp_ne_zero _

@[simp] theorem turn_zero : turn 0 = 1 := by simp [turn]

@[simp] theorem turn_one : turn 1 = 1 := by
  simpa only [turn, Complex.ofReal_one, mul_one] using Complex.exp_two_pi_mul_I

theorem turn_add (s t : ℝ) : turn (s + t) = turn s * turn t := by
  simp only [turn, Complex.ofReal_add, mul_add, Complex.exp_add]

@[simp] theorem turn_neg (t : ℝ) : turn (-t) = (turn t)⁻¹ := by
  simp only [turn, Complex.ofReal_neg, mul_neg, Complex.exp_neg]

theorem turn_sub (s t : ℝ) : turn (s - t) = turn s / turn t := by
  rw [sub_eq_add_neg, turn_add, turn_neg, div_eq_mul_inv]

theorem turn_periodic : Function.Periodic turn 1 := by
  intro t
  rw [turn_add, turn_one, mul_one]

/-- Reversing a full loop is the negative-time circle coordinate. -/
theorem turn_one_sub (t : ℝ) : turn (1 - t) = turn (-t) := by
  rw [sub_eq_add_neg, turn_add, turn_one, one_mul]

theorem turn_one_sub_eq_inv (t : ℝ) : turn (1 - t) = (turn t)⁻¹ := by
  rw [turn_one_sub, turn_neg]

theorem turn_one_sub_exp (t : ℝ) :
    turn (1 - t) = Complex.exp (-2 * Real.pi * Complex.I * (t : ℂ)) := by
  rw [turn_one_sub]
  unfold turn
  congr 1
  push_cast
  ring

theorem turn_nat_mul (n : ℕ) (t : ℝ) : turn ((n : ℝ) * t) = turn t ^ n := by
  unfold turn
  rw [← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

/-- Raising a fractional turn to its positive integer degree gives the
original full-time circle coordinate. -/
theorem turn_div_nat_pow (t : ℝ) (n : ℕ) (hn : 0 < n) :
    turn (t / n) ^ n = turn t := by
  rw [← turn_nat_mul]
  congr 1
  exact mul_div_cancel₀ t (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn))

/-- A positive third turn is the inverse of the source's negative
order-three rotation. -/
theorem turn_one_third : turn (1 / 3) = (-SpecialPeriods.rho)⁻¹ := by
  change Complex.exp (2 * Real.pi * Complex.I * ((1 / 3 : ℝ) : ℂ)) = _
  calc
    Complex.exp (2 * Real.pi * Complex.I * ((1 / 3 : ℝ) : ℂ)) =
        Complex.exp (-(((Real.pi / 3 : ℝ) : ℂ) * Complex.I) +
          (Real.pi : ℂ) * Complex.I) := by
      congr 1
      push_cast
      ring
    _ = -Complex.exp (-(((Real.pi / 3 : ℝ) : ℂ) * Complex.I)) :=
      Complex.exp_add_pi_mul_I _
    _ = -SpecialPeriods.rho⁻¹ := by
      rw [Complex.exp_neg, ← SpecialPeriods.rho_eq_exp]
    _ = (-SpecialPeriods.rho)⁻¹ := by rw [inv_neg]

/-- The positive quarter-turn endpoint. -/
theorem turn_one_quarter : turn (1 / 4) = Complex.I := by
  change Complex.exp (2 * Real.pi * Complex.I * ((1 / 4 : ℝ) : ℂ)) = _
  calc
    Complex.exp (2 * Real.pi * Complex.I * ((1 / 4 : ℝ) : ℂ)) =
        Complex.exp ((Real.pi : ℂ) / 2 * Complex.I) := by
      congr 1
      push_cast
      ring
    _ = Complex.I := Complex.exp_pi_div_two_mul_I

end Wikipedia.HopfProblem.TrianglePeriodFamily.Meridians
