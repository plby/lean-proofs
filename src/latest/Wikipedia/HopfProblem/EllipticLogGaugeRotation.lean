import Wikipedia.HopfProblem.EllipticFamilies
import Wikipedia.HopfProblem.CuspExponentials

/-!
# The logarithmic sign of the elliptic base rotations

The selected base rotations have angle `-2π / m`, for `m = 3` or `4`.
Thus a normalized logarithm changes by `-1 / m`, up to an integer.  This
is the sign that cancels the positive affine translation in the
logarithmic gauge transformation.
-/

noncomputable section

namespace Wikipedia.HopfProblem.Elliptic.LogGauge

open SpecialPeriods CuspUniformization

theorem exponential_neg_one_third : exponential (-(1 / (3 : ℂ))) = -rho := by
  have hρ : Complex.exp ((Real.pi : ℂ) / 3 * Complex.I) = rho := by
    simpa only [Complex.ofReal_div, Complex.ofReal_ofNat] using rho_eq_exp.symm
  rw [exponential,
    show (2 * Real.pi * Complex.I : ℂ) * -(1 / 3) =
      (Real.pi : ℂ) / 3 * Complex.I - Real.pi * Complex.I by ring,
    Complex.exp_sub_pi_mul_I, hρ]

theorem exponential_neg_one_fourth : exponential (-(1 / (4 : ℂ))) = -Complex.I := by
  rw [exponential,
    show (2 * Real.pi * Complex.I : ℂ) * -(1 / 4) =
      -(Real.pi : ℂ) / 2 * Complex.I by ring,
    Complex.exp_neg_pi_div_two_mul_I]

/-- Both actual base rotations use the negative primitive angle. -/
theorem familyRotation_val_exponential (j : Kind) (z : Disc) :
    (familyRotation j z : ℂ) = exponential (-(1 / (j.order : ℂ))) * (z : ℂ) := by
  cases j
  · change -rho * (z : ℂ) = exponential (-(1 / (3 : ℂ))) * (z : ℂ)
    rw [exponential_neg_one_third]
  · change -Complex.I * (z : ℂ) = exponential (-(1 / (4 : ℂ))) * (z : ℂ)
    rw [exponential_neg_one_fourth]

theorem familyRotation_ne_zero (j : Kind) (z : Disc) (hz : (z : ℂ) ≠ 0) :
    (familyRotation j z : ℂ) ≠ 0 := by
  rw [familyRotation_val_exponential]
  exact mul_ne_zero (exponential_ne_zero _) hz

/-- The shift holds for any choices of normalized logarithms, not only the
principal logarithm. -/
theorem familyRotation_logarithms (j : Kind) (z : Disc) (s r : ℂ)
    (hs : exponential s = (z : ℂ)) (hr : exponential r = (familyRotation j z : ℂ)) :
    ∃ n : ℤ, r = s - 1 / (j.order : ℂ) + n := by
  apply (exponential_eq_iff r (s - 1 / (j.order : ℂ))).mp
  rw [hr, familyRotation_val_exponential, sub_eq_add_neg, exponential_add, hs]
  exact mul_comm _ _

/-- A rotation subtracts `1 / m` from the normalized logarithm, modulo integers. -/
theorem logarithm_familyRotation (j : Kind) (z : Disc) (hz : (z : ℂ) ≠ 0) :
    ∃ n : ℤ, logarithm (familyRotation j z : ℂ) =
      logarithm (z : ℂ) - 1 / (j.order : ℂ) + n :=
  familyRotation_logarithms j z _ _ (exponential_logarithm hz)
    (exponential_logarithm (familyRotation_ne_zero j z hz))

end Wikipedia.HopfProblem.Elliptic.LogGauge
