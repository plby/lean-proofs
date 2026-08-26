/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.SmoothParameters

/-!
# Exact dyadic parameters for the residual-prime fibres

The smooth-parameter ray already defines the primary frontier X and the
interval length U = X * core r * r.  The Rankin decomposition also uses
z = X / 2^r.  Defining z as a power of two makes this quotient exact and
gives a clean logarithmic lower bound at both endpoints of every relevant
cofactor fibre.
-/

namespace Erdos4b
namespace SmoothParameters

noncomputable section

/-- The exact dyadic version of the intermediate frontier x / log₂ x. -/
def residualPrimeFrontier (a r : ℕ) : ℕ :=
  2 ^ (primaryExponent a r - r)

/-- The full cofactor range for which U / m stays above the residual-prime
frontier.  The final small-cofactor range is a subset of this one. -/
def fullResidualCofactorCutoff (r : ℕ) : ℕ :=
  2 ^ r * core r * r

theorem self_le_primaryExponent (a r : ℕ) :
    r ≤ primaryExponent a r := by
  have hfactor : 1 ≤ 2 ^ (a + 2 * r) := Nat.one_le_two_pow
  calc
    r ≤ core r := self_le_core r
    _ = 1 * core r := by simp
    _ ≤ 2 ^ (a + 2 * r) * core r :=
      Nat.mul_le_mul_right (core r) hfactor
    _ = primaryExponent a r := by rw [primaryExponent]

theorem self_lt_primaryExponent {a r : ℕ} :
    r < primaryExponent a r := by
  have hrcore : r < core r := by
    calc
      r < 2 ^ r := r.lt_two_pow_self
      _ ≤ 2 ^ (2 ^ r) :=
        pow_le_pow_right₀ (by norm_num : (1 : ℕ) ≤ 2)
          (Nat.le_of_lt r.lt_two_pow_self)
      _ = core r := by rw [core]
  have hfactor : 1 ≤ 2 ^ (a + 2 * r) := Nat.one_le_two_pow
  calc
    r < core r := hrcore
    _ = 1 * core r := by simp
    _ ≤ 2 ^ (a + 2 * r) * core r :=
      Nat.mul_le_mul_right (core r) hfactor
    _ = primaryExponent a r := by rw [primaryExponent]

theorem residualPrimeFrontier_mul_twoPow (a r : ℕ) :
    residualPrimeFrontier a r * 2 ^ r = primaryFrontier a r := by
  rw [residualPrimeFrontier, primaryFrontier]
  exact pow_sub_mul_pow 2 (self_le_primaryExponent a r)

theorem residualPrimeFrontier_pos (a r : ℕ) :
    0 < residualPrimeFrontier a r := by
  simp [residualPrimeFrontier]

theorem residualPrimeFrontier_one_lt (a r : ℕ) :
    1 < residualPrimeFrontier a r := by
  rw [residualPrimeFrontier]
  exact one_lt_pow₀ (by norm_num)
    (Nat.sub_pos_of_lt (self_lt_primaryExponent (a := a) (r := r))).ne'

theorem fullResidualCofactorCutoff_pos {r : ℕ} (hr : 0 < r) :
    0 < fullResidualCofactorCutoff r := by
  exact Nat.mul_pos
    (Nat.mul_pos (by positivity) (core_pos r)) hr

/-- Exact factorization U = z * B on the dyadic ray. -/
theorem intervalLength_eq_residualPrimeFrontier_mul_cutoff (a r : ℕ) :
    intervalLength a r =
      residualPrimeFrontier a r * fullResidualCofactorCutoff r := by
  rw [intervalLength, fullResidualCofactorCutoff]
  rw [← residualPrimeFrontier_mul_twoPow a r]
  ring

/-- Exact logarithm of the dyadic residual-prime frontier. -/
theorem log_residualPrimeFrontier (a r : ℕ) :
    Real.log (residualPrimeFrontier a r : ℝ) =
      ((primaryExponent a r - r : ℕ) : ℝ) * Real.log 2 := by
  rw [residualPrimeFrontier, Nat.cast_pow, Real.log_pow]
  norm_num

/-- Every positive cofactor in the full range leaves a prime endpoint at
least z. -/
theorem residualPrimeFrontier_le_intervalLength_div
    {a r m : ℕ} (hm : 0 < m) (hmB : m ≤ fullResidualCofactorCutoff r) :
    residualPrimeFrontier a r ≤ intervalLength a r / m := by
  apply (Nat.le_div_iff_mul_le hm).2
  calc
    residualPrimeFrontier a r * m ≤
        residualPrimeFrontier a r * fullResidualCofactorCutoff r :=
      Nat.mul_le_mul_left _ hmB
    _ = intervalLength a r :=
      (intervalLength_eq_residualPrimeFrontier_mul_cutoff a r).symm

/-- The same exact log z lower bound works uniformly throughout the
cofactor range. -/
theorem log_residualPrimeFrontier_le_log_intervalLength_div
    {a r m : ℕ} (hm : 0 < m) (hmB : m ≤ fullResidualCofactorCutoff r) :
    Real.log (residualPrimeFrontier a r : ℝ) ≤
      Real.log ((intervalLength a r / m : ℕ) : ℝ) := by
  exact Real.log_le_log
    (by exact_mod_cast residualPrimeFrontier_pos a r)
    (by exact_mod_cast
      residualPrimeFrontier_le_intervalLength_div hm hmB)

end

end SmoothParameters
end Erdos4b
