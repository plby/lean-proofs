/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos175.Phase

/-!
# Derivatives of the reciprocal phase

This file records the elementary differential estimates for the phase
`t ↦ x / t` on a dyadic interval.  They are the input concerning this
particular phase in the derivative estimates used by Granville--Ramaré.
-/

namespace Erdos175

open Set

/-- The exact `k`-th derivative of `t ↦ x / t`. -/
theorem iteratedDeriv_reciprocalPhase (k : ℕ) (x t : ℝ) :
    iteratedDeriv k (reciprocalPhase x) t =
      (-1 : ℝ) ^ k * (k.factorial : ℝ) * x / t ^ (k + 1) := by
  change iteratedDeriv k (fun u : ℝ => x * u⁻¹) t = _
  rw [iteratedDeriv_const_mul_field, iteratedDeriv_eq_iterate, iter_deriv_inv]
  rw [show (-1 - (k : ℤ)) = Int.negSucc k by omega, zpow_negSucc]
  ring

/-- The absolute value of the `k`-th derivative, for a positive argument. -/
theorem abs_iteratedDeriv_reciprocalPhase (k : ℕ) (x : ℝ) {t : ℝ} (ht : 0 < t) :
    |iteratedDeriv k (reciprocalPhase x) t| =
      (k.factorial : ℝ) * |x| / t ^ (k + 1) := by
  rw [iteratedDeriv_reciprocalPhase, abs_div, abs_mul, abs_mul]
  simp [abs_pow, abs_of_pos ht]

/-- On the positive half-line the magnitude of every derivative of the
reciprocal phase is antitone. -/
theorem antitoneOn_abs_iteratedDeriv_reciprocalPhase (k : ℕ) (x : ℝ) :
    AntitoneOn (fun t : ℝ => |iteratedDeriv k (reciprocalPhase x) t|) (Ioi 0) := by
  intro a ha b hb hab
  change |iteratedDeriv k (reciprocalPhase x) b| ≤
    |iteratedDeriv k (reciprocalPhase x) a|
  rw [abs_iteratedDeriv_reciprocalPhase k x hb,
    abs_iteratedDeriv_reciprocalPhase k x ha]
  exact div_le_div_of_nonneg_left
    (mul_nonneg (Nat.cast_nonneg _) (abs_nonneg _))
    (pow_pos ha _) (pow_le_pow_left₀ ha.le hab _)

/-- Endpoint bounds for the magnitude of the `k`-th derivative on a positive
closed interval. -/
theorem abs_iteratedDeriv_reciprocalPhase_interval_bounds
    (k : ℕ) (x : ℝ) {A B t : ℝ} (hA : 0 < A) (htA : A ≤ t) (htB : t ≤ B) :
    (k.factorial : ℝ) * |x| / B ^ (k + 1) ≤
        |iteratedDeriv k (reciprocalPhase x) t| ∧
      |iteratedDeriv k (reciprocalPhase x) t| ≤
        (k.factorial : ℝ) * |x| / A ^ (k + 1) := by
  have ht : 0 < t := hA.trans_le htA
  rw [abs_iteratedDeriv_reciprocalPhase k x ht]
  constructor <;> gcongr

/-- The dyadic-interval form of the endpoint bounds. -/
theorem abs_iteratedDeriv_reciprocalPhase_dyadic_bounds
    (k : ℕ) (x : ℝ) {A t : ℝ} (hA : 0 < A) (htA : A ≤ t) (ht2A : t ≤ 2 * A) :
    (k.factorial : ℝ) * |x| / (2 * A) ^ (k + 1) ≤
        |iteratedDeriv k (reciprocalPhase x) t| ∧
      |iteratedDeriv k (reciprocalPhase x) t| ≤
        (k.factorial : ℝ) * |x| / A ^ (k + 1) := by
  exact abs_iteratedDeriv_reciprocalPhase_interval_bounds k x hA htA ht2A

/-- For nonnegative `x`, an even derivative of `x/t` is nonnegative on the
positive half-line. -/
theorem iteratedDeriv_reciprocalPhase_nonneg_of_even
    {k : ℕ} (hk : Even k) {x t : ℝ} (hx : 0 ≤ x) (ht : 0 < t) :
    0 ≤ iteratedDeriv k (reciprocalPhase x) t := by
  rw [iteratedDeriv_reciprocalPhase, hk.neg_one_pow]
  positivity

/-- For nonnegative `x`, an odd derivative of `x/t` is nonpositive on the
positive half-line. -/
theorem iteratedDeriv_reciprocalPhase_nonpos_of_odd
    {k : ℕ} (hk : Odd k) {x t : ℝ} (hx : 0 ≤ x) (ht : 0 < t) :
    iteratedDeriv k (reciprocalPhase x) t ≤ 0 := by
  rw [iteratedDeriv_reciprocalPhase, hk.neg_one_pow]
  simp only [neg_one_mul]
  exact div_nonpos_of_nonpos_of_nonneg
    (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (Nat.cast_nonneg _)) hx)
    (pow_nonneg ht.le _)

/-- Even derivatives of `x/t`, for nonnegative `x`, are antitone on the
positive half-line. -/
theorem antitoneOn_iteratedDeriv_reciprocalPhase_of_even
    {k : ℕ} (hk : Even k) {x : ℝ} (hx : 0 ≤ x) :
    AntitoneOn (fun t : ℝ => iteratedDeriv k (reciprocalPhase x) t) (Ioi 0) := by
  intro a ha b hb hab
  change iteratedDeriv k (reciprocalPhase x) b ≤
    iteratedDeriv k (reciprocalPhase x) a
  rw [iteratedDeriv_reciprocalPhase, iteratedDeriv_reciprocalPhase,
    hk.neg_one_pow]
  simp only [one_mul]
  exact div_le_div_of_nonneg_left
    (mul_nonneg (Nat.cast_nonneg _) hx)
    (pow_pos ha _) (pow_le_pow_left₀ ha.le hab _)

/-- Odd derivatives of `x/t`, for nonnegative `x`, are monotone on the
positive half-line. -/
theorem monotoneOn_iteratedDeriv_reciprocalPhase_of_odd
    {k : ℕ} (hk : Odd k) {x : ℝ} (hx : 0 ≤ x) :
    MonotoneOn (fun t : ℝ => iteratedDeriv k (reciprocalPhase x) t) (Ioi 0) := by
  intro a ha b hb hab
  have h := antitoneOn_abs_iteratedDeriv_reciprocalPhase k x ha hb hab
  change |iteratedDeriv k (reciprocalPhase x) b| ≤
    |iteratedDeriv k (reciprocalPhase x) a| at h
  rw [abs_iteratedDeriv_reciprocalPhase k x hb,
    abs_iteratedDeriv_reciprocalPhase k x ha, abs_of_nonneg hx] at h
  change iteratedDeriv k (reciprocalPhase x) a ≤
    iteratedDeriv k (reciprocalPhase x) b
  rw [iteratedDeriv_reciprocalPhase, iteratedDeriv_reciprocalPhase,
    hk.neg_one_pow]
  simp only [neg_one_mul]
  calc
    -(k.factorial : ℝ) * x / a ^ (k + 1) =
        -((k.factorial : ℝ) * x / a ^ (k + 1)) := by ring
    _ ≤ -((k.factorial : ℝ) * x / b ^ (k + 1)) := neg_le_neg h
    _ = -(k.factorial : ℝ) * x / b ^ (k + 1) := by ring

end Erdos175
