/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Finite sixth-root approximations for the diagonal-surface determinant method.
Formal author: Codex.

The construction uses Mathlib's binomial series over a binomial ring. The
results here are polynomial identities and divisibility statements, not
assumed surface counting estimates.
-/

import Mathlib

namespace Erdos477.Counting

variable {R : Type*} [CommRing R] [BinomialRing R]

lemma binomialSeries_nat_mul (a : R) (n : ℕ) :
    PowerSeries.binomialSeries R ((n : R) * a) =
      (PowerSeries.binomialSeries R a) ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [Nat.cast_add, Nat.cast_one, add_mul, one_mul,
      PowerSeries.binomialSeries_add, ih, pow_succ]

lemma binomialSeries_sixth_root (a : R) (ha : 6 * a = 1) :
    (PowerSeries.binomialSeries R a) ^ 6 = 1 + PowerSeries.X := by
  rw [← binomialSeries_nat_mul]
  norm_num only [Nat.cast_ofNat]
  rw [ha]
  simpa using PowerSeries.binomialSeries_nat (R := R) (A := R) 1

/-- Truncation of the sixth-root series; `a` will be the inverse of six. -/
noncomputable def rootApprox (a : R) (N : ℕ) : Polynomial R :=
  PowerSeries.trunc N (PowerSeries.binomialSeries R a)

omit [BinomialRing R] in
lemma X_pow_dvd_of_trunc_eq_zero (P : Polynomial R) (N : ℕ)
    (h : PowerSeries.trunc N (P : PowerSeries R) = 0) :
    Polynomial.X ^ N ∣ P := by
  rw [Polynomial.X_pow_dvd_iff]
  intro i hi
  have hc := congrArg (fun Q : Polynomial R => Q.coeff i) h
  simpa only [PowerSeries.coeff_trunc, if_pos hi, Polynomial.coeff_coe,
    Polynomial.coeff_zero] using hc

/-- The truncated root solves the sixth-power equation modulo `X^N`. -/
theorem X_pow_dvd_rootApprox_error (a : R) (ha : 6 * a = 1) (N : ℕ) :
    Polynomial.X ^ N ∣ (rootApprox a N) ^ 6 - (1 + Polynomial.X) := by
  apply X_pow_dvd_of_trunc_eq_zero
  simp only [rootApprox, Polynomial.coe_sub, Polynomial.coe_pow, Polynomial.coe_add,
    Polynomial.coe_one, Polynomial.coe_X, PowerSeries.trunc_sub,
    PowerSeries.trunc_trunc_pow, binomialSeries_sixth_root a ha, sub_self]

/-- Substitution turns the formal approximation into a congruence modulo
`p^N` whenever its argument is divisible by `p`. -/
theorem pow_dvd_rootApprox_error (a : R) (ha : 6 * a = 1)
    (p z : R) (hz : p ∣ z) (N : ℕ) :
    p ^ N ∣ (rootApprox a N).eval z ^ 6 - (1 + z) := by
  obtain ⟨Q, hQ⟩ := X_pow_dvd_rootApprox_error a ha N
  have heval := congrArg (Polynomial.eval z) hQ
  simp only [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_add,
    Polynomial.eval_one, Polynomial.eval_X, Polynomial.eval_mul] at heval
  rw [heval]
  exact dvd_mul_of_dvd_left (pow_dvd_pow_of_dvd hz N) _

/-- Every positive-order truncation has constant coefficient one. -/
lemma rootApprox_coeff_zero (a : R) {N : ℕ} (hN : 0 < N) :
    (rootApprox a N).coeff 0 = 1 := by
  simp only [rootApprox, PowerSeries.coeff_trunc, if_pos hN,
    PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.binomialSeries_constantCoeff]

lemma X_dvd_rootApprox_sub_one (a : R) {N : ℕ} (hN : 0 < N) :
    Polynomial.X ∣ rootApprox a N - 1 := by
  rw [Polynomial.X_dvd_iff]
  simp only [Polynomial.coeff_sub, rootApprox_coeff_zero a hN, Polynomial.coeff_one_zero,
    sub_self]

lemma dvd_rootApprox_sub_one (a : R) (p z : R) (hz : p ∣ z)
    {N : ℕ} (hN : 0 < N) : p ∣ (rootApprox a N).eval z - 1 := by
  obtain ⟨Q, hQ⟩ := X_dvd_rootApprox_sub_one a hN
  have heval := congrArg (Polynomial.eval z) hQ
  simp only [Polynomial.eval_sub, Polynomial.eval_one, Polynomial.eval_X,
    Polynomial.eval_mul] at heval
  rw [heval]
  exact dvd_mul_of_dvd_left hz _

#print axioms pow_dvd_rootApprox_error
-- 'Erdos477.Counting.pow_dvd_rootApprox_error' depends on axioms:
-- [propext, Classical.choice, Quot.sound]

end Erdos477.Counting
