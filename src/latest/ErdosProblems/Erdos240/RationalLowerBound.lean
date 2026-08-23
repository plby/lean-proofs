/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos240.PrimeLogs
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

/-!
# Elementary rational lower bounds for logarithms

For distinct positive natural numbers `A` and `B`, the rational number
`A / B` cannot be too close to one: its logarithm has absolute value at
least `1 / max A B`.  The final lemmas rewrite the logarithm of a quotient
of prime-power products as an integer linear form in prime logarithms.
-/

namespace Erdos240.RationalLowerBound

open scoped BigOperators

/-- If `m < n` are positive naturals, then `log (n / m) ≥ 1 / n`.
This is the rational specialization of `1 - x⁻¹ ≤ log x`. -/
lemma one_div_le_log_nat_div {m n : ℕ} (hm : 0 < m) (hmn : m < n) :
    (1 : ℝ) / n ≤ Real.log ((n : ℝ) / (m : ℝ)) := by
  have hmR : 0 < (m : ℝ) := by exact_mod_cast hm
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hm.trans hmn
  have hstep : (1 : ℝ) ≤ (n : ℝ) - (m : ℝ) := by
    have hsucc : m + 1 ≤ n := Nat.succ_le_iff.mpr hmn
    have hsuccR : (m : ℝ) + 1 ≤ (n : ℝ) := by exact_mod_cast hsucc
    linarith
  calc
    (1 : ℝ) / n ≤ ((n : ℝ) - (m : ℝ)) / n := by
      exact (div_le_div_iff_of_pos_right hnR).mpr hstep
    _ = 1 - (((n : ℝ) / (m : ℝ))⁻¹) := by
      rw [inv_div]
      field_simp
    _ ≤ Real.log ((n : ℝ) / (m : ℝ)) :=
      Real.one_sub_inv_le_log_of_pos (div_pos hnR hmR)

/-- Reversing a positive ratio negates its logarithm, hence does not change
the absolute value. -/
lemma abs_log_nat_div_comm {A B : ℕ} (hA : 0 < A) (hB : 0 < B) :
    |Real.log ((A : ℝ) / (B : ℝ))| =
      |Real.log ((B : ℝ) / (A : ℝ))| := by
  have hA0 : (A : ℝ) ≠ 0 := by positivity
  have hB0 : (B : ℝ) ≠ 0 := by positivity
  rw [Real.log_div hA0 hB0, Real.log_div hB0 hA0]
  rw [show Real.log (A : ℝ) - Real.log (B : ℝ) =
      -(Real.log (B : ℝ) - Real.log (A : ℝ)) by ring, abs_neg]

/-- Elementary Liouville bound for a nontrivial positive rational number. -/
theorem one_div_max_le_abs_log_nat_div {A B : ℕ}
    (hA : 0 < A) (hB : 0 < B) (hne : A ≠ B) :
    (1 : ℝ) / (max A B : ℕ) ≤
      |Real.log ((A : ℝ) / (B : ℝ))| := by
  rcases lt_or_gt_of_ne hne with hAB | hBA
  · rw [Nat.max_eq_right (Nat.le_of_lt hAB)]
    rw [abs_log_nat_div_comm hA hB]
    rw [abs_of_pos (Real.log_pos (by
      rw [one_lt_div₀ (by exact_mod_cast hA : (0 : ℝ) < A)]
      exact_mod_cast hAB))]
    exact one_div_le_log_nat_div hA hAB
  · rw [Nat.max_eq_left (Nat.le_of_lt hBA)]
    rw [abs_of_pos (Real.log_pos (by
      rw [one_lt_div₀ (by exact_mod_cast hB : (0 : ℝ) < B)]
      exact_mod_cast hBA))]
    exact one_div_le_log_nat_div hB hBA

section PrimePowers

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (p : ι → ℕ) (hp : ∀ i, (p i).Prime)

include hp

omit [DecidableEq ι] in
/-- The logarithm of a quotient of two prime-power products is the linear
form whose coefficients are the differences of the two exponent vectors. -/
lemma log_div_prod_prime_powers (e f : ι → ℕ) :
    Real.log (((∏ i, p i ^ e i : ℕ) : ℝ) /
        ((∏ i, p i ^ f i : ℕ) : ℝ)) =
      ∑ i, ((((e i : ℤ) - (f i : ℤ) : ℤ) : ℝ) *
        Real.log (p i : ℝ)) := by
  have he0 : ((∏ i, p i ^ e i : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast (Finset.prod_ne_zero_iff.mpr fun i hi =>
      pow_ne_zero _ (hp i).ne_zero)
  have hf0 : ((∏ i, p i ^ f i : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast (Finset.prod_ne_zero_iff.mpr fun i hi =>
      pow_ne_zero _ (hp i).ne_zero)
  rw [Real.log_div he0 hf0]
  rw [PrimeLogs.log_prod_prime_powers p hp,
    PrimeLogs.log_prod_prime_powers p hp]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  push_cast
  ring

/-- Distinct exponent vectors over distinct primes give distinct products. -/
lemma prod_prime_powers_ne_of_ne
    (hinj : Function.Injective p) {e f : ι → ℕ} (hef : e ≠ f) :
    (∏ i, p i ^ e i) ≠ ∏ i, p i ^ f i := by
  intro hprod
  apply hef
  funext j
  have hfac := congrArg (fun n : ℕ => n.factorization (p j)) hprod
  simpa only [PrimeLogs.factorization_prod_prime_powers p hp hinj] using hfac

/-- Liouville's rational bound applied to an integer linear form coming from
the difference of two prime-power exponent vectors. -/
theorem one_div_max_prod_le_abs_sum_sub_mul_log
    (hinj : Function.Injective p) {e f : ι → ℕ} (hef : e ≠ f) :
    (1 : ℝ) / (max (∏ i, p i ^ e i) (∏ i, p i ^ f i) : ℕ) ≤
      |∑ i, ((((e i : ℤ) - (f i : ℤ) : ℤ) : ℝ) *
        Real.log (p i : ℝ))| := by
  have hepos : 0 < ∏ i, p i ^ e i :=
    Finset.prod_pos fun i hi => pow_pos (hp i).pos _
  have hfpos : 0 < ∏ i, p i ^ f i :=
    Finset.prod_pos fun i hi => pow_pos (hp i).pos _
  have hbound := one_div_max_le_abs_log_nat_div hepos hfpos
    (prod_prime_powers_ne_of_ne p hp hinj hef)
  rwa [log_div_prod_prime_powers p hp e f] at hbound

end PrimePowers

end Erdos240.RationalLowerBound

#print axioms Erdos240.RationalLowerBound.one_div_max_le_abs_log_nat_div
#print axioms Erdos240.RationalLowerBound.log_div_prod_prime_powers
#print axioms Erdos240.RationalLowerBound.one_div_max_prod_le_abs_sum_sub_mul_log
