/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Prime logarithm identities for Erdős Problem 240

This module isolates the elementary arithmetic input needed before applying
a lower bound for a linear form in logarithms.  Unique factorization gives
integer linear independence of the logarithms of distinct primes, while the
logarithm of a prime-power product bounds each exponent coordinate.
-/

namespace Erdos240.PrimeLogs

open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (p : ι → ℕ) (hp : ∀ i, (p i).Prime)

section PrimeFamily

include hp

omit [DecidableEq ι] in
/-- The logarithm of a finite product of positive prime powers is the
corresponding sum of exponent-weighted prime logarithms. -/
lemma log_prod_prime_powers (e : ι → ℕ) :
    Real.log ((∏ i, p i ^ e i : ℕ) : ℝ) =
      ∑ i, (e i : ℝ) * Real.log (p i : ℝ) := by
  calc
    Real.log ((∏ i, p i ^ e i : ℕ) : ℝ) =
        Real.log (∏ i, ((p i : ℝ) ^ e i)) := by simp
    _ = ∑ i, Real.log ((p i : ℝ) ^ e i) := by
      apply Real.log_prod
      intro i hi
      exact pow_ne_zero _ (Nat.cast_ne_zero.mpr (hp i).ne_zero)
    _ = ∑ i, (e i : ℝ) * Real.log (p i : ℝ) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [Real.log_pow]

/-- Unique factorization recovers each exponent in a product of powers of
pairwise distinct primes. -/
lemma factorization_prod_prime_powers
    (hinj : Function.Injective p) (e : ι → ℕ) (j : ι) :
    (∏ i, p i ^ e i).factorization (p j) = e j := by
  rw [Nat.factorization_prod_apply]
  · simp only [(hp _).factorization_pow, Finsupp.single_apply]
    simp [hinj.eq_iff]
  · intro i hi
    exact pow_ne_zero _ (hp i).ne_zero

/-- Prime logarithms indexed by pairwise distinct primes are linearly
independent for integer coefficients. -/
theorem int_linear_independent_prime_logs
    (hinj : Function.Injective p) (z : ι → ℤ)
    (hz : ∑ i, (z i : ℝ) * Real.log (p i : ℝ) = 0) :
    z = 0 := by
  let A : ℕ := ∏ i, p i ^ (z i).toNat
  let B : ℕ := ∏ i, p i ^ (-z i).toNat
  have hcast (i : ι) :
      (z i : ℝ) = ((z i).toNat : ℝ) - ((-z i).toNat : ℝ) := by
    exact_mod_cast (z i).toNat_sub_toNat_neg.symm
  have hlog : Real.log (A : ℝ) = Real.log (B : ℝ) := by
    apply sub_eq_zero.mp
    rw [log_prod_prime_powers p hp, log_prod_prime_powers p hp]
    rw [← Finset.sum_sub_distrib]
    calc
      (∑ i, (((z i).toNat : ℝ) * Real.log (p i : ℝ) -
          ((-z i).toNat : ℝ) * Real.log (p i : ℝ))) =
          ∑ i, (z i : ℝ) * Real.log (p i : ℝ) := by
            apply Finset.sum_congr rfl
            intro i hi
            rw [hcast]
            ring
      _ = 0 := hz
  have hABreal : (A : ℝ) = (B : ℝ) := by
    apply Real.log_injOn_pos
    · change 0 < (A : ℝ)
      exact_mod_cast (Finset.prod_pos fun i hi => pow_pos (hp i).pos _)
    · change 0 < (B : ℝ)
      exact_mod_cast (Finset.prod_pos fun i hi => pow_pos (hp i).pos _)
    · exact hlog
  have hAB : A = B := by exact_mod_cast hABreal
  funext j
  have hfac := congrArg (fun n : ℕ => n.factorization (p j)) hAB
  have hparts : (z j).toNat = (-z j).toNat := by
    simpa [A, B, factorization_prod_prime_powers p hp hinj] using hfac
  show z j = 0
  calc
    z j = ((z j).toNat : ℤ) - ((-z j).toNat : ℤ) :=
      (z j).toNat_sub_toNat_neg.symm
    _ = 0 := sub_eq_zero.mpr (by exact_mod_cast hparts)

/-- Equivalently, a nontrivial integer linear combination of logarithms of
pairwise distinct primes never vanishes. -/
theorem sum_int_mul_log_ne_zero
    (hinj : Function.Injective p) {z : ι → ℤ} (hz : z ≠ 0) :
    ∑ i, (z i : ℝ) * Real.log (p i : ℝ) ≠ 0 := by
  intro hzero
  exact hz (int_linear_independent_prime_logs p hp hinj z hzero)

omit [DecidableEq ι] in
/-- Every exponent-weighted prime logarithm is at most the logarithm of the
whole product. -/
lemma exponent_mul_log_le_log_prod (e : ι → ℕ) (j : ι) :
    (e j : ℝ) * Real.log (p j : ℝ) ≤
      Real.log ((∏ i, p i ^ e i : ℕ) : ℝ) := by
  rw [log_prod_prime_powers p hp]
  refine Finset.single_le_sum
    (f := fun i => (e i : ℝ) * Real.log (p i : ℝ))
    (s := Finset.univ) ?_ (Finset.mem_univ j)
  · intro i hi
    exact mul_nonneg (Nat.cast_nonneg _) (Real.log_nonneg (by
      exact_mod_cast (hp i).one_le))

omit [DecidableEq ι] in
/-- Dividing by the positive logarithm gives the familiar exponent bound. -/
lemma exponent_le_log_prod_div_log (e : ι → ℕ) (j : ι) :
    (e j : ℝ) ≤
      Real.log ((∏ i, p i ^ e i : ℕ) : ℝ) / Real.log (p j : ℝ) := by
  rw [le_div_iff₀ (Real.log_pos (by exact_mod_cast (hp j).one_lt))]
  exact exponent_mul_log_le_log_prod p hp e j

omit [DecidableEq ι] in
/-- Since every prime is at least two, base two gives a uniform denominator
for all exponent coordinates. -/
lemma exponent_le_log_prod_div_log_two (e : ι → ℕ) (j : ι) :
    (e j : ℝ) ≤
      Real.log ((∏ i, p i ^ e i : ℕ) : ℝ) / Real.log (2 : ℝ) := by
  rw [le_div_iff₀ (Real.log_pos (by norm_num : (1 : ℝ) < 2))]
  calc
    (e j : ℝ) * Real.log 2 ≤ (e j : ℝ) * Real.log (p j : ℝ) := by
      gcongr
      exact_mod_cast (hp j).two_le
    _ ≤ Real.log ((∏ i, p i ^ e i : ℕ) : ℝ) :=
      exponent_mul_log_le_log_prod p hp e j

end PrimeFamily

/-- A factorization coordinate, weighted by its prime logarithm, is at most
the logarithm of the whole nonzero number. -/
lemma factorization_mul_log_le_log {n q : ℕ} (_hn : n ≠ 0)
    (_hq : q.Prime) :
    (n.factorization q : ℝ) * Real.log (q : ℝ) ≤ Real.log (n : ℝ) := by
  calc
    (n.factorization q : ℝ) * Real.log (q : ℝ) =
        (Finsupp.single q (n.factorization q)).sum
          (fun r k => (k : ℝ) * Real.log (r : ℝ)) := by simp
    _ ≤ n.factorization.sum (fun r k => (k : ℝ) * Real.log (r : ℝ)) := by
      apply Finsupp.single_le_sum
      intro r k
      by_cases hr : r = 0
      · simp [hr]
      · exact mul_nonneg (Nat.cast_nonneg _)
          (Real.log_nonneg (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hr))
    _ = Real.log (n : ℝ) := (Real.log_nat_eq_sum_factorization n).symm

/-- Every prime-factorization coordinate of a nonzero number is bounded by
its logarithm divided by `log 2`. -/
lemma factorization_le_log_div_log_two {n q : ℕ} (hn : n ≠ 0)
    (hq : q.Prime) :
    (n.factorization q : ℝ) ≤ Real.log (n : ℝ) / Real.log (2 : ℝ) := by
  rw [le_div_iff₀ (Real.log_pos (by norm_num : (1 : ℝ) < 2))]
  calc
    (n.factorization q : ℝ) * Real.log 2 ≤
        (n.factorization q : ℝ) * Real.log (q : ℝ) := by
      gcongr
      exact_mod_cast hq.two_le
    _ ≤ Real.log (n : ℝ) := factorization_mul_log_le_log hn hq

end Erdos240.PrimeLogs

#print axioms Erdos240.PrimeLogs.int_linear_independent_prime_logs
#print axioms Erdos240.PrimeLogs.sum_int_mul_log_ne_zero
#print axioms Erdos240.PrimeLogs.factorization_le_log_div_log_two
