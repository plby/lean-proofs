/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
The prime sum weighted by reciprocal square roots of finite-field point counts.
Formal author: Codex.
-/

import ErdosProblems.Erdos477.Counting.PrimeSums
import ErdosProblems.Erdos477.Counting.PrimeErrorSeries

namespace Erdos477.Counting

open scoped BigOperators

lemma reciprocal_sqrt_lower (p q : ℝ) (hp : 0 < p) (hq : 0 < q)
    (hcount : q ≤ p ^ 2 + 343 * p * Real.sqrt p) :
    1 / p - 343 / (p * Real.sqrt p) ≤ 1 / Real.sqrt q := by
  have hr : 0 < Real.sqrt p := Real.sqrt_pos.mpr hp
  have hden : 0 < p + 343 * Real.sqrt p := by positivity
  have hroot : (Real.sqrt p) ^ 2 = p := Real.sq_sqrt hp.le
  have hupper : Real.sqrt q ≤ p + 343 * Real.sqrt p := by
    apply Real.sqrt_le_iff.mpr
    refine ⟨hden.le, ?_⟩
    nlinarith [mul_pos hp hr]
  have hid : 1 / (p + 343 * Real.sqrt p) - (1 / p - 343 / (p * Real.sqrt p)) =
      117649 / (p * (p + 343 * Real.sqrt p)) := by
    field_simp
    nlinarith
  have hdiff : 1 / p - 343 / (p * Real.sqrt p) ≤ 1 / (p + 343 * Real.sqrt p) := by
    apply sub_nonneg.mp
    rw [hid]
    positivity
  exact hdiff.trans (one_div_le_one_div_of_le (Real.sqrt_pos.mpr hq) hupper)

lemma sum_nonneg_le_sum_sdiff_add (S E : Finset ℕ) (f : ℕ → ℝ) (hf : ∀ n, 0 ≤ f n) :
    (∑ n ∈ S, f n) ≤ (∑ n ∈ S \ E, f n) + ∑ n ∈ E, f n := by
  have hset : S ∪ E = (S \ E) ∪ E := by
    ext n
    simp only [Finset.mem_union, Finset.mem_sdiff]
    tauto
  calc
    _ ≤ ∑ n ∈ S ∪ E, f n :=
      Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_left (fun n _ _ => hf n)
    _ = _ := by
      rw [hset, Finset.sum_union]
      exact Finset.sdiff_disjoint

/-- The leading logarithm survives both the finite-field error and deletion
of any fixed finite collection of primes. -/
theorem exists_reciprocal_sqrt_prime_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (N : ℕ), 1 ≤ N → ∀ (E : Finset ℕ) (q : ℕ → ℝ),
      (∀ p ∈ Nat.primesLE N \ E, 0 < q p ∧
        q p ≤ (p : ℝ) ^ 2 + 343 * p * Real.sqrt p) →
      Real.log N - C - (∑ p ∈ E, Real.log p / (p : ℝ)) ≤
        ∑ p ∈ Nat.primesLE N \ E, Real.log p / Real.sqrt (q p) := by
  obtain ⟨K, hK, hKsum⟩ := exists_log_sqrt_error_bound
  refine ⟨3 + 343 * K, by positivity, ?_⟩
  intro N hN E q hq
  let S := Nat.primesLE N \ E
  have hsplit := sum_nonneg_le_sum_sdiff_add (Nat.primesLE N) E
    (fun p => Real.log p / (p : ℝ)) (fun p =>
      div_nonneg (Real.log_natCast_nonneg p) (Nat.cast_nonneg p))
  have hprime := log_sub_three_le_prime_sum N hN
  have hpoint :
      (∑ p ∈ S, Real.log p / (p : ℝ)) -
        343 * (∑ p ∈ S, Real.log p / ((p : ℝ) * Real.sqrt p)) ≤
      ∑ p ∈ S, Real.log p / Real.sqrt (q p) := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_le_sum
    intro p hp
    have hpp := (Nat.mem_primesLE.mp (Finset.mem_sdiff.mp hp).1).2
    have h := mul_le_mul_of_nonneg_left
      (reciprocal_sqrt_lower p (q p) (Nat.cast_pos.mpr hpp.pos) (hq p hp).1 (hq p hp).2)
      (Real.log_natCast_nonneg p)
    convert h using 1 <;> ring
  have herr := hKsum S
  change _ ≤ ∑ p ∈ S, Real.log p / Real.sqrt (q p)
  change _ ≤ (∑ p ∈ S, Real.log p / (p : ℝ)) + _ at hsplit
  linarith

#print axioms exists_reciprocal_sqrt_prime_bound
-- 'Erdos477.Counting.exists_reciprocal_sqrt_prime_bound' depends on axioms:
-- [propext, Classical.choice, Quot.sound]

end Erdos477.Counting
