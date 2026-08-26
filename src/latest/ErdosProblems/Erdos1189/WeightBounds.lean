/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Elementary bounds relating Simpson's weight to the integer it factors.
Informal source: Section 4.1 of Pickhardt and Omniscience Research Agent,
"Irreducible Covering Sets: A Solution of Erdős Problem 1189".
Formal author: OpenAI Codex.
-/

import ErdosProblems.Erdos1189.PrimeGrid

namespace Erdos1189

open Finset

lemma simpsonWeight_eq_finsupp_sum (N : ℕ) :
    simpsonWeight N = N.factorization.sum (fun p a => a * (p - 1)) := rfl

lemma simpsonWeight_mul {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) :
    simpsonWeight (a * b) = simpsonWeight a + simpsonWeight b := by
  simp only [simpsonWeight_eq_finsupp_sum, Nat.factorization_mul ha hb]
  exact Finsupp.sum_add_index' (fun p => zero_mul (p - 1)) (fun _ _ _ => add_mul _ _ _)

lemma simpsonWeight_prime {p : ℕ} (hp : p.Prime) : simpsonWeight p = p - 1 := by
  rw [simpsonWeight_eq_finsupp_sum, hp.factorization]
  simp

lemma simpsonWeight_dvd {a b : ℕ} (hb : b ≠ 0) (hab : a ∣ b) :
    simpsonWeight a ≤ simpsonWeight b := by
  obtain ⟨c, rfl⟩ := hab
  rw [simpsonWeight_mul (left_ne_zero_of_mul hb) (right_ne_zero_of_mul hb)]
  omega

lemma simpsonWeight_prime_product {D : Finset ℕ} (hD : ∀ p ∈ D, p.Prime) :
    simpsonWeight (∏ p ∈ D, p) = ∑ p ∈ D, (p - 1) := by
  induction D using Finset.induction with
  | empty => simp [simpsonWeight]
  | @insert p D hp ih =>
      have hpP : p.Prime := hD p (mem_insert_self _ _)
      have hDP : ∀ q ∈ D, q.Prime := fun q hq => hD q (mem_insert_of_mem hq)
      rw [prod_insert hp, simpsonWeight_mul hpP.ne_zero
        (prod_ne_zero_iff.mpr (fun q hq => (hDP q hq).ne_zero)),
        simpsonWeight_prime hpP, ih hDP, sum_insert hp]

lemma succ_le_two_pow (n : ℕ) : n + 1 ≤ 2 ^ n := by
  induction n with
  | zero => norm_num
  | succ n ih =>
      rw [pow_succ]
      omega

lemma le_two_pow_pred {n : ℕ} (hn : 0 < n) : n ≤ 2 ^ (n - 1) := by
  simpa only [Nat.sub_add_cancel hn] using succ_le_two_pow (n - 1)

lemma four_mul_le_three_two_pow {n : ℕ} (hn : 3 ≤ n) :
    4 * n ≤ 3 * 2 ^ (n - 1) := by
  induction n, hn using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
      have hp : 2 ^ n = 2 ^ (n - 1) * 2 := by
        nth_rw 1 [← Nat.sub_add_cancel (show 1 ≤ n by omega)]
        rw [pow_succ]
      simp only [Nat.add_sub_cancel]
      rw [hp]
      omega

lemma prime_power_le_weight_power {p a : ℕ} (hp : 0 < p) :
    p ^ a ≤ 2 ^ (a * (p - 1)) := by
  calc
    p ^ a ≤ (2 ^ (p - 1)) ^ a := Nat.pow_le_pow_left (le_two_pow_pred hp) _
    _ = 2 ^ (a * (p - 1)) := by rw [← pow_mul, Nat.mul_comm]

lemma odd_power_le_weight_power {p a : ℕ} (hp : 3 ≤ p) (ha : 0 < a) :
    4 * p ^ a ≤ 3 * 2 ^ (a * (p - 1)) := by
  obtain ⟨b, rfl⟩ := Nat.exists_eq_succ_of_ne_zero ha.ne'
  have h1 := four_mul_le_three_two_pow hp
  have h2 := prime_power_le_weight_power (a := b) (show 0 < p by omega)
  calc
    4 * p ^ (b + 1) = (4 * p) * p ^ b := by rw [pow_succ]; ring
    _ ≤ (3 * 2 ^ (p - 1)) * 2 ^ (b * (p - 1)) := Nat.mul_le_mul h1 h2
    _ = 3 * 2 ^ ((b + 1) * (p - 1)) := by
      rw [mul_assoc, ← pow_add]
      congr 2
      ring

lemma le_two_pow_simpsonWeight {N : ℕ} (hN : N ≠ 0) : N ≤ 2 ^ simpsonWeight N := by
  calc
    N = ∏ p ∈ N.primeFactors, p ^ N.factorization p :=
      Nat.prod_primeFactors_pow_factorization hN
    _ ≤ ∏ p ∈ N.primeFactors, 2 ^ (N.factorization p * (p - 1)) := by
      exact prod_le_prod' fun p hp => prime_power_le_weight_power
        (Nat.prime_of_mem_primeFactors hp).pos
    _ = 2 ^ simpsonWeight N := by rw [prod_pow_eq_pow_sum]; rfl

lemma four_mul_le_three_pow_weight {N p : ℕ} (hN : N ≠ 0)
    (hp : p ∈ N.primeFactors) (hp3 : 3 ≤ p) :
    4 * N ≤ 3 * 2 ^ simpsonWeight N := by
  have ha : 0 < N.factorization p := by
    exact Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hp)
  have hrest : (∏ q ∈ N.primeFactors.erase p, q ^ N.factorization q) ≤
      2 ^ (∑ q ∈ N.primeFactors.erase p, N.factorization q * (q - 1)) := by
    rw [← prod_pow_eq_pow_sum]
    exact prod_le_prod' fun q hq => prime_power_le_weight_power
      (Nat.prime_of_mem_primeFactors (mem_of_mem_erase hq)).pos
  calc
    4 * N = (4 * p ^ N.factorization p) *
        (∏ q ∈ N.primeFactors.erase p, q ^ N.factorization q) := by
      conv_lhs => rw [Nat.prod_primeFactors_pow_factorization hN]
      rw [← mul_prod_erase _ _ hp]
      ring
    _ ≤ (3 * 2 ^ (N.factorization p * (p - 1))) *
        2 ^ (∑ q ∈ N.primeFactors.erase p, N.factorization q * (q - 1)) :=
      Nat.mul_le_mul (odd_power_le_weight_power hp3 ha) hrest
    _ = 3 * 2 ^ simpsonWeight N := by
      rw [mul_assoc, ← pow_add,
        add_sum_erase _ (fun q => N.factorization q * (q - 1)) hp]
      rfl

lemma eq_two_pow_of_primeFactors {N : ℕ} (hN : N ≠ 0)
    (h : ∀ p ∈ N.primeFactors, p = 2) : N = 2 ^ N.factorization 2 := by
  apply Nat.eq_pow_of_factorization_eq_single hN
  ext p
  by_cases hp : p = 2
  · subst p
    simp
  · have hp' : p ∉ N.factorization.support := fun hm => hp (h p hm)
    simp [Finsupp.notMem_support_iff.mp hp', Finsupp.single_eq_of_ne hp]

end Erdos1189
