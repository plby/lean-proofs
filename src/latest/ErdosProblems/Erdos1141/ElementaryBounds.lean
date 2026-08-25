import Mathlib

/-!
# Elementary bounds for the small-prime argument

The divisor function is smaller than every fixed positive power. We use a
purely algebraic bound with an unspecified constant, so no large constants
need to be evaluated by Lean.
-/

open scoped BigOperators

namespace Erdos1141

lemma succ_pow_le_factorial_mul_two_pow (e r : ℕ) :
    (e + 1) ^ r ≤ (r.factorial * 2 ^ r) * 2 ^ e := by
  calc
    (e + 1) ^ r ≤ (e + 1).ascFactorial r := Nat.pow_succ_le_ascFactorial _ _
    _ = r.factorial * (e + r).choose r := Nat.ascFactorial_eq_factorial_mul_choose e r
    _ ≤ r.factorial * 2 ^ (e + r) := Nat.mul_le_mul_left _ (Nat.choose_le_two_pow _ _)
    _ = _ := by rw [pow_add]; ring

lemma succ_pow_le_prime_pow_of_large (e r p : ℕ) (hp : 2 ^ r ≤ p) :
    (e + 1) ^ r ≤ p ^ e := by
  calc
    (e + 1) ^ r ≤ (2 ^ e) ^ r :=
      Nat.pow_le_pow_left (Nat.succ_le_of_lt (Nat.lt_two_pow_self (n := e))) r
    _ = (2 ^ r) ^ e := by rw [← pow_mul, ← pow_mul, Nat.mul_comm e r]
    _ ≤ p ^ e := Nat.pow_le_pow_left hp e

/-- An elementary uniform divisor bound in integer-power form. -/
theorem exists_divisors_card_pow_le (r : ℕ) :
    ∃ C : ℕ, 0 < C ∧ ∀ n : ℕ, n ≠ 0 → n.divisors.card ^ r ≤ C * n := by
  let c := r.factorial * 2 ^ r
  have hc : 0 < c := Nat.mul_pos (Nat.factorial_pos _) (by positivity)
  refine ⟨c ^ (2 ^ r), pow_pos hc _, ?_⟩
  intro n hn
  rw [Nat.card_divisors hn, ← Finset.prod_pow]
  calc
    _ ≤ ∏ p ∈ n.primeFactors, (if p < 2 ^ r then c else 1) * p ^ n.factorization p := by
      apply Finset.prod_le_prod'
      intro p hp
      have hprime := Nat.prime_of_mem_primeFactors hp
      by_cases hsmall : p < 2 ^ r
      · rw [if_pos hsmall]
        exact (succ_pow_le_factorial_mul_two_pow _ _).trans
          (Nat.mul_le_mul_left c (Nat.pow_le_pow_left hprime.two_le _))
      · rw [if_neg hsmall, one_mul]
        exact succ_pow_le_prime_pow_of_large _ _ _ (Nat.le_of_not_lt hsmall)
    _ = (∏ p ∈ n.primeFactors, if p < 2 ^ r then c else 1) * n := by
      rw [Finset.prod_mul_distrib, ← Nat.prod_primeFactors_pow_factorization hn]
    _ ≤ c ^ (2 ^ r) * n := by
      apply Nat.mul_le_mul_right n
      rw [← Finset.prod_filter, Finset.prod_const]
      apply Nat.pow_le_pow_right hc
      calc
        (n.primeFactors.filter fun p ↦ p < 2 ^ r).card ≤ (Finset.range (2 ^ r)).card :=
          Finset.card_le_card (fun p hp ↦ Finset.mem_range.mpr (Finset.mem_filter.mp hp).2)
        _ = 2 ^ r := Finset.card_range _

theorem exists_divisors_card_le_rpow (r : ℕ) (hr : 0 < r) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, n ≠ 0 →
      (n.divisors.card : ℝ) ≤ C * (n : ℝ) ^ (1 / (r : ℝ)) := by
  obtain ⟨C, hC, hbound⟩ := exists_divisors_card_pow_le r
  have hCr : (0 : ℝ) < C := by exact_mod_cast hC
  refine ⟨(C : ℝ) ^ (1 / (r : ℝ)), Real.rpow_pos_of_pos hCr _, ?_⟩
  intro n hn
  have hpow : (n.divisors.card : ℝ) ^ r ≤ (C : ℝ) * n := by
    exact_mod_cast hbound n hn
  have hroot := Real.rpow_le_rpow (by positivity : 0 ≤ (n.divisors.card : ℝ) ^ r)
    hpow (by positivity : 0 ≤ 1 / (r : ℝ))
  rw [Real.mul_rpow hCr.le (Nat.cast_nonneg n)] at hroot
  simpa only [one_div, Real.pow_rpow_inv_natCast (Nat.cast_nonneg n.divisors.card) hr.ne']
    using hroot

lemma two_pow_primeFactors_card_le_divisors_card (n : ℕ) (hn : n ≠ 0) :
    2 ^ n.primeFactors.card ≤ n.divisors.card := by
  rw [Nat.card_divisors hn]
  calc
    2 ^ n.primeFactors.card = ∏ _p ∈ n.primeFactors, 2 := by simp
    _ ≤ _ := Finset.prod_le_prod' (by
      intro p hp
      have hpos := (Nat.prime_of_mem_primeFactors hp).factorization_pos_of_dvd hn
        (Nat.dvd_of_mem_primeFactors hp)
      omega)

/-- The bound can be made uniform over all positive integers below a growing cutoff. -/
theorem eventually_divisors_card_le_rpow_uniform (r : ℕ) (hr : 0 < r) :
    ∀ᶠ q : ℕ in Filter.atTop, ∀ n : ℕ, n ≠ 0 → n ≤ q →
      (n.divisors.card : ℝ) ≤ (q : ℝ) ^ (2 / (r : ℝ)) := by
  obtain ⟨C, hC, hbound⟩ := exists_divisors_card_le_rpow r hr
  have htend : Filter.Tendsto (fun q : ℕ ↦ (q : ℝ) ^ (1 / (r : ℝ)))
      Filter.atTop Filter.atTop :=
    (tendsto_rpow_atTop (by positivity : 0 < 1 / (r : ℝ))).comp
      tendsto_natCast_atTop_atTop
  filter_upwards [htend.eventually_ge_atTop C, Filter.eventually_ge_atTop 1] with q hq hq1
  intro n hn hnq
  have hqpos : (0 : ℝ) < q := by exact_mod_cast hq1
  calc
    (n.divisors.card : ℝ) ≤ C * (n : ℝ) ^ (1 / (r : ℝ)) := hbound n hn
    _ ≤ (q : ℝ) ^ (1 / (r : ℝ)) * (q : ℝ) ^ (1 / (r : ℝ)) :=
      mul_le_mul hq (Real.rpow_le_rpow (by positivity) (by exact_mod_cast hnq)
        (by positivity)) (by positivity) (by positivity)
    _ = (q : ℝ) ^ (2 / (r : ℝ)) := by rw [← Real.rpow_add hqpos]; congr 1; ring

end Erdos1141
