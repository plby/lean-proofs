/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Combining prime-power divisors into a logarithmic lower bound.
Formal author: Codex.
-/

import Mathlib

namespace Erdos477.Counting

open scoped BigOperators

lemma prod_prime_powers_dvd (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime)
    (e : ℕ → ℕ) (D : ℤ) (hdiv : ∀ p ∈ S, (p : ℤ) ^ e p ∣ D) :
    (∏ p ∈ S, (p : ℤ) ^ e p) ∣ D := by
  apply Finset.prod_dvd_of_coprime ?_ hdiv
  intro p hp q hq hpq
  simpa only [Nat.cast_pow] using
    (Nat.coprime_pow_primes (e p) (e q) (hS p hp) (hS q hq) hpq).isCoprime

/-- Each nonzero integer is at least the product of its pairwise coprime
prime-power divisors. Taking logarithms adds their contributions. -/
theorem sum_log_prime_powers_le (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime)
    (e : ℕ → ℕ) (D : ℤ) (hD : D ≠ 0) (hdiv : ∀ p ∈ S, (p : ℤ) ^ e p ∣ D) :
    (∑ p ∈ S, (e p : ℝ) * Real.log p) ≤ Real.log |(D : ℝ)| := by
  have hprod := prod_prime_powers_dvd S hS e D hdiv
  have hle : (∏ p ∈ S, (p : ℤ) ^ e p) ≤ |D| :=
    Int.le_of_dvd (abs_pos.mpr hD) ((dvd_abs _ _).mpr hprod)
  have hleR : (∏ p ∈ S, (p : ℝ) ^ e p) ≤ |(D : ℝ)| := by exact_mod_cast hle
  have hpos : (0 : ℝ) < ∏ p ∈ S, (p : ℝ) ^ e p := by
    apply Finset.prod_pos
    intro p hp
    exact pow_pos (Nat.cast_pos.mpr (hS p hp).pos) _
  calc
    _ = Real.log (∏ p ∈ S, (p : ℝ) ^ e p) := by
      rw [Real.log_prod]
      · simp only [Real.log_pow]
      · intro p hp
        exact pow_ne_zero _ (by exact_mod_cast (hS p hp).ne_zero)
    _ ≤ _ := Real.log_le_log hpos hleR

lemma log_prime_power_add_sum_le (p : ℕ) (hp : p.Prime) (r : ℕ)
    (S : Finset ℕ) (hpS : p ∉ S) (hS : ∀ q ∈ S, q.Prime)
    (e : ℕ → ℕ) (D : ℤ) (hD : D ≠ 0) (hpr : (p : ℤ) ^ r ∣ D)
    (hdiv : ∀ q ∈ S, (q : ℤ) ^ e q ∣ D) :
    (r : ℝ) * Real.log p + (∑ q ∈ S, (e q : ℝ) * Real.log q) ≤
      Real.log |(D : ℝ)| := by
  have he (q) (hq : q ∈ S) : q ≠ p := fun h => hpS (h ▸ hq)
  have hprime (q) (hq : q ∈ insert p S) : q.Prime := by
    rcases Finset.mem_insert.mp hq with rfl | hq
    · exact hp
    · exact hS q hq
  have hdvd (q) (hq : q ∈ insert p S) :
      (q : ℤ) ^ (if q = p then r else e q) ∣ D := by
    rcases Finset.mem_insert.mp hq with rfl | hq
    · simpa only [ite_true] using hpr
    · simpa only [if_neg (he q hq)] using hdiv q hq
  have h := sum_log_prime_powers_le (insert p S) hprime
    (fun q => if q = p then r else e q) D hD hdvd
  rw [Finset.sum_insert hpS] at h
  simpa only [ite_true, Finset.sum_congr rfl (fun q hq =>
    show ((if q = p then r else e q : ℕ) : ℝ) * Real.log q =
      (e q : ℝ) * Real.log q by rw [if_neg (he q hq)])] using h

#print axioms sum_log_prime_powers_le
-- 'Erdos477.Counting.sum_log_prime_powers_le' depends on axioms:
-- [propext, Classical.choice, Quot.sound]

end Erdos477.Counting
