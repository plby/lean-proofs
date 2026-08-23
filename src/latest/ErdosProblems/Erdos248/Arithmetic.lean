import ErdosProblems.Erdos248.Core
import Mathlib.NumberTheory.Primorial

/-!
# Erdős Problem 248: elementary arithmetic reductions

This file isolates the deterministic estimates used outside the weighted
sieve: `omega` is the cardinality of the prime-factor finset, its exponential
is bounded by the integer, very far shifts are harmless, and the primorial
congruence identifies tiny prime divisors with prime divisors of the shift.
-/

open scoped ArithmeticFunction.omega

namespace Erdos248

/-- The arithmetic-function notation `omega` agrees with the cardinality of
the natural prime-factor finset. -/
theorem omega_eq_primeFactors_card (m : ℕ) :
    ω m = m.primeFactors.card := by
  rw [ArithmeticFunction.cardDistinctFactors_apply]
  exact (List.card_toFinset m.primeFactorsList).symm

/-- The product of the distinct prime factors of a positive integer is at
least two to the number of those factors. -/
theorem two_pow_omega_le {m : ℕ} (hm : m ≠ 0) :
    2 ^ ω m ≤ m := by
  rw [omega_eq_primeFactors_card]
  calc
    2 ^ m.primeFactors.card = ∏ _p ∈ m.primeFactors, 2 := by simp
    _ ≤ ∏ p ∈ m.primeFactors, p := by
      apply Finset.prod_le_prod
      · intro p hp
        exact Nat.zero_le 2
      intro p hp
      exact (Nat.prime_of_mem_primeFactors hp).two_le
    _ ≤ m := Nat.le_of_dvd (Nat.pos_of_ne_zero hm)
      (Nat.prod_primeFactors_dvd m)

/-- Exponent comparison form of `two_pow_omega_le`. -/
theorem omega_le_of_le_two_pow {m a : ℕ} (hm : m ≠ 0)
    (hma : m ≤ 2 ^ a) :
    ω m ≤ a := by
  rw [← Nat.pow_le_pow_iff_right (by decide : 1 < 2)]
  exact (two_pow_omega_le hm).trans hma

/-- Once the shift is at least the binary scale containing `n`, the desired
linear bound is completely elementary. -/
theorem omega_add_le_two_mul_of_le_pow {n L k : ℕ}
    (hn : n ≤ 2 ^ L) (hLk : L ≤ k) (hk : 1 ≤ k) :
    ω (n + k) ≤ 2 * k := by
  apply omega_le_of_le_two_pow (by omega)
  have hn_pow : n ≤ 2 ^ k :=
    hn.trans (Nat.pow_le_pow_right (by decide : 0 < 2) hLk)
  have hk_pow : k ≤ 2 ^ k := k.lt_two_pow_self.le
  calc
    n + k ≤ 2 ^ k + 2 ^ k := Nat.add_le_add hn_pow hk_pow
    _ = 2 ^ (k + 1) := by rw [pow_succ]; omega
    _ ≤ 2 ^ (2 * k) := by
      apply Nat.pow_le_pow_right (by decide : 0 < 2)
      omega

/-- A prime below the pre-sieving cutoff divides `n + k` exactly when it
divides `k`, provided the square of the cutoff primorial divides `n`. -/
theorem prime_dvd_add_iff_of_primorial_sq_dvd
    {n k w p : ℕ} (hW : primorial w ^ 2 ∣ n)
    (hp : p.Prime) (hpw : p ≤ w) :
    p ∣ n + k ↔ p ∣ k := by
  have hpW : p ∣ primorial w := hp.dvd_primorial_iff.mpr hpw
  have hpn : p ∣ n :=
    (hpW.trans (dvd_pow_self _ (by omega))).trans hW
  simpa [Nat.add_comm] using (Nat.dvd_add_iff_left hpn).symm

/-- The square on the pre-sieve modulus is unnecessary when only distinct
prime divisors are counted. -/
theorem prime_dvd_add_iff_of_primorial_dvd
    {n k w p : ℕ} (hW : primorial w ∣ n)
    (hp : p.Prime) (hpw : p ≤ w) :
    p ∣ n + k ↔ p ∣ k := by
  have hpW : p ∣ primorial w := hp.dvd_primorial_iff.mpr hpw
  have hpn : p ∣ n := hpW.trans hW
  simpa [Nat.add_comm] using (Nat.dvd_add_iff_left hpn).symm

end Erdos248
