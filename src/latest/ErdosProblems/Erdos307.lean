import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic.NormNum

/--
Erdős Problem 307: Can three consecutive integers have strictly decreasing largest prime factors?
Answer: Yes. The sequence 13, 14, 15 is a valid counterexample.
-/
theorem erdos_307 : ∃ n : ℕ,
  ∃ p1 p2 p3 : ℕ,
    p1.Prime ∧ p1 ∣ n - 1 ∧ (∀ q, q.Prime → q ∣ n - 1 → q ≤ p1) ∧
    p2.Prime ∧ p2 ∣ n ∧ (∀ q, q.Prime → q ∣ n → q ≤ p2) ∧
    p3.Prime ∧ p3 ∣ n + 1 ∧ (∀ q, q.Prime → q ∣ n + 1 → q ≤ p3) ∧
    p1 > p2 ∧ p2 > p3 := by
  use 14, 13, 7, 5
  have h1 : 14 - 1 = 13 := by norm_num
  have h2 : 14 = 2 * 7 := by norm_num
  have h3 : 14 + 1 = 3 * 5 := by norm_num
  refine ⟨by decide, ?_, ?_, by decide, ?_, ?_, by decide, ?_, ?_, by decide⟩
  · rw [h1]
  · intro q hq hq13
    rw [h1] at hq13
    have : q = 13 := (Nat.prime_dvd_prime_iff_eq hq (by decide)).mp hq13
    exact le_of_eq this
  · rw [h2]
    exact dvd_mul_left 7 2
  · intro q hq hq14
    rw [h2] at hq14
    rcases (Nat.Prime.dvd_mul hq).mp hq14 with hq2 | hq7
    · have : q = 2 := (Nat.prime_dvd_prime_iff_eq hq (by decide)).mp hq2
      rw [this]
      decide
    · have : q = 7 := (Nat.prime_dvd_prime_iff_eq hq (by decide)).mp hq7
      exact le_of_eq this
  · rw [h3]
    exact dvd_mul_left 5 3
  · intro q hq hq15
    rw [h3] at hq15
    rcases (Nat.Prime.dvd_mul hq).mp hq15 with hq3 | hq5
    · have : q = 3 := (Nat.prime_dvd_prime_iff_eq hq (by decide)).mp hq3
      rw [this]
      decide
    · have : q = 5 := (Nat.prime_dvd_prime_iff_eq hq (by decide)).mp hq5
      exact le_of_eq this
