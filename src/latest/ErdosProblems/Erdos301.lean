import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Fintype.Card
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.Convex.Gauge
import Mathlib.LinearAlgebra.AffineSpace.AffineMap

open Nat

/-- 
A powerful number is a positive integer n such that for every prime p dividing n, p^2 also divides n.
-/
def IsPowerful (n : ℕ) : Prop :=
  ∀ p : ℕ, Nat.Prime p → p ∣ n → p^2 ∣ n

/--
A perfect square is an integer n such that k * k = n for some integer k.
-/
def IsPerfectSquare (n : ℕ) : Prop :=
  ∃ k : ℕ, k * k = n

lemma powerful_12167 : IsPowerful 12167 := by
  intro p hp hp_div
  have h_eq : 12167 = 23^3 := by norm_num
  rw [h_eq] at hp_div
  have h_div_23 : p ∣ 23 := Nat.Prime.dvd_of_dvd_pow hp hp_div
  have h23_prime : Nat.Prime 23 := by decide
  have hp23 : p = 23 := (Nat.prime_dvd_prime_iff_eq hp h23_prime).mp h_div_23
  rw [hp23]
  norm_num

lemma powerful_12168 : IsPowerful 12168 := by
  intro p hp hp_div
  have h_eq : 12168 = 2^3 * 3^2 * 13^2 := by norm_num
  rw [h_eq] at hp_div
  have h_div_prod : p ∣ (2^3) ∨ p ∣ (3^2 * 13^2) := hp.dvd_mul.mp hp_div
  rcases h_div_prod with h2 | h313
  · have h_div_2 : p ∣ 2 := Nat.Prime.dvd_of_dvd_pow hp h2
    have hp2 : p = 2 := (Nat.prime_dvd_prime_iff_eq hp (by decide)).mp h_div_2
    rw [hp2]
    norm_num
  · have h_div_prod2 : p ∣ (3^2) ∨ p ∣ (13^2) := hp.dvd_mul.mp h313
    rcases h_div_prod2 with h3 | h13
    · have h_div_3 : p ∣ 3 := Nat.Prime.dvd_of_dvd_pow hp h3
      have hp3 : p = 3 := (Nat.prime_dvd_prime_iff_eq hp (by decide)).mp h_div_3
      rw [hp3]
      norm_num
    · have h_div_13 : p ∣ 13 := Nat.Prime.dvd_of_dvd_pow hp h13
      have hp13 : p = 13 := (Nat.prime_dvd_prime_iff_eq hp (by decide)).mp h_div_13
      rw [hp13]
      norm_num

lemma not_square_12167 : ¬ IsPerfectSquare 12167 := by
  intro ⟨k, hk⟩
  have hk_symm : k * k = 12167 := hk
  have h1 : k < 111 ∨ k ≥ 111 := lt_or_ge k 111
  rcases h1 with hl | hg
  · nlinarith
  · nlinarith

lemma not_square_12168 : ¬ IsPerfectSquare 12168 := by
  intro ⟨k, hk⟩
  have hk_symm : k * k = 12168 := hk
  have h1 : k < 111 ∨ k ≥ 111 := lt_or_ge k 111
  rcases h1 with hl | hg
  · nlinarith
  · nlinarith

/-- 
JSP-000301 / Erdős Problem 301:
If two consecutive positive integers are powerful, must at least one be a perfect square?
Counterexample: 12167 and 12168.
-/
theorem jsp_000301 :
  ∃ n : ℕ, n > 0 ∧ IsPowerful n ∧ IsPowerful (n + 1) ∧ ¬ IsPerfectSquare n ∧ ¬ IsPerfectSquare (n + 1) := by
  use 12167
  refine ⟨by decide, powerful_12167, powerful_12168, not_square_12167, not_square_12168⟩
