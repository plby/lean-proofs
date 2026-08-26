/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos822.PrimeSquareIncidence
import Mathlib.Analysis.PSeries

/-!
# The finite range of repeated shifted prime factors

A repeated prime factor of a shifted cofactor at scale N is at most
2*N^14.  The reciprocal-square mass of all primes above y in that finite
range is bounded by 1/y using the elementary p-series telescope.
-/

namespace Erdos822

open scoped BigOperators

/-- Candidate primes above y whose square can divide a shifted cofactor at
scale N. -/
def largeSquarePrimes (N y : ℕ) : Finset ℕ :=
  (Finset.Ioc y (2 * N ^ 14)).filter Nat.Prime

@[simp]
theorem mem_largeSquarePrimes_iff {N y p : ℕ} :
    p ∈ largeSquarePrimes N y ↔
      y < p ∧ p ≤ 2 * N ^ 14 ∧ p.Prime := by
  simp [largeSquarePrimes, and_assoc]

/-- A repeated prime factor of a shifted odd raw cofactor lies in the
explicit square-prime range. -/
theorem prime_le_two_mul_pow_fourteen_of_sq_dvd_shifted
    {N m p : ℕ} (hN : 1 ≤ N) (hm : m ∈ oddRawCofactors N)
    (hp : p.Prime) (hpsq : p ^ 2 ∣ shiftedTotient m) :
    p ≤ 2 * N ^ 14 := by
  have hmle : m ≤ N ^ 28 := oddRawCofactors_le_pow_twenty_eight hm
  have hshiftle : shiftedTotient m ≤ 2 * N ^ 28 :=
    (shiftedTotient_le_two_mul m).trans
      (Nat.mul_le_mul_left 2 hmle)
  have hshiftpos : 0 < shiftedTotient m := by
    have hmpos := oddRawCofactors_pos hm
    exact hmpos.trans_le (Nat.le_add_right m (Nat.totient m))
  have hsqle : p ^ 2 ≤ shiftedTotient m :=
    Nat.le_of_dvd hshiftpos hpsq
  by_contra hnot
  have hgt : 2 * N ^ 14 < p := by omega
  have hsquare : (2 * N ^ 14) ^ 2 < p ^ 2 :=
    Nat.pow_lt_pow_left hgt (by norm_num)
  have hNpow : 0 < N ^ 28 := by positivity
  have hdouble : 2 * N ^ 28 < (2 * N ^ 14) ^ 2 := by
    rw [show (2 * N ^ 14) ^ 2 = 4 * N ^ 28 by ring]
    omega
  omega

theorem mem_largeSquarePrimes_of_sq_dvd_shifted
    {N y m p : ℕ} (hN : 1 ≤ N) (hm : m ∈ oddRawCofactors N)
    (hp : p.Prime) (hyp : y < p)
    (hpsq : p ^ 2 ∣ shiftedTotient m) :
    p ∈ largeSquarePrimes N y := by
  rw [mem_largeSquarePrimes_iff]
  exact ⟨hyp,
    prime_le_two_mul_pow_fourteen_of_sq_dvd_shifted hN hm hp hpsq,
    hp⟩

/-- The candidate square-prime range has at most its endpoint many
elements. -/
theorem largeSquarePrimes_card_le (N y : ℕ) :
    (largeSquarePrimes N y).card ≤ 2 * N ^ 14 := by
  calc
    (largeSquarePrimes N y).card ≤ (Finset.Ioc y (2 * N ^ 14)).card :=
      Finset.card_le_card (Finset.filter_subset _ _)
    _ ≤ (Finset.Icc 1 (2 * N ^ 14)).card := by
      apply Finset.card_le_card
      intro n hn
      rw [Finset.mem_Icc]
      have hnData := Finset.mem_Ioc.mp hn
      exact ⟨by omega, hnData.2⟩
    _ = 2 * N ^ 14 := by simp

/-- Reciprocal-square mass of all candidate primes above y is bounded by
1/y. -/
theorem sum_inv_sq_largeSquarePrimes_le_inv
    {N y : ℕ} (hy : 1 ≤ y) :
    ∑ p ∈ largeSquarePrimes N y,
        (1 : ℝ) / (p ^ 2 : ℕ) ≤ (1 : ℝ) / y := by
  by_cases hyU : y ≤ 2 * N ^ 14
  · calc
      (∑ p ∈ largeSquarePrimes N y,
          (1 : ℝ) / (p ^ 2 : ℕ)) ≤
          ∑ n ∈ Finset.Ioc y (2 * N ^ 14),
            (1 : ℝ) / (n ^ 2 : ℕ) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
          (Finset.filter_subset _ _)
        intro n hn hnot
        positivity
      _ ≤ (1 : ℝ) / y - (1 : ℝ) / (2 * N ^ 14) := by
        have h :=
          (sum_Ioc_inv_sq_le_sub (α := ℝ) (k := y)
            (n := 2 * N ^ 14) (by omega) hyU)
        norm_num only [one_div, Nat.cast_pow] at h ⊢
        push_cast at h
        exact h
      _ ≤ (1 : ℝ) / y := by
        have hnonneg : 0 ≤ (1 : ℝ) / (2 * N ^ 14) := by positivity
        linarith
  · have hempty : largeSquarePrimes N y = ∅ := by
      unfold largeSquarePrimes
      have hIoc : Finset.Ioc y (2 * N ^ 14) = ∅ := by
        apply Finset.not_nonempty_iff_eq_empty.mp
        rintro ⟨n, hn⟩
        have hnData := Finset.mem_Ioc.mp hn
        omega
      rw [hIoc]
      simp
    rw [hempty]
    simp

end Erdos822
