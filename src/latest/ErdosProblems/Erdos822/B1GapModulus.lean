/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos822.B1Asymptotic
import ErdosProblems.Erdos851.EulerMass

/-! # The intermediate-prime exclusion modulus -/

namespace Erdos822

open Filter
open scoped BigOperators

def gapPrimeSet (y Z : ℕ) : Finset ℕ := insert 2 (Erdos851.sievePrimes y Z)

def gapModulus (y Z : ℕ) : ℕ := ∏ p ∈ gapPrimeSet y Z, p

def b1GapModulus (N : ℕ) : ℕ := gapModulus (b1Cutoff N) (b1DoubleLog N)

theorem prime_of_mem_gapPrimeSet {y Z p : ℕ} (hp : p ∈ gapPrimeSet y Z) : p.Prime := by
  rcases Finset.mem_insert.mp hp with rfl | hp
  · exact Nat.prime_two
  · exact (Erdos851.mem_sievePrimes.mp hp).2.2

theorem gapModulus_pos (y Z : ℕ) : 0 < gapModulus y Z := by
  exact Finset.prod_pos fun p hp ↦ (prime_of_mem_gapPrimeSet hp).pos

theorem primeFactors_gapModulus (y Z : ℕ) :
    (gapModulus y Z).primeFactors = gapPrimeSet y Z :=
  Nat.primeFactors_prod fun _p hp ↦ prime_of_mem_gapPrimeSet hp

theorem gapModulus_coprime_iff (y Z n : ℕ) :
    (gapModulus y Z).Coprime n ↔
      Odd n ∧ ∀ p : ℕ, p.Prime → y < p → p ≤ Z → ¬ p ∣ n := by
  rw [gapModulus, Nat.coprime_prod_left_iff]
  constructor
  · intro h
    refine ⟨Nat.coprime_two_left.mp (h 2 (Finset.mem_insert_self _ _)), ?_⟩
    intro p hp hyp hpZ
    apply hp.coprime_iff_not_dvd.mp
    exact h p (Finset.mem_insert_of_mem (Erdos851.mem_sievePrimes.mpr ⟨hyp, hpZ, hp⟩))
  · rintro ⟨hn, h⟩ p hp
    rcases Finset.mem_insert.mp hp with rfl | hp
    · exact Nat.coprime_two_left.mpr hn
    · obtain ⟨hyp, hpZ, hprime⟩ := Erdos851.mem_sievePrimes.mp hp
      exact hprime.coprime_iff_not_dvd.mpr (h p hprime hyp hpZ)

theorem gapModulus_totient_ratio {y Z : ℕ} (hy : 2 ≤ y) :
    (Nat.totient (gapModulus y Z) : ℝ) / gapModulus y Z =
      (1 / 2 : ℝ) * Erdos851.localEulerProduct Erdos851.oneShiftDensity y Z := by
  have hQpos : (0 : ℝ) < gapModulus y Z := by exact_mod_cast gapModulus_pos y Z
  have hprod := congrArg (fun q : ℚ ↦ (q : ℝ))
    (Nat.totient_eq_mul_prod_factors (gapModulus y Z))
  push_cast at hprod
  have htwo : 2 ∉ Erdos851.sievePrimes y Z := by
    intro h
    have := (Erdos851.mem_sievePrimes.mp h).1
    omega
  rw [primeFactors_gapModulus, gapPrimeSet, Finset.prod_insert htwo] at hprod
  norm_num at hprod
  unfold Erdos851.localEulerProduct Erdos851.oneShiftDensity
  apply (div_eq_iff hQpos.ne').mpr
  nlinarith [hprod]

/-- Weak Mertens and the fourth-root logarithm ratio give a positive
uniform density of admissible residue classes. -/
theorem exists_b1GapModulus_totient_ratio_lower :
    ∃ δ : ℝ, 0 < δ ∧ ∀ N : ℕ, 2 ≤ b1Cutoff N →
      δ ≤ (Nat.totient (b1GapModulus N) : ℝ) / b1GapModulus N := by
  obtain ⟨C, hC, hdim⟩ := Erdos851.exists_oneShift_dimension_bound
  refine ⟨1 / (16 * C), by positivity, ?_⟩
  intro N hy
  let y := b1Cutoff N
  let Z := b1DoubleLog N
  let V := Erdos851.localEulerProduct Erdos851.oneShiftDensity y Z
  have hyZ : y ≤ Z := nthRoot_le_self_of_pos (by norm_num)
  have hratio : Real.log (Z : ℝ) / Real.log (y : ℝ) ≤ 8 := by
    simpa [y, Z, b1Cutoff] using
      (log_div_log_slowSieveCutoff_le (N := b1DoubleLog N) (S := 1)
        (by norm_num) (by simpa [b1Cutoff] using hy))
  have hinv := hdim y Z hy hyZ
  rw [Erdos851.inverseLocalEulerProduct_eq_inv] at hinv
  have hinv' : V⁻¹ ≤ 8 * C := by
    have hm := mul_le_mul_of_nonneg_left hratio hC.le
    dsimp [V]
    nlinarith
  have hVpos : 0 < V := Erdos851.oneShift_localEulerProduct_pos
  have hV : (8 * C)⁻¹ ≤ V :=
    (inv_le_comm₀ hVpos (by positivity)).mp hinv'
  rw [b1GapModulus, gapModulus_totient_ratio hy]
  change 1 / (16 * C) ≤ (1 / 2 : ℝ) * V
  calc
    1 / (16 * C) = (1 / 2 : ℝ) * (8 * C)⁻¹ := by ring
    _ ≤ (1 / 2 : ℝ) * V := mul_le_mul_of_nonneg_left hV (by norm_num)

/-- A crude period bound suffices because `Z` is only a double logarithm. -/
theorem gapModulus_le_two_pow_sq {y Z : ℕ} (hZ : 2 ≤ Z) :
    gapModulus y Z ≤ 2 ^ (Z ^ 2) := by
  have hle : ∀ p ∈ gapPrimeSet y Z, p ≤ Z := by
    intro p hp
    rcases Finset.mem_insert.mp hp with rfl | hp
    · exact hZ
    · exact (Erdos851.mem_sievePrimes.mp hp).2.1
  have hcard : (gapPrimeSet y Z).card ≤ Z := by
    calc
      (gapPrimeSet y Z).card ≤ (Finset.Icc 1 Z).card := by
        apply Finset.card_le_card
        intro p hp
        exact Finset.mem_Icc.mpr ⟨(prime_of_mem_gapPrimeSet hp).one_le, hle p hp⟩
      _ = Z := by simp
  calc
    gapModulus y Z ≤ Z ^ (gapPrimeSet y Z).card := Finset.prod_le_pow_card _ _ _ hle
    _ ≤ Z ^ Z := Nat.pow_le_pow_right (by omega) hcard
    _ ≤ (2 ^ Z) ^ Z := Nat.pow_le_pow_left Nat.lt_two_pow_self.le Z
    _ = 2 ^ (Z ^ 2) := by rw [← pow_mul, pow_two]

end Erdos822
