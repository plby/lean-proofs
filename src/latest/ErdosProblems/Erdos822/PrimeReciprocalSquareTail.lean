/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos387.PrimeReciprocalBound
import ErdosProblems.Erdos822.FinsetSumUnion

/-! # The logarithmically sharpened reciprocal-prime-square tail -/

namespace Erdos822

open scoped BigOperators Classical

theorem sum_inv_two_pow_Ico_le (J K : ℕ) :
    ∑ j ∈ Finset.Ico J K, (1 : ℝ) / (2 : ℝ) ^ j ≤ 2 / (2 : ℝ) ^ J := by
  rw [Finset.sum_Ico_eq_sum_range]
  calc
    (∑ i ∈ Finset.range (K - J), (1 : ℝ) / (2 : ℝ) ^ (J + i)) =
        (1 / (2 : ℝ) ^ J) * ∑ i ∈ Finset.range (K - J), (1 / 2 : ℝ) ^ i := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      simp [pow_add, div_eq_mul_inv, mul_comm]
    _ ≤ (1 / (2 : ℝ) ^ J) * 2 :=
      mul_le_mul_of_nonneg_left (sum_geometric_two_le (K - J)) (by positivity)
    _ = 2 / (2 : ℝ) ^ J := by ring

theorem sum_inv_sq_primeLogShell_le_card (N j : ℕ) :
    (∑ p ∈ Erdos387.PrimeReciprocal.primeLogShell N j, (1 : ℝ) / (p : ℝ) ^ 2) ≤
      (Erdos387.PrimeReciprocal.primeLogShell N j).card / ((2 : ℝ) ^ j) ^ 2 := by
  calc
    (∑ p ∈ Erdos387.PrimeReciprocal.primeLogShell N j, (1 : ℝ) / (p : ℝ) ^ 2) ≤
        ∑ _p ∈ Erdos387.PrimeReciprocal.primeLogShell N j,
          (1 : ℝ) / ((2 : ℝ) ^ j) ^ 2 := by
      apply Finset.sum_le_sum
      intro p hp
      have hp' := Finset.mem_filter.mp hp
      have hprime := (Nat.mem_primesLE.mp hp'.1).2
      have hpowNat : 2 ^ j ≤ p := by
        rw [← hp'.2]
        exact Nat.pow_log_le_self 2 hprime.ne_zero
      have hpow : (2 : ℝ) ^ j ≤ p := by exact_mod_cast hpowNat
      exact one_div_le_one_div_of_le (by positivity)
        ((sq_le_sq₀ (by positivity) (by positivity)).mpr hpow)
    _ = (Erdos387.PrimeReciprocal.primeLogShell N j).card / ((2 : ℝ) ^ j) ^ 2 := by
      simp [div_eq_mul_inv]

theorem sum_inv_sq_primeLogShell_le_of_chebyshev
    {C : ℝ} (hC : 0 < C)
    (hpi : ∀ t : ℕ, 2 ≤ t → (Nat.primeCounting t : ℝ) ≤ C * t / Real.log (t : ℝ))
    {N y j : ℕ} (hy : 2 ≤ y) (hj : Nat.log 2 y ≤ j) :
    (∑ p ∈ Erdos387.PrimeReciprocal.primeLogShell N j, (1 : ℝ) / (p : ℝ) ^ 2) ≤
      (2 * C / Real.log (y : ℝ)) * (1 / (2 : ℝ) ^ j) := by
  have hyR : (0 : ℝ) < y := by exact_mod_cast (show 0 < y by omega)
  have hlogy : 0 < Real.log (y : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < y by omega))
  have hT2 : 2 ≤ 2 ^ (j + 1) := by
    simpa using Nat.pow_le_pow_right (n := 2) (by norm_num) (show 1 ≤ j + 1 by omega)
  have hyT : y ≤ 2 ^ (j + 1) :=
    (Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) y).le.trans
      (Nat.pow_le_pow_right (by norm_num) (by omega))
  have hlogle : Real.log (y : ℝ) ≤ Real.log ((2 ^ (j + 1) : ℕ) : ℝ) :=
    Real.log_le_log hyR (by exact_mod_cast hyT)
  have hpi' : (Nat.primeCounting (2 ^ (j + 1)) : ℝ) ≤
      C * (2 : ℝ) ^ (j + 1) / Real.log (y : ℝ) := by
    have h := hpi (2 ^ (j + 1)) hT2
    have hdiv := div_le_div_of_nonneg_left
      (show 0 ≤ C * ((2 ^ (j + 1) : ℕ) : ℝ) by positivity) hlogy hlogle
    simpa only [Nat.cast_pow, Nat.cast_ofNat] using h.trans hdiv
  have hcard : (Erdos387.PrimeReciprocal.primeLogShell N j).card ≤
      Nat.primeCounting (2 ^ (j + 1)) :=
    Erdos387.PrimeReciprocal.card_primeLogShell_le_primeCounting N j
  have hcardR : ((Erdos387.PrimeReciprocal.primeLogShell N j).card : ℝ) ≤
      Nat.primeCounting (2 ^ (j + 1)) := by exact_mod_cast hcard
  calc
    (∑ p ∈ Erdos387.PrimeReciprocal.primeLogShell N j, (1 : ℝ) / (p : ℝ) ^ 2) ≤
        (Erdos387.PrimeReciprocal.primeLogShell N j).card / ((2 : ℝ) ^ j) ^ 2 :=
      sum_inv_sq_primeLogShell_le_card N j
    _ ≤ (C * (2 : ℝ) ^ (j + 1) / Real.log (y : ℝ)) / ((2 : ℝ) ^ j) ^ 2 :=
      div_le_div_of_nonneg_right (hcardR.trans hpi') (by positivity)
    _ = (2 * C / Real.log (y : ℝ)) * (1 / (2 : ℝ) ^ j) := by
      rw [pow_succ]
      field_simp

/-- Chebyshev's prime-counting upper bound supplies the logarithmic saving
missing from the unrestricted integer reciprocal-square tail. -/
theorem exists_sum_inv_sq_primesAbove_le :
    ∃ C : ℝ, 0 < C ∧ ∀ N y : ℕ, 2 ≤ y →
      (∑ p ∈ (Nat.primesLE N).filter (fun p ↦ y < p), (1 : ℝ) / (p : ℝ) ^ 2) ≤
        C / ((y : ℝ) * Real.log (y : ℝ)) := by
  obtain ⟨C, hC, hpi⟩ := Erdos387.PrimeReciprocal.exists_uniform_primeCounting_le_div_log_all
  refine ⟨8 * C, by positivity, ?_⟩
  intro N y hy
  let J := Nat.log 2 y
  let K := Nat.log 2 N + 1
  have hlogy : 0 < Real.log (y : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < y by omega))
  have hyR : (0 : ℝ) < y := by exact_mod_cast (show 0 < y by omega)
  have hsub : (Nat.primesLE N).filter (fun p ↦ y < p) ⊆
      (Finset.Ico J K).biUnion (Erdos387.PrimeReciprocal.primeLogShell N) := by
    intro p hp
    obtain ⟨hpN, hyp⟩ := Finset.mem_filter.mp hp
    have hpUpper := (Nat.mem_primesLE.mp hpN).1
    exact Finset.mem_biUnion.mpr ⟨Nat.log 2 p,
      Finset.mem_Ico.mpr ⟨Nat.log_mono_right hyp.le,
        Nat.lt_succ_of_le (Nat.log_mono_right hpUpper)⟩,
      Finset.mem_filter.mpr ⟨hpN, rfl⟩⟩
  have hgeom : 2 / (2 : ℝ) ^ J ≤ 4 / (y : ℝ) := by
    have hyPower : (y : ℝ) ≤ 2 * (2 : ℝ) ^ J := by
      have h := (Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) y).le
      have h' : (y : ℝ) ≤ (2 : ℝ) ^ (J + 1) := by exact_mod_cast h
      simpa [pow_succ, mul_comm] using h'
    apply (div_le_div_iff₀ (by positivity : (0 : ℝ) < (2 : ℝ) ^ J) hyR).mpr
    nlinarith
  calc
    (∑ p ∈ (Nat.primesLE N).filter (fun p ↦ y < p), (1 : ℝ) / (p : ℝ) ^ 2) ≤
        ∑ p ∈ (Finset.Ico J K).biUnion (Erdos387.PrimeReciprocal.primeLogShell N),
          (1 : ℝ) / (p : ℝ) ^ 2 :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun p hp hnot ↦ by positivity)
    _ ≤ ∑ j ∈ Finset.Ico J K,
        ∑ p ∈ Erdos387.PrimeReciprocal.primeLogShell N j, (1 : ℝ) / (p : ℝ) ^ 2 :=
      sum_biUnion_le_sum _ _ _ (fun j hj p hp ↦ by positivity)
    _ ≤ ∑ j ∈ Finset.Ico J K, (2 * C / Real.log (y : ℝ)) * (1 / (2 : ℝ) ^ j) := by
      exact Finset.sum_le_sum fun j hj ↦
        sum_inv_sq_primeLogShell_le_of_chebyshev hC hpi hy (Finset.mem_Ico.mp hj).1
    _ = (2 * C / Real.log (y : ℝ)) * ∑ j ∈ Finset.Ico J K, (1 / (2 : ℝ) ^ j) := by
      rw [Finset.mul_sum]
    _ ≤ (2 * C / Real.log (y : ℝ)) * (2 / (2 : ℝ) ^ J) :=
      mul_le_mul_of_nonneg_left (sum_inv_two_pow_Ico_le J K) (by positivity)
    _ ≤ (2 * C / Real.log (y : ℝ)) * (4 / (y : ℝ)) :=
      mul_le_mul_of_nonneg_left hgeom (by positivity)
    _ = 8 * C / ((y : ℝ) * Real.log (y : ℝ)) := by ring

#print axioms exists_sum_inv_sq_primesAbove_le

end Erdos822
