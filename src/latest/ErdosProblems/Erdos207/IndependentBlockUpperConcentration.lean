/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.IndependentBlockConcentration
import Mathlib.Analysis.Complex.ExponentialBounds

/-! # Exponential generating bound for the upper tail of disjoint active blocks -/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

theorem independentBits_probability_activeBlocks_card_ge_mul_pow_le
    {I J : Type*} [Fintype I] [DecidableEq I] [DecidableEq J]
    (p : I → ℝ≥0) (hp : ∀ i, p i ≤ 1) (blocks : J → Finset I) (S : Finset J)
    (hpair : (S : Set J).PairwiseDisjoint blocks) (q : ℝ≥0) (hqle : q ≤ 1)
    (huniform : ∀ j ∈ S, blockProbability p blocks j = q) (k : ℕ) :
    (FiniteLaw.independentBits p hp).probability
      (fun ω ↦ k ≤ (activeBlocks blocks S ω).card) * (2 : ℝ≥0) ^ k ≤ (1 + q) ^ S.card := by
  classical
  let L := FiniteLaw.independentBits p hp
  let Bad := S.powerset.filter fun A ↦ k ≤ A.card
  have hraw : L.probability (fun ω ↦ k ≤ (activeBlocks blocks S ω).card) ≤
      ∑ A ∈ Bad, q ^ A.card * (1 - q) ^ (S.card - A.card) := by
    calc
      _ ≤ L.probability (fun ω ↦ ∃ A ∈ Bad, activeBlocks blocks S ω = A) := by
        apply L.probability_mono
        intro ω hcard
        refine ⟨activeBlocks blocks S ω, mem_filter.mpr ⟨mem_powerset.mpr ?_, hcard⟩, rfl⟩
        intro j hj
        exact (mem_activeBlocks_iff.mp hj).1
      _ ≤ ∑ A ∈ Bad, L.probability (fun ω ↦ activeBlocks blocks S ω = A) :=
        L.probability_exists_le Bad _
      _ = _ := by
        apply sum_congr rfl
        intro A hA
        exact independentBits_probability_activeBlocks_eq p hp blocks S A hpair
          (mem_powerset.mp (mem_filter.mp hA).1) q huniform
  have hsplit : 2 * q + (1 - q) = 1 + q := by
    calc
      2 * q + (1 - q) = q + (q + (1 - q)) := by ring
      _ = q + 1 := by rw [add_tsub_cancel_of_le hqle]
      _ = _ := add_comm _ _
  calc
    _ ≤ (∑ A ∈ Bad, q ^ A.card * (1 - q) ^ (S.card - A.card)) * (2 : ℝ≥0) ^ k :=
      mul_le_mul_of_nonneg_right hraw zero_le
    _ = ∑ A ∈ Bad, (q ^ A.card * (1 - q) ^ (S.card - A.card)) * (2 : ℝ≥0) ^ k := by rw [sum_mul]
    _ ≤ ∑ A ∈ Bad, (2 * q) ^ A.card * (1 - q) ^ (S.card - A.card) := by
      apply sum_le_sum
      intro A hA
      have hpow : (2 : ℝ≥0) ^ k ≤ 2 ^ A.card :=
        pow_le_pow_right₀ (by norm_num) (mem_filter.mp hA).2
      calc
        _ ≤ (q ^ A.card * (1 - q) ^ (S.card - A.card)) * (2 : ℝ≥0) ^ A.card :=
          mul_le_mul_of_nonneg_left hpow zero_le
        _ = _ := by rw [mul_pow]; ring
    _ ≤ ∑ A ∈ S.powerset, (2 * q) ^ A.card * (1 - q) ^ (S.card - A.card) :=
      sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun _ _ _ ↦ zero_le)
    _ = _ := by rw [sum_powerset_split_probabilities, hsplit]

theorem independentBits_probability_activeBlocks_card_ge_mul_pow_le_exp
    {I J : Type*} [Fintype I] [DecidableEq I] [DecidableEq J]
    (p : I → ℝ≥0) (hp : ∀ i, p i ≤ 1) (blocks : J → Finset I) (S : Finset J)
    (hpair : (S : Set J).PairwiseDisjoint blocks) (q : ℝ≥0) (hqle : q ≤ 1)
    (huniform : ∀ j ∈ S, blockProbability p blocks j = q) (k : ℕ) :
    ((FiniteLaw.independentBits p hp).probability
      (fun ω ↦ k ≤ (activeBlocks blocks S ω).card) : ℝ) * (2 : ℝ) ^ k ≤
        Real.exp ((q : ℝ) * S.card) := by
  have hgen : ((FiniteLaw.independentBits p hp).probability
      (fun ω ↦ k ≤ (activeBlocks blocks S ω).card) : ℝ) * (2 : ℝ) ^ k ≤
        (1 + (q : ℝ)) ^ S.card := by
    exact_mod_cast independentBits_probability_activeBlocks_card_ge_mul_pow_le
      p hp blocks S hpair q hqle huniform k
  apply hgen.trans
  calc
    (1 + (q : ℝ)) ^ S.card ≤ (Real.exp (q : ℝ)) ^ S.card := by
      apply pow_le_pow_left₀ (by positivity)
      simpa only [add_comm] using Real.add_one_le_exp (q : ℝ)
    _ = _ := by rw [← Real.exp_nat_mul]; congr 1; ring

theorem independentBits_probability_activeBlocks_card_ge_le_exp
    {I J : Type*} [Fintype I] [DecidableEq I] [DecidableEq J]
    (p : I → ℝ≥0) (hp : ∀ i, p i ≤ 1) (blocks : J → Finset I) (S : Finset J)
    (hpair : (S : Set J).PairwiseDisjoint blocks) (q : ℝ≥0) (hqle : q ≤ 1)
    (huniform : ∀ j ∈ S, blockProbability p blocks j = q)
    (k : ℕ) (hk : 4 * ((q : ℝ) * S.card) ≤ k) :
    ((FiniteLaw.independentBits p hp).probability
      (fun ω ↦ k ≤ (activeBlocks blocks S ω).card) : ℝ) ≤ Real.exp (-(k : ℝ) / 4) := by
  have hgen := independentBits_probability_activeBlocks_card_ge_mul_pow_le_exp
    p hp blocks S hpair q hqle huniform k
  have htwo : (0 : ℝ) < 2 ^ k := pow_pos (by norm_num) _
  apply (mul_le_mul_iff_left₀ htwo).mp
  apply hgen.trans
  have hpow : (2 : ℝ) ^ k = Real.exp ((k : ℝ) * Real.log 2) := by
    rw [Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
  rw [hpow, ← Real.exp_add, Real.exp_le_exp]
  have hlog : (1 / 2 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hmul := mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg k : (0 : ℝ) ≤ k)
  linarith

theorem independentBits_probability_activeBlocks_card_ge_le_dyadic
    {I J : Type*} [Fintype I] [DecidableEq I] [DecidableEq J]
    (p : I → ℝ≥0) (hp : ∀ i, p i ≤ 1) (blocks : J → Finset I) (S : Finset J)
    (hpair : (S : Set J).PairwiseDisjoint blocks) (q : ℝ≥0) (hqle : q ≤ 1)
    (huniform : ∀ j ∈ S, blockProbability p blocks j = q)
    (k s : ℕ) (hk : 4 * ((q : ℝ) * S.card) ≤ k) (hs : 4 * s ≤ k) :
    (FiniteLaw.independentBits p hp).probability
      (fun ω ↦ k ≤ (activeBlocks blocks S ω).card) ≤ ((2 : ℝ≥0) ^ s)⁻¹ := by
  have h := independentBits_probability_activeBlocks_card_ge_le_exp p hp blocks S hpair q hqle huniform k hk
  have hR : ((FiniteLaw.independentBits p hp).probability
      (fun ω ↦ k ≤ (activeBlocks blocks S ω).card) : ℝ) ≤ ((2 : ℝ) ^ s)⁻¹ := by
    calc
      _ ≤ Real.exp (-(k : ℝ) / 4) := h
      _ ≤ Real.exp (-(s : ℝ)) := by
        rw [Real.exp_le_exp]
        have hsR : (4 : ℝ) * s ≤ k := by exact_mod_cast hs
        linarith
      _ = (Real.exp (-1)) ^ s := by rw [← Real.exp_nat_mul]; congr 1; ring
      _ ≤ (1 / 2 : ℝ) ^ s := pow_le_pow_left₀ (Real.exp_nonneg _) Real.exp_neg_one_lt_half.le _
      _ = _ := by rw [one_div, inv_pow]
  exact_mod_cast hR

end

end Erdos207
