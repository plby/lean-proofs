/-
Copyright (c) 2026 The Formal Conjectures Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Formal Conjectures Authors
-/

import ErdosProblems.Erdos446.BlockPartition
import ErdosProblems.Erdos446.MassProducts

/-!
# Erdős Problem 446: sharp products for capped block classes

The reciprocal mass of a prime block is `log 2` plus a geometrically
decaying error.  Ford's caps make both the repeated Mertens errors and the
without-replacement losses summable, so their product costs only an absolute
factor rather than a factor exponential in the number of blocks.
-/

namespace Erdos446

open Finset Real
open scoped BigOperators

theorem cappedComposition_linear_cap {M K : ℕ} (hM : 1 ≤ M)
    {b : Fin K → ℕ} (hb : b ∈ cappedCompositions M K) (i : Fin K) :
    extendComposition b i ≤ (M * M) * (i.val + 1) := by
  rw [extendComposition_fin]
  have hcap := (mem_cappedCompositions.mp hb).2 i
  calc
    b i ≤ M * (M + i.val) := hcap
    _ ≤ (M * M) * (i.val + 1) := by
      rw [Nat.mul_add, Nat.mul_add, Nat.mul_one]
      rw [Nat.add_comm (M * M * i.val) (M * M)]
      apply Nat.add_le_add_left
      calc
        M * i.val = M * (1 * i.val) := by simp
        _ ≤ M * (M * i.val) :=
          Nat.mul_le_mul_left M (Nat.mul_le_mul_right i.val hM)
        _ = M * M * i.val := by rw [Nat.mul_assoc]

theorem sum_range_extendComposition {K : ℕ} (b : Fin K → ℕ) :
    (∑ i ∈ Finset.range K, extendComposition b i) = ∑ i : Fin K, b i := by
  rw [← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro i hi
  exact extendComposition_fin b i

theorem slotCount_extendComposition_of_mem {M K : ℕ} {b : Fin K → ℕ}
    (hb : b ∈ cappedCompositions M K) :
    slotCount K (extendComposition b) = K := by
  rw [slotCount]
  simp only [extendComposition_fin]
  exact mem_compositions.mp (mem_cappedCompositions.mp hb).1

theorem card_blockSlot_extendComposition_of_mem {M K : ℕ}
    {b : Fin K → ℕ} (hb : b ∈ cappedCompositions M K) :
    Fintype.card (BlockSlot K (extendComposition b)) = K := by
  rw [card_blockSlot, slotCount_extendComposition_of_mem hb]

theorem blockEndpoint_ge_two_pow (j : ℕ) :
    2 ^ j ≤ blockEndpoint j := by
  unfold blockEndpoint
  exact Nat.pow_le_pow_right (by omega)
    (Nat.le_of_lt j.lt_two_pow_self)

theorem inv_blockEndpoint_le_inv_two_pow (j : ℕ) :
    (1 / (blockEndpoint j : ℝ)) ≤ 1 / (2 : ℝ) ^ j := by
  have hpos : (0 : ℝ) < (2 : ℝ) ^ j := by positivity
  have hcast : (2 : ℝ) ^ j ≤ (blockEndpoint j : ℝ) := by
    exact_mod_cast blockEndpoint_ge_two_pow j
  exact one_div_le_one_div_of_le hpos hcast

/-- Relative loss of one ordered prime slot: the block-mass error plus the
loss from excluding the earlier primes selected in the same block. -/
noncomputable def blockSlotLoss {K : ℕ} (C : ℝ) (M : ℕ)
    (b : Fin K → ℕ) (s : BlockSlot K (extendComposition b)) : ℝ :=
  (C + s.2.val) /
    (Real.log 2 * (2 : ℝ) ^ (M + s.1.val))

theorem blockSlotLoss_nonneg {K : ℕ} {C : ℝ} (hC : 0 ≤ C)
    (M : ℕ) (b : Fin K → ℕ)
    (s : BlockSlot K (extendComposition b)) :
    0 ≤ blockSlotLoss C M b s := by
  dsimp [blockSlotLoss]
  positivity

theorem blockSlotLoss_sum_le {M K : ℕ} {C : ℝ} (hC : 0 ≤ C)
    {b : Fin K → ℕ} (hcap : ∀ i : Fin K,
      extendComposition b i ≤ (M * M) * (i.val + 1)) :
    (∑ s : BlockSlot K (extendComposition b), blockSlotLoss C M b s) ≤
      (4 * (M * M) * C + 12 * (M * M) ^ 2) /
        (Real.log 2 * (2 : ℝ) ^ M) := by
  have hCsum := slot_geometric_error_sum_le
    (M := M) (k := K) (K := M * M) (b := extendComposition b) hC hcap
  have hTsum := slot_local_geometric_sum_le
    (M := M) (k := K) (K := M * M) (b := extendComposition b) hcap
  have hlog : 0 < Real.log 2 := Real.log_pos one_lt_two
  push_cast at hCsum hTsum
  calc
    (∑ s : BlockSlot K (extendComposition b), blockSlotLoss C M b s) =
        (1 / Real.log 2) *
          ((∑ s : BlockSlot K (extendComposition b),
              C / (2 : ℝ) ^ (M + s.1.val)) +
            ∑ s : BlockSlot K (extendComposition b),
              (s.2.val : ℝ) / (2 : ℝ) ^ (M + s.1.val)) := by
      rw [mul_add, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro s hs
      dsimp [blockSlotLoss]
      field_simp [hlog.ne']
    _ ≤ (1 / Real.log 2) *
          (4 * (M * M) * C / (2 : ℝ) ^ M +
            12 * (M * M) ^ 2 / (2 : ℝ) ^ M) := by
      apply mul_le_mul_of_nonneg_left (add_le_add hCsum hTsum)
      positivity
    _ = (4 * (M * M) * C + 12 * (M * M) ^ 2) /
          (Real.log 2 * (2 : ℝ) ^ M) := by
      field_simp [hlog.ne']

theorem blockSlot_factor_lower
    {M K : ℕ} {C : ℝ} (hC : 0 ≤ C)
    {b : Fin K → ℕ}
    (hmass : ∀ i : Fin K,
      |primeBlockMass (M + i) - Real.log 2| ≤
        C / (2 : ℝ) ^ (M + i.val))
    (s : BlockSlot K (extendComposition b)) :
    Real.log 2 * (1 - blockSlotLoss C M b s) ≤
      primeBlockMass (M + s.1) -
        (s.2.val : ℝ) / (blockEndpoint (M + s.1) : ℝ) := by
  have hlog : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hm := neg_le_of_abs_le (hmass s.1)
  have hinv := inv_blockEndpoint_le_inv_two_pow (M + s.1.val)
  have ht : (0 : ℝ) ≤ s.2.val := by positivity
  have hatom :
      (s.2.val : ℝ) / (blockEndpoint (M + s.1) : ℝ) ≤
        (s.2.val : ℝ) / (2 : ℝ) ^ (M + s.1.val) := by
    simpa only [div_eq_mul_inv, one_mul] using
      mul_le_mul_of_nonneg_left hinv ht
  dsimp [blockSlotLoss]
  have hpow : (0 : ℝ) < (2 : ℝ) ^ (M + s.1.val) := by positivity
  calc
    Real.log 2 *
          (1 - (C + (s.2.val : ℕ)) /
            (Real.log 2 * (2 : ℝ) ^ (M + s.1.val))) =
        Real.log 2 -
          C / (2 : ℝ) ^ (M + s.1.val) -
          (s.2.val : ℝ) / (2 : ℝ) ^ (M + s.1.val) := by
      push_cast
      field_simp [hlog.ne', hpow.ne']
      ring
    _ ≤ primeBlockMass (M + s.1) -
          (s.2.val : ℝ) / (2 : ℝ) ^ (M + s.1.val) := by
      linarith
    _ ≤ primeBlockMass (M + s.1) -
          (s.2.val : ℝ) / (blockEndpoint (M + s.1) : ℝ) := by
      linarith

theorem compositionBlockFamily_divisorMass_eq
    {M K : ℕ} {b : Fin K → ℕ} (hb : b ∈ cappedCompositions M K) :
    (∑ a ∈ compositionBlockFamily M b,
        (a.divisors.card : ℝ) / a) =
      (2 : ℝ) ^ K *
        ∏ i : Fin K, blockElementaryMass (M + i) (b i) := by
  simpa only [compositionBlockFamily, extendComposition_fin,
    sum_range_extendComposition b,
    mem_compositions.mp (mem_cappedCompositions.mp hb).1] using
      blockFamily_divisor_reciprocal_sum M K (extendComposition b)

/-- A half of the ideal divisor mass survives all Mertens and
without-replacement errors. -/
theorem compositionBlockFamily_divisorMass_lower
    {M K : ℕ} {C : ℝ} (hM : 1 ≤ M) (hC : 0 ≤ C)
    {b : Fin K → ℕ} (hb : b ∈ cappedCompositions M K)
    (hmass : ∀ i : Fin K,
      |primeBlockMass (M + i) - Real.log 2| ≤
        C / (2 : ℝ) ^ (M + i.val))
    (hselect : ∀ i : Fin K,
      (b i : ℝ) * (1 / (blockEndpoint (M + i) : ℝ)) ≤
        primeBlockMass (M + i))
    (hbudget :
      (4 * (M * M) * C + 12 * (M * M) ^ 2) /
          (Real.log 2 * (2 : ℝ) ^ M) ≤ 1 / 2) :
    ((2 * Real.log 2 : ℝ) ^ K / 2) /
        compositionFactorial b ≤
      ∑ a ∈ compositionBlockFamily M b,
        (a.divisors.card : ℝ) / a := by
  let z : BlockSlot K (extendComposition b) → ℝ :=
    blockSlotLoss C M b
  have hcap : ∀ i : Fin K,
      extendComposition b i ≤ (M * M) * (i.val + 1) :=
    cappedComposition_linear_cap hM hb
  have hz0 : ∀ s, 0 ≤ z s :=
    fun s ↦ blockSlotLoss_nonneg hC M b s
  have hzsum : (∑ s, z s) ≤ 1 / 2 :=
    (blockSlotLoss_sum_le hC hcap).trans hbudget
  have hz1 : ∀ s, z s ≤ 1 := by
    intro s
    have hsle : z s ≤ ∑ t, z t := by
      exact Finset.single_le_sum (fun t _ht ↦ hz0 t) (Finset.mem_univ s)
    linarith
  have hfactor : ∀ s,
      Real.log 2 * (1 - z s) ≤
        primeBlockMass (M + s.1) -
          (s.2.val : ℝ) / (blockEndpoint (M + s.1) : ℝ) :=
    blockSlot_factor_lower hC hmass
  have hprod := prod_lower_of_relative_error
    (ι := BlockSlot K (extendComposition b))
    (Real.log 2) (Real.log_pos one_lt_two).le
    (fun s ↦ primeBlockMass (M + s.1) -
      (s.2.val : ℝ) / (blockEndpoint (M + s.1) : ℝ))
    z hz0 hz1 hfactor
  rw [card_blockSlot_extendComposition_of_mem hb] at hprod
  have hhalf : (1 / 2 : ℝ) ≤ 1 - ∑ s, z s := by linarith
  have hlogpow : 0 ≤ Real.log 2 ^ K := by positivity
  have hraw :
      Real.log 2 ^ K / 2 ≤
        ∏ s : BlockSlot K (extendComposition b),
          (primeBlockMass (M + s.1) -
            (s.2.val : ℝ) / (blockEndpoint (M + s.1) : ℝ)) := by
    calc
      Real.log 2 ^ K / 2 = Real.log 2 ^ K * (1 / 2 : ℝ) := by ring
      _ ≤ Real.log 2 ^ K * (1 - ∑ s, z s) :=
        mul_le_mul_of_nonneg_left hhalf hlogpow
      _ ≤ _ := hprod
  have hrecip := blockFamily_reciprocal_sum_falling_lower
    (M := M) (k := K) (b := extendComposition b)
    (by simpa only [extendComposition_fin] using hselect)
  simp only [extendComposition_fin] at hrecip
  have hnumerator :
      (∏ i : Fin K,
          ∏ t ∈ Finset.range (b i),
            (primeBlockMass (M + i) -
              (t : ℝ) / (blockEndpoint (M + i) : ℝ))) =
        ∏ s : BlockSlot K (extendComposition b),
          (primeBlockMass (M + s.1) -
            (s.2.val : ℝ) / (blockEndpoint (M + s.1) : ℝ)) := by
    have hslots := prod_blockSlot_local
      (k := K) (b := extendComposition b)
      (fun (i : Fin K) (t : Fin (extendComposition b i)) ↦
        primeBlockMass (M + i) -
          (t.val : ℝ) / (blockEndpoint (M + i) : ℝ))
    calc
      (∏ i : Fin K,
          ∏ t ∈ Finset.range (b i),
            (primeBlockMass (M + i) -
              (t : ℝ) / (blockEndpoint (M + i) : ℝ))) =
          ∏ i : Fin K, ∏ t : Fin (extendComposition b i),
            (primeBlockMass (M + i) -
              (t.val : ℝ) / (blockEndpoint (M + i) : ℝ)) := by
        apply Finset.prod_congr rfl
        intro i hi
        simpa only [extendComposition_fin] using
          (Fin.prod_univ_eq_prod_range
            (fun t : ℕ ↦ primeBlockMass (M + i) -
              (t : ℝ) / (blockEndpoint (M + i) : ℝ))
            (extendComposition b i)).symm
      _ = _ := hslots.symm
  have hnested :
      (∏ i : Fin K,
          (∏ t ∈ Finset.range (b i),
            (primeBlockMass (M + i) -
              (t : ℝ) / (blockEndpoint (M + i) : ℝ))) /
            ((b i).factorial : ℝ)) =
        (∏ s : BlockSlot K (extendComposition b),
          (primeBlockMass (M + s.1) -
            (s.2.val : ℝ) / (blockEndpoint (M + s.1) : ℝ))) /
          compositionFactorial b := by
    rw [Finset.prod_div_distrib]
    rw [hnumerator]
    rfl
  rw [hnested] at hrecip
  rw [compositionBlockFamily_divisorMass_eq hb]
  have hfac : 0 < compositionFactorial b := by
    dsimp [compositionFactorial]
    positivity
  have hrawDiv := div_le_div_of_nonneg_right hraw hfac.le
  calc
    ((2 * Real.log 2 : ℝ) ^ K / 2) / compositionFactorial b =
        (2 : ℝ) ^ K *
          ((Real.log 2 ^ K / 2) / compositionFactorial b) := by
      rw [mul_pow]
      ring
    _ ≤ (2 : ℝ) ^ K *
          ((∏ s : BlockSlot K (extendComposition b),
            (primeBlockMass (M + s.1) -
              (s.2.val : ℝ) / (blockEndpoint (M + s.1) : ℝ))) /
            compositionFactorial b) :=
      mul_le_mul_of_nonneg_left hrawDiv (by positivity)
    _ ≤ (2 : ℝ) ^ K *
          (∑ a ∈ blockFamily M K (extendComposition b), 1 / (a : ℝ)) :=
      mul_le_mul_of_nonneg_left hrecip (by positivity)
    _ = (2 : ℝ) ^ K *
          ∏ i : Fin K, blockElementaryMass (M + i) (b i) := by
      rw [blockFamily_reciprocal_sum_factorization]
      simp only [extendComposition_fin]

end Erdos446
