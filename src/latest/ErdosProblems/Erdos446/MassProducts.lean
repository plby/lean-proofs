/-
Copyright (c) 2026 The Formal Conjectures Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Formal Conjectures Authors
-/

import ErdosProblems.Erdos446.BlockCloseWeight
import Mathlib.Analysis.Complex.Exponential

/-!
# Erdős Problem 446: controlling products of reciprocal block masses

The Mertens errors of the doubly exponential prime blocks are geometric.
This file records the finite product inequalities used to combine all those
errors into one absolute factor, together with the sigma-slot identities that
translate between block products and ordered slots.
-/

namespace Erdos446

open Finset Real
open scoped BigOperators

theorem sum_blockSlot_fiber {k : ℕ} {b : ℕ → ℕ}
    (f : Fin k → ℝ) :
    (∑ s : BlockSlot k b, f s.1) =
      ∑ i : Fin k, (b i : ℝ) * f i := by
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro i hi
  simp

theorem prod_blockSlot_fiber {k : ℕ} {b : ℕ → ℕ}
    (f : Fin k → ℝ) :
    (∏ s : BlockSlot k b, f s.1) =
      ∏ i : Fin k, f i ^ b i := by
  rw [Fintype.prod_sigma]
  apply Finset.prod_congr rfl
  intro i hi
  simp

theorem prod_blockSlot_local {k : ℕ} {b : ℕ → ℕ}
    (f : (i : Fin k) → Fin (b i) → ℝ) :
    (∏ s : BlockSlot k b, f s.1 s.2) =
      ∏ i : Fin k, ∏ t : Fin (b i), f i t := by
  rw [Fintype.prod_sigma]

theorem sum_blockSlot_local {k : ℕ} {b : ℕ → ℕ}
    (f : (i : Fin k) → Fin (b i) → ℝ) :
    (∑ s : BlockSlot k b, f s.1 s.2) =
      ∑ i : Fin k, ∑ t : Fin (b i), f i t := by
  rw [Fintype.sum_sigma]

/-- A finite version of `1 - ∑ zᵢ ≤ ∏ (1-zᵢ)` for `zᵢ ∈ [0,1]`. -/
theorem one_sub_sum_le_prod_one_sub {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (z : ι → ℝ)
    (hz0 : ∀ i ∈ S, 0 ≤ z i) (hz1 : ∀ i ∈ S, z i ≤ 1) :
    1 - ∑ i ∈ S, z i ≤ ∏ i ∈ S, (1 - z i) := by
  induction S using Finset.induction_on with
  | empty => simp
  | @insert a S ha ih =>
      rw [Finset.sum_insert ha, Finset.prod_insert ha]
      have hza0 := hz0 a (Finset.mem_insert_self a S)
      have hza1 := hz1 a (Finset.mem_insert_self a S)
      have hS0 : 0 ≤ ∑ i ∈ S, z i :=
        Finset.sum_nonneg fun i hi ↦ hz0 i (Finset.mem_insert_of_mem hi)
      have hih := ih
        (fun i hi ↦ hz0 i (Finset.mem_insert_of_mem hi))
        (fun i hi ↦ hz1 i (Finset.mem_insert_of_mem hi))
      calc
        1 - (z a + ∑ i ∈ S, z i) ≤
            (1 - ∑ i ∈ S, z i) * (1 - z a) := by nlinarith
        _ ≤ (∏ i ∈ S, (1 - z i)) * (1 - z a) :=
          mul_le_mul_of_nonneg_right hih (sub_nonneg.mpr hza1)
        _ = (1 - z a) * ∏ i ∈ S, (1 - z i) := by ring

/-- Upper multiplicative perturbations are controlled by the exponential of
the sum of their relative errors. -/
theorem prod_one_add_le_exp_sum_univ {ι : Type*} [Fintype ι]
    (z : ι → ℝ) (hz : ∀ i, 0 ≤ z i) :
    (∏ i : ι, (1 + z i)) ≤ Real.exp (∑ i : ι, z i) := by
  exact Real.prod_one_add_le_exp_sum Finset.univ (fun i ↦ hz i)

theorem prod_upper_of_relative_error {ι : Type*} [Fintype ι]
    (L : ℝ) (hL : 0 ≤ L) (x z : ι → ℝ)
    (hx0 : ∀ i, 0 ≤ x i) (hz0 : ∀ i, 0 ≤ z i)
    (hupper : ∀ i, x i ≤ L * (1 + z i)) :
    (∏ i : ι, x i) ≤
      L ^ Fintype.card ι * Real.exp (∑ i : ι, z i) := by
  calc
    (∏ i : ι, x i) ≤ ∏ i : ι, L * (1 + z i) := by
      apply Finset.prod_le_prod
      · intro i hi
        exact hx0 i
      · intro i hi
        exact hupper i
    _ = L ^ Fintype.card ι * ∏ i : ι, (1 + z i) := by
      rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ]
    _ ≤ L ^ Fintype.card ι * Real.exp (∑ i : ι, z i) := by
      apply mul_le_mul_of_nonneg_left (prod_one_add_le_exp_sum_univ z hz0)
      exact pow_nonneg hL _

theorem prod_lower_of_relative_error {ι : Type*} [Fintype ι]
    (L : ℝ) (hL : 0 ≤ L) (x z : ι → ℝ)
    (hz0 : ∀ i, 0 ≤ z i) (hz1 : ∀ i, z i ≤ 1)
    (hlower : ∀ i, L * (1 - z i) ≤ x i) :
    L ^ Fintype.card ι * (1 - ∑ i : ι, z i) ≤
      ∏ i : ι, x i := by
  classical
  have hprodLower :
      (∏ i : ι, L * (1 - z i)) ≤ ∏ i : ι, x i := by
    apply Finset.prod_le_prod
    · intro i hi
      exact mul_nonneg hL (sub_nonneg.mpr (hz1 i))
    · intro i hi
      exact hlower i
  calc
    L ^ Fintype.card ι * (1 - ∑ i : ι, z i) ≤
        L ^ Fintype.card ι * ∏ i : ι, (1 - z i) := by
      apply mul_le_mul_of_nonneg_left
      · exact one_sub_sum_le_prod_one_sub Finset.univ z
          (fun i hi ↦ hz0 i) (fun i hi ↦ hz1 i)
      · exact pow_nonneg hL _
    _ = ∏ i : ι, L * (1 - z i) := by
      rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ]
    _ ≤ _ := hprodLower

/-- Exact finite identity behind `∑ (i+1)/2^i ≤ 4`. -/
theorem weighted_geometric_one_identity (k : ℕ) :
    (∑ i ∈ Finset.range k, ((i + 1 : ℕ) : ℝ) / (2 : ℝ) ^ i) +
        2 * ((k + 2 : ℕ) : ℝ) / (2 : ℝ) ^ k = 4 := by
  induction k with
  | zero => norm_num
  | succ k ih =>
      rw [Finset.sum_range_succ, pow_succ]
      have hpow : (2 : ℝ) ^ k ≠ 0 := by positivity
      calc
        (∑ i ∈ Finset.range k, ((i + 1 : ℕ) : ℝ) / (2 : ℝ) ^ i) +
              (((k + 1 : ℕ) : ℝ) / (2 : ℝ) ^ k) +
              2 * (((k + 1 + 2 : ℕ) : ℝ)) / ((2 : ℝ) ^ k * 2) =
            (∑ i ∈ Finset.range k,
              ((i + 1 : ℕ) : ℝ) / (2 : ℝ) ^ i) +
              2 * (((k + 2 : ℕ) : ℝ)) / (2 : ℝ) ^ k := by
          field_simp [hpow]
          push_cast
          ring
        _ = 4 := ih

theorem weighted_geometric_one_le (k : ℕ) :
    (∑ i ∈ Finset.range k, ((i + 1 : ℕ) : ℝ) / (2 : ℝ) ^ i) ≤ 4 := by
  have htail : 0 ≤ 2 * ((k + 2 : ℕ) : ℝ) / (2 : ℝ) ^ k := by positivity
  linarith [weighted_geometric_one_identity k]

/-- Exact finite identity behind `∑ (i+1)^2/2^i ≤ 12`. -/
theorem weighted_geometric_square_identity (k : ℕ) :
    (∑ i ∈ Finset.range k, (((i + 1 : ℕ) : ℝ) ^ 2) / (2 : ℝ) ^ i) +
        2 * (((k : ℝ) ^ 2 + 4 * k + 6)) / (2 : ℝ) ^ k = 12 := by
  induction k with
  | zero => norm_num
  | succ k ih =>
      rw [Finset.sum_range_succ, pow_succ]
      have hpow : (2 : ℝ) ^ k ≠ 0 := by positivity
      calc
        (∑ i ∈ Finset.range k,
              (((i + 1 : ℕ) : ℝ) ^ 2) / (2 : ℝ) ^ i) +
              (((k + 1 : ℕ) : ℝ) ^ 2 / (2 : ℝ) ^ k) +
              2 * ((((k + 1 : ℕ) : ℝ) ^ 2 +
                4 * ((k + 1 : ℕ) : ℝ) + 6)) /
                ((2 : ℝ) ^ k * 2) =
            (∑ i ∈ Finset.range k,
              (((i + 1 : ℕ) : ℝ) ^ 2) / (2 : ℝ) ^ i) +
              2 * (((k : ℝ) ^ 2 + 4 * k + 6)) / (2 : ℝ) ^ k := by
          field_simp [hpow]
          push_cast
          ring
        _ = 12 := ih

theorem weighted_geometric_square_le (k : ℕ) :
    (∑ i ∈ Finset.range k, (((i + 1 : ℕ) : ℝ) ^ 2) / (2 : ℝ) ^ i) ≤ 12 := by
  have htail :
      0 ≤ 2 * (((k : ℝ) ^ 2 + 4 * k + 6)) / (2 : ℝ) ^ k := by positivity
  linarith [weighted_geometric_square_identity k]

theorem pow_add_inv_split (M i : ℕ) :
    (1 / (2 : ℝ) ^ (M + i)) =
      (1 / (2 : ℝ) ^ M) * (1 / (2 : ℝ) ^ i) := by
  rw [pow_add]
  field_simp

theorem slot_geometric_error_sum_le
    {M k K : ℕ} {b : ℕ → ℕ} {C : ℝ} (hC : 0 ≤ C)
    (hcap : ∀ i : Fin k, b i ≤ K * (i.val + 1)) :
    (∑ s : BlockSlot k b, C / (2 : ℝ) ^ (M + s.1.val)) ≤
      4 * K * C / (2 : ℝ) ^ M := by
  change (∑ s : BlockSlot k b,
    (fun i : Fin k ↦ C / (2 : ℝ) ^ (M + i.val)) s.1) ≤ _
  rw [Fintype.sum_sigma]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul]
  calc
    (∑ i : Fin k, (b i : ℝ) * (C / (2 : ℝ) ^ (M + i.val))) ≤
        ∑ i : Fin k,
          ((K * (i.val + 1) : ℕ) : ℝ) *
            (C / (2 : ℝ) ^ (M + i.val)) := by
      apply Finset.sum_le_sum
      intro i hi
      apply mul_le_mul_of_nonneg_right
      · exact_mod_cast hcap i
      · positivity
    _ = K * C / (2 : ℝ) ^ M *
        ∑ i ∈ Finset.range k,
          ((i + 1 : ℕ) : ℝ) / (2 : ℝ) ^ i := by
      rw [← Fin.sum_univ_eq_sum_range]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      rw [pow_add]
      push_cast
      field_simp
    _ ≤ K * C / (2 : ℝ) ^ M * 4 := by
      apply mul_le_mul_of_nonneg_left (weighted_geometric_one_le k)
      positivity
    _ = 4 * K * C / (2 : ℝ) ^ M := by ring

theorem slot_local_geometric_sum_le
    {M k K : ℕ} {b : ℕ → ℕ}
    (hcap : ∀ i : Fin k, b i ≤ K * (i.val + 1)) :
    (∑ s : BlockSlot k b,
        (s.2.val : ℝ) / (2 : ℝ) ^ (M + s.1.val)) ≤
      12 * K ^ 2 / (2 : ℝ) ^ M := by
  change (∑ s : BlockSlot k b,
    (fun (i : Fin k) (t : Fin (b i)) ↦
      (t.val : ℝ) / (2 : ℝ) ^ (M + i.val)) s.1 s.2) ≤ _
  rw [Fintype.sum_sigma]
  calc
    (∑ i : Fin k, ∑ t : Fin (b i),
        (t.val : ℝ) / (2 : ℝ) ^ (M + i.val)) ≤
        ∑ i : Fin k,
          (((K * (i.val + 1) : ℕ) : ℝ) ^ 2) /
            (2 : ℝ) ^ (M + i.val) := by
      apply Finset.sum_le_sum
      intro i hi
      calc
        (∑ t : Fin (b i),
            (t.val : ℝ) / (2 : ℝ) ^ (M + i.val)) ≤
            ∑ _t : Fin (b i),
              ((K * (i.val + 1) : ℕ) : ℝ) /
                (2 : ℝ) ^ (M + i.val) := by
          apply Finset.sum_le_sum
          intro t ht
          apply div_le_div_of_nonneg_right
          · exact_mod_cast (t.isLt.le.trans (hcap i))
          · positivity
        _ = (b i : ℝ) *
            (((K * (i.val + 1) : ℕ) : ℝ) /
              (2 : ℝ) ^ (M + i.val)) := by simp
        _ ≤ ((K * (i.val + 1) : ℕ) : ℝ) *
            (((K * (i.val + 1) : ℕ) : ℝ) /
              (2 : ℝ) ^ (M + i.val)) := by
          apply mul_le_mul_of_nonneg_right
          · exact_mod_cast hcap i
          · positivity
        _ = (((K * (i.val + 1) : ℕ) : ℝ) ^ 2) /
              (2 : ℝ) ^ (M + i.val) := by ring
    _ = K ^ 2 / (2 : ℝ) ^ M *
        ∑ i ∈ Finset.range k,
          (((i + 1 : ℕ) : ℝ) ^ 2) / (2 : ℝ) ^ i := by
      rw [← Fin.sum_univ_eq_sum_range]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      rw [pow_add]
      push_cast
      field_simp
    _ ≤ K ^ 2 / (2 : ℝ) ^ M * 12 := by
      apply mul_le_mul_of_nonneg_left (weighted_geometric_square_le k)
      positivity
    _ = 12 * K ^ 2 / (2 : ℝ) ^ M := by ring

end Erdos446
