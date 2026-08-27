/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.SmallHallCounting
import ErdosProblems.Erdos207.SharpRobustHallSampling
import Mathlib.Algebra.Order.Field.GeomSum
import Mathlib.Data.NNReal.Basic

/-! # A size-sensitive geometric bound for the exact sharp Hall sum -/

namespace Erdos207

open Finset
open scoped Classical NNReal

noncomputable section

theorem nnreal_sum_Icc_pow_le_two_mul
    (x : ℝ≥0) (hx : x ≤ 1 / 2) (n : ℕ) :
    ∑ s ∈ Icc 1 n, x ^ s ≤ 2 * x := by
  have hxR : (x : ℝ) ≤ 1 / 2 := by exact_mod_cast hx
  have hbound : ∑ s ∈ Icc 1 n, (x : ℝ) ^ s ≤ 2 * (x : ℝ) := by
    have hg := geom_sum_Ico_le_of_lt_one (m := 1) (n := n+1) x.property (by linarith : (x : ℝ) < 1)
    have hinterval : Ico 1 (n+1) = Icc 1 n := by ext i; simp only [mem_Ico, mem_Icc]; omega
    rw [hinterval, pow_one] at hg
    apply hg.trans
    calc
      (x : ℝ) / (1 - x) ≤ (x : ℝ) / (1 / 2) :=
        div_le_div_of_nonneg_left x.property (by norm_num) (by linarith)
      _ = _ := by ring
  apply NNReal.coe_le_coe.mp
  simpa only [NNReal.coe_sum, NNReal.coe_pow, NNReal.coe_mul, NNReal.coe_ofNat] using hbound

theorem sharpHall_summand_le_size_power
    {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (r : A → B → Prop) [DecidableRel r] (sigma : ℝ≥0) (c Delta : ℕ)
    (o : OrientedSmallHallObstruction A B)
    (hcandidate : c * orientedSmallHallSize o ≤ (orientedSmallHallCandidates r o).card) :
    (1 - sigma / 2) ^ (orientedSmallHallCandidates r o).card /
      (1 / 2 : ℝ≥0) ^ (Delta * orientedSmallHallSize o) ≤
        ((1 - sigma / 2) ^ c * (2 : ℝ≥0) ^ Delta) ^ orientedSmallHallSize o := by
  have hbase : 1 - sigma / 2 ≤ (1 : ℝ≥0) := tsub_le_self
  calc
    _ ≤ (1 - sigma / 2) ^ (c * orientedSmallHallSize o) /
        (1 / 2 : ℝ≥0) ^ (Delta * orientedSmallHallSize o) := by
      apply div_le_div_of_nonneg_right _ zero_le
      exact NNReal.pow_antitone_exp _ _ hcandidate hbase
    _ = _ := by
      simp only [inv_pow, div_eq_mul_inv, inv_inv, pow_mul, mul_pow, one_mul]

theorem sharpHall_sum_le
    {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (r : A → B → Prop) [DecidableRel r] (hcard : Fintype.card A = Fintype.card B)
    (sigma : ℝ≥0) (c Delta : ℕ)
    (hcandidate : ∀ o : OrientedSmallHallObstruction A B,
      c * orientedSmallHallSize o ≤ (orientedSmallHallCandidates r o).card)
    (hsmall : ((2 * (Fintype.card A + 1) * (Fintype.card B + 1) : ℕ) : ℝ≥0) *
      ((1 - sigma / 2) ^ c * (2 : ℝ≥0) ^ Delta) ≤ 1 / 2) :
    (∑ o : OrientedSmallHallObstruction A B,
      (1 - sigma / 2) ^ (orientedSmallHallCandidates r o).card /
        (1 / 2 : ℝ≥0) ^ (Delta * orientedSmallHallSize o)) ≤
      4 * ((2 * (Fintype.card A + 1) * (Fintype.card B + 1) : ℕ) : ℝ≥0) *
        ((1 - sigma / 2) ^ c * (2 : ℝ≥0) ^ Delta) := by
  calc
    _ ≤ ∑ o : OrientedSmallHallObstruction A B,
        ((1 - sigma / 2) ^ c * (2 : ℝ≥0) ^ Delta) ^ orientedSmallHallSize o :=
      sum_le_sum (fun o _ ↦ sharpHall_summand_le_size_power r sigma c Delta o (hcandidate o))
    _ ≤ 2 * ∑ s ∈ Icc 1 (Fintype.card A),
        (((2 * (Fintype.card A + 1) * (Fintype.card B + 1) : ℕ) : ℝ≥0) *
          ((1 - sigma / 2) ^ c * (2 : ℝ≥0) ^ Delta)) ^ s := orientedSmallHall_weighted_sum_le hcard _
    _ ≤ 2 * (2 * (((2 * (Fintype.card A + 1) * (Fintype.card B + 1) : ℕ) : ℝ≥0) *
        ((1 - sigma / 2) ^ c * (2 : ℝ≥0) ^ Delta))) :=
      mul_le_mul_of_nonneg_left (nnreal_sum_Icc_pow_le_two_mul _ hsmall _) zero_le
    _ = _ := by ring

end

end Erdos207
