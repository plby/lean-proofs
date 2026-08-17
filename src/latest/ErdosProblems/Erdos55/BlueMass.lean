/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/
import ErdosProblems.Erdos55.HuePrefix
import ErdosProblems.Erdos55.Weighted

/-!
# Exponential mass across the CFP blue windows

The source bounds the contribution of one integer to all blue windows by a
double-exponential series.  The coarser inequality `exp (-x) ≤ 1/x` gives the
clean absolute bound `32`, which is more than sufficient after choosing a
smaller final absolute constant.
-/

namespace Erdos55

open scoped BigOperators

private theorem exp_neg_le_inv {x : ℝ} (hx : 0 < x) :
    Real.exp (-x) ≤ x⁻¹ := by
  rw [inv_eq_one_div, le_div_iff₀ hx]
  calc
    Real.exp (-x) * x = x * Real.exp (-x) := by ring
    _ ≤ Real.exp (-1) := Real.mul_exp_neg_le_exp_neg_one x
    _ ≤ 1 := Real.exp_le_one_iff.mpr (by norm_num)

theorem blueWeight_le (a j : ℕ) (ha : 0 < a) :
    Real.exp (-(a : ℝ) / (2 : ℝ) ^ (j + 4)) ≤
      (2 : ℝ) ^ (j + 4) / a := by
  have hQ : (0 : ℝ) < (2 : ℝ) ^ (j + 4) := by positivity
  have haR : (0 : ℝ) < a := by exact_mod_cast ha
  have hx : 0 < (a : ℝ) / (2 : ℝ) ^ (j + 4) := div_pos haR hQ
  calc
    Real.exp (-(a : ℝ) / (2 : ℝ) ^ (j + 4)) =
        Real.exp (-((a : ℝ) / (2 : ℝ) ^ (j + 4))) := by ring_nf
    _ ≤ (((a : ℝ) / (2 : ℝ) ^ (j + 4))⁻¹) := exp_neg_le_inv hx
    _ = (2 : ℝ) ^ (j + 4) / a := by field_simp

/-- A fixed positive integer contributes total exponential weight at most
`32` over every finite collection of indices satisfying `2^j < a`. -/
theorem sum_blueWeight_le (a i : ℕ) (ha : 0 < a) :
    ∑ j ∈ (Finset.Icc 1 i).filter (fun j ↦ 2 ^ j < a),
        Real.exp (-(a : ℝ) / (2 : ℝ) ^ (j + 4)) ≤ 32 := by
  classical
  let J := (Finset.Icc 1 i).filter (fun j ↦ 2 ^ j < a)
  let L := Nat.log 2 a
  have hJrange : J ⊆ Finset.range (L + 1) := by
    intro j hj
    have hjpow : 2 ^ j < a := (Finset.mem_filter.mp hj).2
    have hjlog : j ≤ L := Nat.le_log_of_pow_le (by omega) hjpow.le
    exact Finset.mem_range.mpr (by omega)
  have hpowSumNat : (∑ j ∈ Finset.range (L + 1), 2 ^ j) ≤ 2 ^ (L + 1) := by
    have hgeom : ∀ n : ℕ, (∑ j ∈ Finset.range n, 2 ^ j) = 2 ^ n - 1 := by
      intro n
      induction n with
      | zero => simp
      | succ n ih =>
          rw [Finset.sum_range_succ, ih, pow_succ]
          have hone : 1 ≤ 2 ^ n := Nat.one_le_two_pow
          omega
    calc
      (∑ j ∈ Finset.range (L + 1), 2 ^ j) = 2 ^ (L + 1) - 1 := hgeom _
      _ ≤ 2 ^ (L + 1) := Nat.sub_le _ _
  have hpowlog : 2 ^ L ≤ a := Nat.pow_log_le_self 2 ha.ne'
  have hpowSum :
      (∑ j ∈ J, (2 : ℝ) ^ j) ≤ 2 * (a : ℝ) := by
    calc
      (∑ j ∈ J, (2 : ℝ) ^ j) ≤
          ∑ j ∈ Finset.range (L + 1), (2 : ℝ) ^ j :=
        Finset.sum_le_sum_of_subset_of_nonneg hJrange (fun _ _ _ ↦ by positivity)
      _ = (∑ j ∈ Finset.range (L + 1), 2 ^ j : ℕ) := by
        norm_cast
      _ ≤ (2 ^ (L + 1) : ℕ) := by exact_mod_cast hpowSumNat
      _ = 2 * (2 ^ L : ℕ) := by rw [pow_succ']; norm_num
      _ ≤ 2 * (a : ℝ) := by
        exact_mod_cast (Nat.mul_le_mul_left 2 hpowlog)
  have haR : (0 : ℝ) < a := by exact_mod_cast ha
  calc
    ∑ j ∈ J, Real.exp (-(a : ℝ) / (2 : ℝ) ^ (j + 4)) ≤
        ∑ j ∈ J, (2 ^ (j + 4) : ℝ) / a := by
      exact Finset.sum_le_sum fun j _ ↦ blueWeight_le a j ha
    _ = (16 / (a : ℝ)) * ∑ j ∈ J, (2 : ℝ) ^ j := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      rw [show j + 4 = 4 + j by omega, pow_add]
      norm_num
      ring
    _ ≤ (16 / (a : ℝ)) * (2 * a) := by
      exact mul_le_mul_of_nonneg_left hpowSum (by positivity)
    _ = 32 := by field_simp <;> norm_num

noncomputable def blueWindow (A : Set ℕ) (j : ℕ) : Finset ℕ :=
  rankPrefix A (j * 2 ^ j) \ rankPrefix A (2 ^ j)

noncomputable def blueMass (A : Set ℕ) (j : ℕ) : ℝ :=
  ∑ a ∈ blueWindow A j, Real.exp (-(a : ℝ) / (2 : ℝ) ^ (j + 4))

theorem rankPrefix_mono {A : Set ℕ} (hA : A.Infinite) {M N : ℕ}
    (hMN : M ≤ N) : rankPrefix A M ⊆ rankPrefix A N := by
  intro a ha
  rw [mem_rankPrefix_iff hA] at ha ⊢
  exact ⟨ha.1, ha.2.trans hMN⟩

private theorem scale_mono {j i : ℕ} (hji : j ≤ i) :
    j * 2 ^ j ≤ i * 2 ^ i := by
  exact Nat.mul_le_mul hji (Nat.pow_le_pow_right (by omega) hji)

/-- Summing the blue-window masses through scale `i` costs at most `32` for
each element of the largest prefix. -/
theorem sum_blueMass_le {A : Set ℕ} (hA : A.Infinite)
    (hApos : IsPositiveNatSet A) (i : ℕ) :
    ∑ j ∈ Finset.Icc 1 i, blueMass A j ≤
      32 * (rankPrefix A (i * 2 ^ i)).card := by
  classical
  let P := rankPrefix A (i * 2 ^ i)
  have hwindow (j : ℕ) (hj : j ∈ Finset.Icc 1 i) :
      blueWindow A j ⊆ P.filter (fun a ↦ 2 ^ j < a) := by
    intro a ha
    have ha' := Finset.mem_sdiff.mp ha
    have hji : j ≤ i := (Finset.mem_Icc.mp hj).2
    have haP : a ∈ P := rankPrefix_mono hA (scale_mono hji) ha'.1
    have halower : 2 ^ j < a := by
      have haAupper := (mem_rankPrefix_iff hA).mp ha'.1
      by_contra hnot
      exact ha'.2 ((mem_rankPrefix_iff hA).mpr ⟨haAupper.1, Nat.le_of_not_gt hnot⟩)
    exact Finset.mem_filter.mpr ⟨haP, halower⟩
  have hjbound (j : ℕ) (hj : j ∈ Finset.Icc 1 i) :
      blueMass A j ≤
        ∑ a ∈ P.filter (fun a ↦ 2 ^ j < a),
          Real.exp (-(a : ℝ) / (2 : ℝ) ^ (j + 4)) := by
    apply Finset.sum_le_sum_of_subset_of_nonneg (hwindow j hj)
    intro a _ _
    positivity
  calc
    ∑ j ∈ Finset.Icc 1 i, blueMass A j ≤
        ∑ j ∈ Finset.Icc 1 i,
          ∑ a ∈ P.filter (fun a ↦ 2 ^ j < a),
            Real.exp (-(a : ℝ) / (2 : ℝ) ^ (j + 4)) :=
      Finset.sum_le_sum hjbound
    _ = ∑ a ∈ P,
          ∑ j ∈ (Finset.Icc 1 i).filter (fun j ↦ 2 ^ j < a),
            Real.exp (-(a : ℝ) / (2 : ℝ) ^ (j + 4)) := by
      simp_rw [Finset.sum_filter]
      rw [Finset.sum_comm]
    _ ≤ ∑ _a ∈ P, (32 : ℝ) := by
      apply Finset.sum_le_sum
      intro a haP
      have haA : a ∈ A := (mem_rankPrefix_iff hA).mp haP |>.1
      exact sum_blueWeight_le a i (hApos haA)
    _ = 32 * P.card := by simp [mul_comm]

end Erdos55
