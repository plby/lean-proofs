/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/
/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Formal Conjectures Authors.
-/

import ErdosProblems.Erdos1165.HLOZShellZeroCentralCount

/-!
# Numerical bound for the fixed central shell-zero replacement count

For fixed `C > 0`, this file bounds the exact comparison coefficient at
`s = floor (C r / (1+C))`.  The proof uses the elementary mode estimate for
the weighted binomial coefficients `choose r k * C^k`.
-/

open scoped BigOperators

namespace Erdos1165.HLOZShellZeroCentralNumerics

open HLOZShellZeroCentralCount

noncomputable section

def weightedChoose (C : ℝ) (r k : ℕ) : ℝ :=
  (r.choose k : ℝ) * C ^ k

lemma weightedChoose_nonneg {C : ℝ} (hC : 0 ≤ C) (r k : ℕ) :
    0 ≤ weightedChoose C r k := by
  unfold weightedChoose
  positivity

lemma weightedChoose_succ_mul (C : ℝ) (r k : ℕ) :
    weightedChoose C r (k + 1) * ((k + 1 : ℕ) : ℝ) =
      weightedChoose C r k * (C * ((r - k : ℕ) : ℝ)) := by
  unfold weightedChoose
  have hchoose :
      (r.choose (k + 1) : ℝ) * ((k + 1 : ℕ) : ℝ) =
        (r.choose k : ℝ) * ((r - k : ℕ) : ℝ) := by
    exact_mod_cast Nat.choose_succ_right_eq r k
  rw [pow_succ]
  calc
    (r.choose (k + 1) : ℝ) * (C ^ k * C) * ((k + 1 : ℕ) : ℝ) =
        ((r.choose (k + 1) : ℝ) * ((k + 1 : ℕ) : ℝ)) * C ^ k * C := by ring
    _ = ((r.choose k : ℝ) * ((r - k : ℕ) : ℝ)) * C ^ k * C := by rw [hchoose]
    _ = (r.choose k : ℝ) * C ^ k * (C * ((r - k : ℕ) : ℝ)) := by ring

lemma weightedChoose_le_succ
    {C : ℝ} (hC : 0 ≤ C) {r k : ℕ}
    (hstep : ((k + 1 : ℕ) : ℝ) ≤ C * ((r - k : ℕ) : ℝ)) :
    weightedChoose C r k ≤ weightedChoose C r (k + 1) := by
  have hk : (0 : ℝ) < ((k + 1 : ℕ) : ℝ) := by positivity
  apply le_of_mul_le_mul_right _ hk
  rw [weightedChoose_succ_mul]
  exact mul_le_mul_of_nonneg_left hstep (weightedChoose_nonneg hC r k)

lemma weightedChoose_succ_le
    {C : ℝ} (hC : 0 ≤ C) {r k : ℕ}
    (hstep : C * ((r - k : ℕ) : ℝ) ≤ ((k + 1 : ℕ) : ℝ)) :
    weightedChoose C r (k + 1) ≤ weightedChoose C r k := by
  have hk : (0 : ℝ) < ((k + 1 : ℕ) : ℝ) := by positivity
  apply le_of_mul_le_mul_right _ hk
  rw [weightedChoose_succ_mul]
  exact mul_le_mul_of_nonneg_left hstep (weightedChoose_nonneg hC r k)

def weightedChooseMode (C : ℝ) (r : ℕ) : ℕ :=
  ⌊C / (1 + C) * ((r : ℝ) + 1)⌋₊

lemma weightedChooseMode_le
    {C : ℝ} (hC : 0 ≤ C) (r : ℕ) :
    weightedChooseMode C r ≤ r := by
  unfold weightedChooseMode
  have hden : 0 < 1 + C := by linarith
  have hp : C / (1 + C) < 1 := (div_lt_one₀ hden).2 (by linarith)
  have hr : (0 : ℝ) < (r : ℝ) + 1 := by positivity
  have harg : C / (1 + C) * ((r : ℝ) + 1) < (r : ℝ) + 1 := by
    nlinarith [mul_pos (sub_pos.mpr hp) hr]
  have hnonneg : 0 ≤ C / (1 + C) * ((r : ℝ) + 1) :=
    mul_nonneg (div_nonneg hC hden.le) hr.le
  apply Nat.le_of_lt_succ
  apply (Nat.floor_lt hnonneg).2
  simpa only [Nat.cast_succ, Nat.cast_add, Nat.cast_one] using harg

lemma weightedChoose_step_up_before_mode
    {C : ℝ} (hC : 0 ≤ C) {r k : ℕ}
    (hk : k < weightedChooseMode C r) :
    weightedChoose C r k ≤ weightedChoose C r (k + 1) := by
  apply weightedChoose_le_succ hC
  have hden : 0 < 1 + C := by linarith
  have hfloor : (weightedChooseMode C r : ℝ) ≤
      C / (1 + C) * ((r : ℝ) + 1) := by
    unfold weightedChooseMode
    exact Nat.floor_le
      (mul_nonneg (div_nonneg hC hden.le) (by positivity))
  have hkn : k + 1 ≤ weightedChooseMode C r := by omega
  have hknR : (((k + 1 : ℕ) : ℝ)) ≤ weightedChooseMode C r := by
    exact_mod_cast hkn
  have hbasic := hknR.trans hfloor
  have hkr : k ≤ r :=
    (Nat.le_of_lt hk).trans (weightedChooseMode_le hC r)
  rw [div_mul_eq_mul_div, le_div_iff₀ hden] at hbasic
  rw [Nat.cast_sub hkr]
  push_cast at hbasic ⊢
  linarith

lemma weightedChoose_step_down_after_mode
    {C : ℝ} (hC : 0 ≤ C) {r k : ℕ}
    (hmode : weightedChooseMode C r ≤ k) (hkr : k < r) :
    weightedChoose C r (k + 1) ≤ weightedChoose C r k := by
  apply weightedChoose_succ_le hC
  have hden : 0 < 1 + C := by linarith
  have hfloor : C / (1 + C) * ((r : ℝ) + 1) <
      (weightedChooseMode C r : ℝ) + 1 := by
    unfold weightedChooseMode
    exact Nat.lt_floor_add_one _
  have hmodeR : (weightedChooseMode C r : ℝ) ≤ k := by exact_mod_cast hmode
  have hbasic : C / (1 + C) * ((r : ℝ) + 1) < (k : ℝ) + 1 := by
    linarith
  rw [div_mul_eq_mul_div, div_lt_iff₀ hden] at hbasic
  rw [Nat.cast_sub (Nat.le_of_lt hkr)]
  push_cast at hbasic ⊢
  linarith

lemma weightedChoose_le_mode
    {C : ℝ} (hC : 0 ≤ C) (r k : ℕ) (hk : k ≤ r) :
    weightedChoose C r k ≤ weightedChoose C r (weightedChooseMode C r) := by
  by_cases hleft : k ≤ weightedChooseMode C r
  · have hchain : ∀ n, k ≤ n → n ≤ weightedChooseMode C r →
        weightedChoose C r k ≤ weightedChoose C r n := by
      intro n hkn
      induction n, hkn using Nat.le_induction with
      | base => exact fun _ ↦ le_rfl
      | succ n hkn ih =>
          intro hnext
          exact (ih (by omega)).trans
            (weightedChoose_step_up_before_mode hC (by omega))
    exact hchain _ hleft le_rfl
  · have hmodek : weightedChooseMode C r ≤ k := by omega
    have hchain : ∀ n, weightedChooseMode C r ≤ n → n ≤ r →
        weightedChoose C r n ≤ weightedChoose C r (weightedChooseMode C r) := by
      intro n hmn
      induction n, hmn using Nat.le_induction with
      | base => exact fun _ ↦ le_rfl
      | succ n hmn ih =>
          intro hnext
          exact (weightedChoose_step_down_after_mode hC hmn (by omega)).trans
            (ih (by omega))
    exact hchain _ hmodek hk

lemma sum_weightedChoose (C : ℝ) (r : ℕ) :
    (1 + C) ^ r = ∑ k ∈ Finset.range (r + 1), weightedChoose C r k := by
  rw [show 1 + C = C + 1 by ring, add_pow]
  apply Finset.sum_congr rfl
  intro k _
  simp only [weightedChoose, one_pow, mul_one]
  ring

theorem one_add_pow_le_mode
    {C : ℝ} (hC : 0 ≤ C) (r : ℕ) :
    (1 + C) ^ r ≤
      ((r + 1 : ℕ) : ℝ) * weightedChoose C r (weightedChooseMode C r) := by
  rw [sum_weightedChoose]
  calc
    (∑ k ∈ Finset.range (r + 1), weightedChoose C r k) ≤
        ∑ _k ∈ Finset.range (r + 1),
          weightedChoose C r (weightedChooseMode C r) := by
      apply Finset.sum_le_sum
      intro k hk
      apply weightedChoose_le_mode hC r k
      exact Nat.le_of_lt_succ (Finset.mem_range.mp hk)
    _ = ((r + 1 : ℕ) : ℝ) * weightedChoose C r (weightedChooseMode C r) := by
      simp

lemma central_le_mode {C : ℝ} (hC : 0 ≤ C) (r : ℕ) :
    centralReplacementUpperCount C r ≤ weightedChooseMode C r := by
  unfold centralReplacementUpperCount weightedChooseMode
  apply Nat.floor_mono
  exact mul_le_mul_of_nonneg_left (by norm_num : (r : ℝ) ≤ r + 1)
    (div_nonneg hC (by linarith))

lemma mode_le_central_add_one {C : ℝ} (hC : 0 ≤ C) (r : ℕ) :
    weightedChooseMode C r ≤ centralReplacementUpperCount C r + 1 := by
  have hden : 0 < 1 + C := by linarith
  have hp_nonneg : 0 ≤ C / (1 + C) := div_nonneg hC hden.le
  have hp_lt : C / (1 + C) < 1 := (div_lt_one₀ hden).2 (by linarith)
  have hcenter : C / (1 + C) * (r : ℝ) <
      (centralReplacementUpperCount C r : ℝ) + 1 := by
    unfold centralReplacementUpperCount
    exact Nat.lt_floor_add_one _
  have harg : C / (1 + C) * ((r : ℝ) + 1) <
      (centralReplacementUpperCount C r : ℝ) + 2 := by
    nlinarith
  unfold weightedChooseMode
  have hnonneg : 0 ≤ C / (1 + C) * ((r : ℝ) + 1) := by positivity
  apply Nat.le_of_lt_succ
  apply (Nat.floor_lt hnonneg).2
  norm_num [Nat.cast_succ, Nat.cast_add] at ⊢
  linarith

lemma weightedChoose_mode_le_one_add_mul_central
    {C : ℝ} (hC : 0 ≤ C) (r : ℕ) :
    weightedChoose C r (weightedChooseMode C r) ≤
      (1 + C) * weightedChoose C r (centralReplacementUpperCount C r) := by
  have hle := central_le_mode hC r
  have hupper := mode_le_central_add_one hC r
  have hcases : weightedChooseMode C r = centralReplacementUpperCount C r ∨
      weightedChooseMode C r = centralReplacementUpperCount C r + 1 := by omega
  rcases hcases with h | h
  · rw [h]
    exact le_mul_of_one_le_left (weightedChoose_nonneg hC _ _) (by linarith)
  · rw [h]
    let s := centralReplacementUpperCount C r
    change weightedChoose C r (s + 1) ≤ (1 + C) * weightedChoose C r s
    have hsle : s ≤ r := centralReplacementUpperCount_le hC r
    have hden : 0 < 1 + C := by linarith
    have hcenter : C / (1 + C) * (r : ℝ) < (s : ℝ) + 1 := by
      dsimp only [s]
      unfold centralReplacementUpperCount
      exact Nat.lt_floor_add_one _
    rw [div_mul_eq_mul_div, div_lt_iff₀ hden] at hcenter
    have hstep : C * (((r - s : ℕ) : ℝ)) ≤
        (1 + C) * (((s + 1 : ℕ) : ℝ)) := by
      rw [Nat.cast_sub hsle]
      push_cast
      have hsnonneg : (0 : ℝ) ≤ s := by positivity
      nlinarith
    have hspos : (0 : ℝ) < ((s + 1 : ℕ) : ℝ) := by positivity
    apply le_of_mul_le_mul_right _ hspos
    rw [weightedChoose_succ_mul]
    have hmul :=
      mul_le_mul_of_nonneg_left hstep (weightedChoose_nonneg hC r s)
    nlinarith

theorem one_add_pow_le_central
    {C : ℝ} (hC : 0 ≤ C) (r : ℕ) :
    (1 + C) ^ r ≤
      ((r + 1 : ℕ) : ℝ) * (1 + C) *
        weightedChoose C r (centralReplacementUpperCount C r) := by
  refine (one_add_pow_le_mode hC r).trans ?_
  have h := mul_le_mul_of_nonneg_left
    (weightedChoose_mode_le_one_add_mul_central hC r)
    (by positivity : (0 : ℝ) ≤ ((r + 1 : ℕ) : ℝ))
  simpa only [mul_assoc] using h

end

end Erdos1165.HLOZShellZeroCentralNumerics
