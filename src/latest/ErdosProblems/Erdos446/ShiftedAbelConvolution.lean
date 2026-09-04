/-
Copyright (c) 2026 The Formal Conjectures Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Formal Conjectures Authors
-/

import ErdosProblems.Erdos446.AbelConvolution

/-!
# Erdős Problem 446: shifted Abel convolution

Ford's first-crossing decomposition also produces an Abel convolution whose
first affine parameter is a negative integer `-d`.  After the change of
index `p = p' + d - 1`, the ordinary `a=-1` convolution reappears, with one
extra power.  This file bounds that power together with the corresponding
ratio of binomial coefficients.
-/

namespace Erdos446

open Finset Real
open scoped BigOperators

/-- The binomial coefficient and extra power introduced by shifting an Abel
sum through `e` places. -/
theorem shifted_choose_power_le (t p e : ℕ)
    (hp : 1 ≤ p) (hpt : p ≤ t) {N : ℝ}
    (hN : (t - 1 : ℕ) ≤ N) (hN0 : 0 ≤ N) :
    (Nat.choose (t + e) (p + e) : ℝ) * (p - 1 : ℕ) ^ e ≤
      N ^ e * Nat.choose t p := by
  induction e with
  | zero => simp
  | succ e ih =>
      have ht : 1 ≤ t := hp.trans hpt
      have hdenPos : (0 : ℝ) < ((p + e + 1 : ℕ) : ℝ) := by positivity
      have hchooseNonneg : (0 : ℝ) ≤ Nat.choose (t + e) (p + e) := by
        positivity
      have hfactor :
          ((p - 1 : ℕ) : ℝ) * (t + e + 1 : ℕ) ≤
            N * (p + e + 1 : ℕ) := by
        have htp : (0 : ℝ) ≤ ((t - p : ℕ) : ℝ) := by positivity
        have hid :
            ((t - 1 : ℕ) : ℝ) * (p + e + 1 : ℕ) -
                ((p - 1 : ℕ) : ℝ) * (t + e + 1 : ℕ) =
              (e + 2 : ℕ) * (t - p : ℕ) := by
          push_cast [Nat.cast_sub hp, Nat.cast_sub ht, Nat.cast_sub hpt]
          ring
        have hfirst :
            ((p - 1 : ℕ) : ℝ) * (t + e + 1 : ℕ) ≤
              ((t - 1 : ℕ) : ℝ) * (p + e + 1 : ℕ) := by
          nlinarith
        have hsecond :
            ((t - 1 : ℕ) : ℝ) * (p + e + 1 : ℕ) ≤
              N * (p + e + 1 : ℕ) := by
          exact mul_le_mul_of_nonneg_right hN hdenPos.le
        exact hfirst.trans hsecond
      have hrecNat := Nat.add_one_mul_choose_eq (t + e) (p + e)
      have hrec' :
          (Nat.choose (t + e + 1) (p + e + 1) : ℝ) *
              ((p + e + 1 : ℕ) : ℝ) =
            ((t + e + 1 : ℕ) : ℝ) *
              Nat.choose (t + e) (p + e) := by
        exact_mod_cast hrecNat.symm
      have hrec :
          ((p + e + 1 : ℕ) : ℝ) *
              Nat.choose (t + e + 1) (p + e + 1) =
            ((t + e + 1 : ℕ) : ℝ) *
              Nat.choose (t + e) (p + e) := by
        simpa [mul_comm] using hrec'
      have hstep :
          (Nat.choose (t + e + 1) (p + e + 1) : ℝ) *
              (p - 1 : ℕ) ≤
            N * Nat.choose (t + e) (p + e) := by
        apply le_of_mul_le_mul_left ?_ hdenPos
        rw [show
          ((p + e + 1 : ℕ) : ℝ) *
                ((Nat.choose (t + e + 1) (p + e + 1) : ℝ) *
                  (p - 1 : ℕ)) =
              (((p + e + 1 : ℕ) : ℝ) *
                Nat.choose (t + e + 1) (p + e + 1)) *
                  (p - 1 : ℕ) by ring, hrec]
        calc
          ((t + e + 1 : ℕ) : ℝ) *
                Nat.choose (t + e) (p + e) * (p - 1 : ℕ) =
              (((p - 1 : ℕ) : ℝ) * (t + e + 1 : ℕ)) *
                Nat.choose (t + e) (p + e) := by ring
          _ ≤ (N * (p + e + 1 : ℕ)) *
                Nat.choose (t + e) (p + e) :=
            mul_le_mul_of_nonneg_right hfactor hchooseNonneg
          _ = ((p + e + 1 : ℕ) : ℝ) *
                (N * Nat.choose (t + e) (p + e)) := by ring
      have hpOneNonneg : (0 : ℝ) ≤ ((p - 1 : ℕ) : ℝ) := by positivity
      calc
        (Nat.choose (t + (e + 1)) (p + (e + 1)) : ℝ) *
              (p - 1 : ℕ) ^ (e + 1) =
            ((Nat.choose (t + e + 1) (p + e + 1) : ℝ) *
              (p - 1 : ℕ)) * ((p - 1 : ℕ) : ℝ) ^ e := by
          ring_nf
        _ ≤ (N * Nat.choose (t + e) (p + e)) *
              ((p - 1 : ℕ) : ℝ) ^ e :=
          mul_le_mul_of_nonneg_right hstep (pow_nonneg hpOneNonneg e)
        _ = N * ((Nat.choose (t + e) (p + e) : ℝ) *
              ((p - 1 : ℕ) : ℝ) ^ e) := by ring
        _ ≤ N * (N ^ e * Nat.choose t p) :=
          mul_le_mul_of_nonneg_left ih hN0
        _ = N ^ (e + 1) * Nat.choose t p := by
          rw [pow_succ]
          ring

/-- Abel's interior sum after shifting both the upper and lower binomial
indices by `e`. -/
noncomputable def fordAbelShiftedIndexSum
    (t e : ℕ) (B : ℝ) : ℝ :=
  ∑ p ∈ Finset.Ico 1 t,
    (Nat.choose (t + e) (p + e) : ℝ) *
      (p - 1 : ℕ) ^ (p + e - 1) *
      (B + (t - p : ℕ)) ^ (t - p - 1)

/-- The shifted Abel sum costs only the corresponding extra power of the
natural total base. -/
theorem fordAbelShiftedIndexSum_le
    {t e : ℕ} {B : ℝ} (ht : 1 < t) (hB : 1 ≤ B) :
    fordAbelShiftedIndexSum t e B ≤
      Real.exp 4 * (t + B - 1) ^ (t + e - 1) := by
  let N : ℝ := t + B - 1
  have hN0 : 0 ≤ N := by dsimp [N]; linarith
  have hN : ((t - 1 : ℕ) : ℝ) ≤ N := by
    rw [Nat.cast_sub (by omega : 1 ≤ t)]
    dsimp [N]
    linarith
  have hpoint : ∀ p ∈ Finset.Ico 1 t,
      (Nat.choose (t + e) (p + e) : ℝ) *
          (p - 1 : ℕ) ^ (p + e - 1) *
          (B + (t - p : ℕ)) ^ (t - p - 1) ≤
        N ^ e *
          ((Nat.choose t p : ℝ) *
            ((-1 : ℝ) + p) ^ (p - 1) *
            (B + (t - p : ℕ)) ^ (t - p - 1)) := by
    intro p hpMem
    have hpData := Finset.mem_Ico.mp hpMem
    have hpowIndex : p + e - 1 = (p - 1) + e := by omega
    have hbase : ((p - 1 : ℕ) : ℝ) = (-1 : ℝ) + p := by
      rw [Nat.cast_sub hpData.1]
      ring
    have hcoeff := shifted_choose_power_le t p e hpData.1 hpData.2.le
      hN hN0
    rw [hpowIndex, pow_add]
    have hrest :
        0 ≤ ((p - 1 : ℕ) : ℝ) ^ (p - 1) *
          (B + (t - p : ℕ)) ^ (t - p - 1) := by positivity
    calc
      (Nat.choose (t + e) (p + e) : ℝ) *
            (((p - 1 : ℕ) : ℝ) ^ (p - 1) *
              ((p - 1 : ℕ) : ℝ) ^ e) *
            (B + (t - p : ℕ)) ^ (t - p - 1) =
          ((Nat.choose (t + e) (p + e) : ℝ) *
              ((p - 1 : ℕ) : ℝ) ^ e) *
            (((p - 1 : ℕ) : ℝ) ^ (p - 1) *
              (B + (t - p : ℕ)) ^ (t - p - 1)) := by ring
      _ ≤ (N ^ e * Nat.choose t p) *
            (((p - 1 : ℕ) : ℝ) ^ (p - 1) *
              (B + (t - p : ℕ)) ^ (t - p - 1)) :=
        mul_le_mul_of_nonneg_right hcoeff hrest
      _ = N ^ e *
          ((Nat.choose t p : ℝ) *
            ((-1 : ℝ) + p) ^ (p - 1) *
            (B + (t - p : ℕ)) ^ (t - p - 1)) := by
        rw [← hbase]
        ring
  have hsum : fordAbelShiftedIndexSum t e B ≤
      N ^ e * fordAbelInteriorSum (t - 1) (-1) B := by
    rw [fordAbelShiftedIndexSum, fordAbelInteriorSum, Finset.mul_sum]
    simpa only [Nat.sub_add_cancel (by omega : 1 ≤ t)] using
      Finset.sum_le_sum hpoint
  have hordinary : fordAbelInteriorSum (t - 1) (-1) B ≤
      Real.exp 4 * N ^ (t - 1) := by
    have h := fordAbelInteriorSum_le_exp_four (t - 1)
      (by omega) (a := (-1 : ℝ)) (b := B) (by norm_num) (by linarith)
    rw [Nat.cast_sub (by omega : 1 ≤ t)] at h
    dsimp [N]
    convert h using 1
    ring
  calc
    fordAbelShiftedIndexSum t e B ≤
        N ^ e * fordAbelInteriorSum (t - 1) (-1) B := hsum
    _ ≤ N ^ e * (Real.exp 4 * N ^ (t - 1)) :=
      mul_le_mul_of_nonneg_left hordinary (pow_nonneg hN0 e)
    _ = Real.exp 4 * N ^ (t + e - 1) := by
      rw [show t + e - 1 = e + (t - 1) by omega, pow_add]
      ring
    _ = Real.exp 4 * (t + B - 1) ^ (t + e - 1) := rfl

/-- The same shifted convolution in the original index `p`, where the first
affine base is `p-d`. -/
noncomputable def fordAbelNegativeShiftSum
    (t d : ℕ) (B : ℝ) : ℝ :=
  ∑ p ∈ Finset.Ico d t,
    (Nat.choose t p : ℝ) *
      (p - d : ℕ) ^ (p - 1) *
      (B + (t - p : ℕ)) ^ (t - p - 1)

/-- Reindexing `p' = p-d+1` identifies the negative-parameter convolution
with the shifted-index sum above. -/
theorem fordAbelNegativeShiftSum_eq
    {t d : ℕ} {B : ℝ} (hd : 1 ≤ d) (hdt : d < t) :
    fordAbelNegativeShiftSum t d B =
      fordAbelShiftedIndexSum (t - d + 1) (d - 1) B := by
  classical
  rw [fordAbelNegativeShiftSum, fordAbelShiftedIndexSum]
  apply Finset.sum_bij (fun p _ ↦ p - d + 1)
  · intro p hp
    have hpData := Finset.mem_Ico.mp hp
    rw [Finset.mem_Ico]
    omega
  · intro p₁ hp₁ p₂ hp₂ heq
    have hp₁Data := Finset.mem_Ico.mp hp₁
    have hp₂Data := Finset.mem_Ico.mp hp₂
    omega
  · intro q hq
    have hqData := Finset.mem_Ico.mp hq
    refine ⟨q + d - 1, ?_, ?_⟩
    · rw [Finset.mem_Ico]
      omega
    · omega
  · intro p hp
    have hpData := Finset.mem_Ico.mp hp
    have htIndex : (t - d + 1) + (d - 1) = t := by omega
    have hpIndex : (p - d + 1) + (d - 1) = p := by omega
    have hbase : p - d + 1 - 1 = p - d := by omega
    have hright : (t - d + 1) - (p - d + 1) = t - p := by omega
    rw [htIndex, hpIndex, hbase, hright]

/-- Uniform shifted Abel bound in the original parameters. -/
theorem fordAbelNegativeShiftSum_le
    {t d : ℕ} {B : ℝ} (hd : 1 ≤ d) (hdt : d < t) (hB : 1 ≤ B) :
    fordAbelNegativeShiftSum t d B ≤
      Real.exp 4 * (t - d + B) ^ (t - 1) := by
  rw [fordAbelNegativeShiftSum_eq hd hdt]
  have h := fordAbelShiftedIndexSum_le
    (t := t - d + 1) (e := d - 1) (B := B) (by omega) hB
  have hbase :
      (((t - d + 1 : ℕ) : ℝ) + B - 1) = (t : ℝ) - d + B := by
    rw [Nat.cast_add, Nat.cast_sub hdt.le]
    push_cast
    ring
  have hexponent : t - d + 1 + (d - 1) - 1 = t - 1 := by omega
  rw [hbase, hexponent] at h
  exact h

/-- The original real-affine notation for the integer negative parameter
`a=-d`. -/
noncomputable def fordAbelIntegerNegativeSum
    (t d : ℕ) (B : ℝ) : ℝ :=
  ∑ p ∈ Finset.Ico d t,
    (Nat.choose t p : ℝ) *
      ((p : ℝ) - (d : ℝ)) ^ (p - 1) *
      (B + (t - p : ℕ)) ^ (t - p - 1)

theorem fordAbelIntegerNegativeSum_eq
    (t d : ℕ) (B : ℝ) :
    fordAbelIntegerNegativeSum t d B =
      fordAbelNegativeShiftSum t d B := by
  rw [fordAbelIntegerNegativeSum, fordAbelNegativeShiftSum]
  apply Finset.sum_congr rfl
  intro p hp
  have hdp := (Finset.mem_Ico.mp hp).1
  rw [Nat.cast_sub hdp]

theorem fordAbelIntegerNegativeSum_le
    {t d : ℕ} {B : ℝ} (hd : 1 ≤ d) (hdt : d < t) (hB : 1 ≤ B) :
    fordAbelIntegerNegativeSum t d B ≤
      Real.exp 4 * (t - d + B) ^ (t - 1) := by
  rw [fordAbelIntegerNegativeSum_eq]
  exact fordAbelNegativeShiftSum_le hd hdt hB

/-- The strict-positive-base sub-sum which occurs in Ford's statement of
the Abel bound. -/
noncomputable def fordAbelIntegerNegativePositiveSum
    (t d : ℕ) (B : ℝ) : ℝ :=
  ∑ p ∈ Finset.Ico (d + 1) t,
    (Nat.choose t p : ℝ) *
      ((p : ℝ) - (d : ℝ)) ^ (p - 1) *
      (B + (t - p : ℕ)) ^ (t - p - 1)

theorem fordAbelIntegerNegativePositiveSum_le
    {t d : ℕ} {B : ℝ} (hd : 1 ≤ d) (hdt : d < t) (hB : 1 ≤ B) :
    fordAbelIntegerNegativePositiveSum t d B ≤
      Real.exp 4 * (t - d + B) ^ (t - 1) := by
  calc
    fordAbelIntegerNegativePositiveSum t d B ≤
        fordAbelIntegerNegativeSum t d B := by
      rw [fordAbelIntegerNegativePositiveSum, fordAbelIntegerNegativeSum]
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro p hp
        have hpData := Finset.mem_Ico.mp hp
        rw [Finset.mem_Ico]
        omega
      · intro p hp _hpNot
        have hpData := Finset.mem_Ico.mp hp
        have hbase : (0 : ℝ) ≤ (p : ℝ) - d := by
          have hdpR : (d : ℝ) ≤ p := by exact_mod_cast hpData.1
          linarith
        exact mul_nonneg
          (mul_nonneg (by positivity)
            (pow_nonneg hbase _))
          (pow_nonneg (by positivity) _)
    _ ≤ Real.exp 4 * (t - d + B) ^ (t - 1) :=
      fordAbelIntegerNegativeSum_le hd hdt hB

end Erdos446
