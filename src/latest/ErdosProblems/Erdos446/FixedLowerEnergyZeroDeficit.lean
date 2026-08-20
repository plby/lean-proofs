/-
Copyright (c) 2026 The Formal Conjectures Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Formal Conjectures Authors
-/

import ErdosProblems.Erdos446.FixedLowerEnergy

/-!
# Erdős Problem 446: the zero-deficit energy convolution

This file bounds the strict interior of the zero-deficit slice in the
finite split of Ford's prefix-energy moment.  Both factors have initial
slack one, so Pyke's exact endpoint formula converts the slice into an
ordinary Abel convolution.  The proof is entirely finite.
-/

namespace Erdos446

open Finset Real
open scoped BigOperators

/-- The strict `d = 0` interior in the deficit-indexed energy sum. -/
noncomputable def fixedEnergyZeroDeficitInterior (k : ℕ) : ℝ :=
  ∑ p ∈ Finset.Ico 1 k,
    smirnovOccupancyMass (k - p) 1 (k - p) *
      smirnovOccupancyMass p 1 p

private theorem zeroDeficit_inv_factorial_mul_inv_factorial_eq_choose_div
    {k p : ℕ} (hpk : p ≤ k) :
    (1 / (((k - p).factorial : ℕ) : ℝ)) *
        (1 / (p.factorial : ℝ)) =
      (k.choose p : ℝ) / (k.factorial : ℝ) := by
  have hchooseNat := Nat.choose_mul_factorial_mul_factorial hpk
  have hchoose :
      (k.choose p : ℝ) * (p.factorial : ℝ) *
          (((k - p).factorial : ℕ) : ℝ) =
        (k.factorial : ℝ) := by
    exact_mod_cast hchooseNat
  field_simp
  nlinarith

/-- Exact conversion of the zero-deficit slice into an Abel convolution.
-/
theorem fixedEnergyZeroDeficitInterior_eq_abel
    {k : ℕ} (hk : 2 ≤ k) :
    fixedEnergyZeroDeficitInterior k =
      (1 / (k.factorial : ℝ)) *
        fordAbelInteriorSum (k - 1) 1 1 := by
  rw [fixedEnergyZeroDeficitInterior, fordAbelInteriorSum,
    Finset.mul_sum]
  have hksucc : k - 1 + 1 = k := by omega
  simp only [hksucc]
  apply Finset.sum_congr rfl
  intro p hpMem
  have hpData := Finset.mem_Ico.mp hpMem
  have hpk : p ≤ k := hpData.2.le
  have hp : 1 ≤ p := hpData.1
  have hkp : 1 ≤ k - p := by omega
  have hprefix := smirnovOccupancyMass_one_general_eq
    (q := k - p) (d := 0) hkp
  have hsuffix := smirnovOccupancyMass_one_general_eq
    (q := p) (d := 0) hp
  simp only [Nat.add_zero] at hprefix hsuffix
  rw [hprefix, hsuffix]
  have hfac := zeroDeficit_inv_factorial_mul_inv_factorial_eq_choose_div
    (k := k) (p := p) hpk
  calc
    _ =
        (((k - p + 1 : ℕ) : ℝ) ^ (k - p - 1)) *
          (((p + 1 : ℕ) : ℝ) ^ (p - 1)) *
          ((1 / (((k - p).factorial : ℕ) : ℝ)) *
            (1 / (p.factorial : ℝ))) := by ring
    _ = (((k - p + 1 : ℕ) : ℝ) ^ (k - p - 1)) *
          (((p + 1 : ℕ) : ℝ) ^ (p - 1)) *
          ((k.choose p : ℝ) / (k.factorial : ℝ)) := by
      rw [hfac]
    _ = (1 / (k.factorial : ℝ)) *
          ((k.choose p : ℝ) *
            (1 + (p : ℝ)) ^ (p - 1) *
            (1 + ((k - p : ℕ) : ℝ)) ^ (k - p - 1)) := by
      push_cast
      ring

/-- The zero-deficit interior is bounded on the exact one-slack mass
scale.  The generous numerical constant absorbs the elementary shift from
`k - 1` to `k + 1` in the Abel base. -/
theorem fixedEnergyZeroDeficitInterior_le
    {k : ℕ} (hk : 2 ≤ k) :
    fixedEnergyZeroDeficitInterior k ≤
      96 * Real.exp 4 *
        (((k + 1 : ℕ) : ℝ) ^ (k - 1) /
          (k.factorial : ℝ)) := by
  have hm : 0 < k - 1 := by omega
  have habel := fordAbelInteriorSum_le_exp_four
    (k - 1) hm (a := (1 : ℝ)) (b := (1 : ℝ))
      (by norm_num) (by norm_num)
  have hkCast : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ k)]
    norm_num
  have habel' : fordAbelInteriorSum (k - 1) 1 1 ≤
      Real.exp 4 * ((k : ℝ) + 2) ^ (k - 1) := by
    convert habel using 1
    rw [hkCast]
    ring
  have hshift : ((k : ℝ) + 2) ^ (k - 1) ≤
      96 * ((k : ℝ) + 1) ^ (k - 1) := by
    have hadd := add_three_pow_le_exp_three_mul_pow
      (k - 1) hm (N := (k : ℝ) - 1) (by
        rw [hkCast])
    have hbase : (k : ℝ) - 1 + 3 = (k : ℝ) + 2 := by ring
    rw [hbase] at hadd
    have hmono : ((k : ℝ) - 1) ^ (k - 1) ≤
        ((k : ℝ) + 1) ^ (k - 1) := by
      have hkOne : (1 : ℝ) ≤ k := by exact_mod_cast (by omega : 1 ≤ k)
      exact pow_le_pow_left₀ (sub_nonneg.mpr hkOne) (by linarith) _
    have he3 : Real.exp 3 ≤ (96 : ℝ) := by
      have he1 : Real.exp 1 ≤ (3 : ℝ) := Real.exp_one_lt_three.le
      have heq : Real.exp 3 = (Real.exp 1) ^ 3 := by
        rw [show (3 : ℝ) = 1 + 1 + 1 by norm_num,
          Real.exp_add, Real.exp_add]
        ring
      rw [heq]
      calc
        Real.exp 1 ^ 3 ≤ (3 : ℝ) ^ 3 :=
          pow_le_pow_left₀ (Real.exp_nonneg 1) he1 3
        _ ≤ 96 := by norm_num
    calc
      ((k : ℝ) + 2) ^ (k - 1) ≤
          Real.exp 3 * ((k : ℝ) - 1) ^ (k - 1) := hadd
      _ ≤ Real.exp 3 * ((k : ℝ) + 1) ^ (k - 1) :=
        mul_le_mul_of_nonneg_left hmono (Real.exp_nonneg 3)
      _ ≤ 96 * ((k : ℝ) + 1) ^ (k - 1) :=
        mul_le_mul_of_nonneg_right he3 (by positivity)
  rw [fixedEnergyZeroDeficitInterior_eq_abel hk]
  calc
    (1 / (k.factorial : ℝ)) *
          fordAbelInteriorSum (k - 1) 1 1 ≤
        (1 / (k.factorial : ℝ)) *
          (Real.exp 4 * ((k : ℝ) + 2) ^ (k - 1)) :=
      mul_le_mul_of_nonneg_left habel' (by positivity)
    _ ≤ (1 / (k.factorial : ℝ)) *
          (Real.exp 4 *
            (96 * ((k : ℝ) + 1) ^ (k - 1))) := by
      gcongr
    _ = 96 * Real.exp 4 *
        (((k + 1 : ℕ) : ℝ) ^ (k - 1) /
          (k.factorial : ℝ)) := by
      push_cast
      ring

/-- Model-scale form used in the final energy assembly. -/
theorem fixedEnergyZeroDeficitInterior_le_scale
    {k : ℕ} (hk : 2 ≤ k) :
    fixedEnergyZeroDeficitInterior k ≤
      288 * Real.exp 4 *
        ((k : ℝ) ^ k / ((k + 1).factorial : ℝ)) := by
  have hmassScale :
      (((k + 1 : ℕ) : ℝ) ^ (k - 1) / (k.factorial : ℝ)) ≤
        3 * ((k : ℝ) ^ k / ((k + 1).factorial : ℝ)) := by
    have hkR : (0 : ℝ) < k := by positivity
    have hfac : (0 : ℝ) < ((k + 1).factorial : ℝ) := by positivity
    have hbase :
        ((k : ℝ) + 1) = (k : ℝ) * (1 + (k : ℝ)⁻¹) := by
      field_simp
    have hpow : (((k + 1 : ℕ) : ℝ) ^ k) ≤
        3 * (k : ℝ) ^ k := by
      calc
        (((k + 1 : ℕ) : ℝ) ^ k) =
            (k : ℝ) ^ k * (1 + (k : ℝ)⁻¹) ^ k := by
          push_cast
          rw [hbase, mul_pow]
        _ ≤ (k : ℝ) ^ k * Real.exp 1 :=
          mul_le_mul_of_nonneg_left Real.one_add_inv_pow_le_exp
            (by positivity)
        _ ≤ (k : ℝ) ^ k * 3 :=
          mul_le_mul_of_nonneg_left Real.exp_one_lt_three.le
            (by positivity)
        _ = 3 * (k : ℝ) ^ k := by ring
    have hleft :
        (((k + 1 : ℕ) : ℝ) ^ (k - 1) / (k.factorial : ℝ)) =
          (((k + 1 : ℕ) : ℝ) ^ k /
            ((k + 1).factorial : ℝ)) := by
      have hexp : (((k : ℝ) + 1) ^ k) =
          (((k : ℝ) + 1) ^ (k - 1)) * ((k : ℝ) + 1) := by
        rw [← pow_succ]
        congr 1
        omega
      rw [Nat.factorial_succ]
      push_cast
      rw [hexp]
      field_simp
    rw [hleft]
    calc
      (((k + 1 : ℕ) : ℝ) ^ k /
          ((k + 1).factorial : ℝ)) ≤
          (3 * (k : ℝ) ^ k) /
            ((k + 1).factorial : ℝ) :=
        div_le_div_of_nonneg_right hpow hfac.le
      _ = 3 * ((k : ℝ) ^ k /
          ((k + 1).factorial : ℝ)) := by ring
  calc
    fixedEnergyZeroDeficitInterior k ≤
        96 * Real.exp 4 *
          (((k + 1 : ℕ) : ℝ) ^ (k - 1) /
            (k.factorial : ℝ)) :=
      fixedEnergyZeroDeficitInterior_le hk
    _ ≤ 96 * Real.exp 4 *
          (3 * ((k : ℝ) ^ k /
            ((k + 1).factorial : ℝ))) := by
      exact mul_le_mul_of_nonneg_left hmassScale (by positivity)
    _ = 288 * Real.exp 4 *
        ((k : ℝ) ^ k / ((k + 1).factorial : ℝ)) := by ring

end Erdos446
