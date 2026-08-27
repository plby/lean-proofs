/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import Mathlib.Tactic

/-! # Integer availability floors with the exact stopped-moment normalization -/

namespace Erdos207

open scoped NNReal

theorem nat_le_twice_denominator_mul_quotient
    (n d : ℕ) (hd : 0 < d) (hdn : d ≤ n) :
    n ≤ 2 * d * (n / d) := by
  have hquot : 1 ≤ n / d := (Nat.le_div_iff_mul_le hd).mpr (by simpa using hdn)
  have hrem := Nat.mod_lt n hd
  have heq := Nat.div_add_mod n d
  have hprod : d ≤ d * (n / d) := by nlinarith
  nlinarith

def dyadicMomentFloor (N t k : ℕ) : ℕ := N ^ 3 / (8 * t ^ k)

theorem dyadicMomentFloor_pos
    (N t k : ℕ) (ht : 0 < t) (hsize : 8 * t ^ k ≤ N ^ 3) :
    0 < dyadicMomentFloor N t k := by
  unfold dyadicMomentFloor
  exact Nat.div_pos hsize (by positivity)

theorem dyadicMomentFloor_lower_budget
    (N t k : ℕ) (ht : 0 < t) (hsize : 8 * t ^ k ≤ N ^ 3) :
    N ^ 3 ≤ 16 * t ^ k * dyadicMomentFloor N t k := by
  have h := nat_le_twice_denominator_mul_quotient (N ^ 3) (8 * t ^ k) (by positivity) hsize
  calc
    _ ≤ 2 * (8 * t ^ k) * (N ^ 3 / (8 * t ^ k)) := h
    _ = _ := by unfold dyadicMomentFloor; ring

theorem dyadicMomentFloor_joint_ratio_nat
    (N t k steps : ℕ) (hN : 1 ≤ N) (ht : 32 ≤ t) (hsteps : steps ≤ N ^ 2)
    (hsize : 8 * t ^ k ≤ N ^ 3) :
    steps * (N + 1) ≤ t ^ (k + 1) * dyadicMomentFloor N t k := by
  have hbudget := dyadicMomentFloor_lower_budget N t k (by omega) hsize
  calc
    steps * (N + 1) ≤ N ^ 2 * (2 * N) := Nat.mul_le_mul hsteps (by omega)
    _ = 2 * N ^ 3 := by ring
    _ ≤ 2 * (16 * t ^ k * dyadicMomentFloor N t k) := Nat.mul_le_mul_left 2 hbudget
    _ = 32 * (t ^ k * dyadicMomentFloor N t k) := by ring
    _ ≤ t * (t ^ k * dyadicMomentFloor N t k) := Nat.mul_le_mul_right _ ht
    _ = _ := by rw [pow_succ]; ring

theorem dyadicMomentFloor_joint_ratio
    (N t k steps : ℕ) (hN : 1 ≤ N) (ht : 32 ≤ t) (hsteps : steps ≤ N ^ 2)
    (hsize : 8 * t ^ k ≤ N ^ 3) :
    (steps : ℝ≥0) * (dyadicMomentFloor N t k : ℝ≥0)⁻¹ ≤
      (t : ℝ≥0) ^ (k + 1) * (N + 1 : ℝ≥0)⁻¹ := by
  have hD : (0 : ℝ≥0) < dyadicMomentFloor N t k := by
    exact_mod_cast dyadicMomentFloor_pos N t k (by omega) hsize
  change (steps : ℝ≥0) / (dyadicMomentFloor N t k : ℝ≥0) ≤
    (t : ℝ≥0) ^ (k + 1) / (N + 1 : ℝ≥0)
  apply (div_le_div_iff₀ hD (by positivity)).mpr
  exact_mod_cast dyadicMomentFloor_joint_ratio_nat N t k steps hN ht hsteps hsize

theorem dyadicMomentFloor_le_real_bound
    (N t k : ℕ) :
    (dyadicMomentFloor N t k : ℝ) ≤ (N : ℝ) ^ 3 / (8 * (t : ℝ) ^ k) := by
  have h : ((N ^ 3 / (8 * t ^ k) : ℕ) : ℝ) ≤ ((N ^ 3 : ℕ) : ℝ) / ((8 * t ^ k : ℕ) : ℝ) :=
    Nat.cast_div_le
  simpa only [dyadicMomentFloor, Nat.cast_pow, Nat.cast_mul, Nat.cast_ofNat] using h

theorem dyadicMomentFloor_le_available
    (N t k M : ℕ) (ht : 0 < t)
    (hM : (N : ℝ) ^ 3 / (4 * (t : ℝ) ^ k) ≤ (M : ℝ)) :
    dyadicMomentFloor N t k ≤ M := by
  have htR : (0 : ℝ) < t := by exact_mod_cast ht
  have hreal : (dyadicMomentFloor N t k : ℝ) ≤ M := by
    refine (dyadicMomentFloor_le_real_bound N t k).trans ((?_ :
      (N : ℝ) ^ 3 / (8 * (t : ℝ) ^ k) ≤ (N : ℝ) ^ 3 / (4 * (t : ℝ) ^ k)).trans hM)
    apply div_le_div_of_nonneg_left (by positivity) (by positivity)
    have hp : 0 ≤ (t : ℝ) ^ k := by positivity
    linarith
  exact_mod_cast hreal

theorem momentFloor_size_of_power_scale
    (N t R k : ℕ) (ht : 8 ≤ t) (hN : t ^ R ≤ N) (hgap : k + 1 ≤ 3 * R) :
    8 * t ^ k ≤ N ^ 3 := by
  calc
    8 * t ^ k ≤ t * t ^ k := Nat.mul_le_mul_right _ ht
    _ = t ^ (k + 1) := by rw [pow_succ]; ring
    _ ≤ t ^ (3 * R) := Nat.pow_le_pow_right (by omega) hgap
    _ = (t ^ R) ^ 3 := by rw [← pow_mul]; congr 1; omega
    _ ≤ N ^ 3 := Nat.pow_le_pow_left hN 3

end Erdos207
