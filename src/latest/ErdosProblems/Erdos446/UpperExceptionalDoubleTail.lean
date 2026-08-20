/-
Copyright (c) 2026 The Formal Conjectures Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Formal Conjectures Authors
-/

import ErdosProblems.Erdos446.UpperFiniteLayerSum

/-!
# Erdős Problem 446: finite double-exponential exceptional tails

After factorial suppression, summing Ford's crowding witnesses first over
the dyadic scale and then over the failed depth leaves a polynomial weight
times `2^(-2^h)`.  The lemmas below bound those finite tails in the two
cases `k-v ≥ γ+5` and `k-v < γ+5`.
-/

namespace Erdos446

open Finset Real
open scoped BigOperators

private theorem add_le_two_pow_add (h t : ℕ) :
    2 ^ h + t ≤ 2 ^ (h + t) := by
  rw [pow_add]
  have ht : t + 1 ≤ 2 ^ t := by
    induction t with
    | zero => norm_num
    | succ t ih =>
        rw [pow_succ]
        omega
  have hh : 1 ≤ 2 ^ h := one_le_pow₀ (by omega)
  calc
    2 ^ h + t ≤ 2 ^ h * (t + 1) := by nlinarith
    _ ≤ 2 ^ h * 2 ^ t := Nat.mul_le_mul_left _ ht

private theorem doubleExpTerm_le_geometric (h t : ℕ) :
    1 / (2 : ℝ) ^ (2 ^ (h + t)) ≤
      (1 / (2 : ℝ) ^ (2 ^ h)) * (1 / 2 : ℝ) ^ t := by
  have hexp := add_le_two_pow_add h t
  have hp := pow_le_pow_of_le_one
    (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (1 / 2 : ℝ) ≤ 1) hexp
  calc
    1 / (2 : ℝ) ^ (2 ^ (h + t)) =
        (1 / 2 : ℝ) ^ (2 ^ (h + t)) := by
      simp [one_div, inv_pow]
    _ ≤ (1 / 2 : ℝ) ^ (2 ^ h + t) := hp
    _ = (1 / (2 : ℝ) ^ (2 ^ h)) * (1 / 2 : ℝ) ^ t := by
      simp [pow_add, one_div, inv_pow]

/-- A finite double-exponential tail is at most twice its first term. -/
theorem doubleExponentialTailPartial_le (h R : ℕ) :
    (∑ t ∈ Finset.range R,
        1 / (2 : ℝ) ^ (2 ^ (h + t))) ≤
      2 / (2 : ℝ) ^ (2 ^ h) := by
  have hgeom :
      (∑ t ∈ Finset.range R, (1 / 2 : ℝ) ^ t) ≤ 2 := by
    rw [geom_sum_eq (by norm_num : (1 / 2 : ℝ) ≠ 1)]
    have hp : 0 ≤ (1 / 2 : ℝ) ^ R := by positivity
    have hid : ((1 / 2 : ℝ) ^ R - 1) / ((1 / 2 : ℝ) - 1) =
        2 * (1 - (1 / 2 : ℝ) ^ R) := by ring
    rw [hid]
    nlinarith
  calc
    (∑ t ∈ Finset.range R,
        1 / (2 : ℝ) ^ (2 ^ (h + t))) ≤
      ∑ t ∈ Finset.range R,
        (1 / (2 : ℝ) ^ (2 ^ h)) * (1 / 2 : ℝ) ^ t := by
      exact Finset.sum_le_sum fun t ht ↦ doubleExpTerm_le_geometric h t
    _ = (1 / (2 : ℝ) ^ (2 ^ h)) *
        (∑ t ∈ Finset.range R, (1 / 2 : ℝ) ^ t) := by
      rw [Finset.mul_sum]
    _ ≤ (1 / (2 : ℝ) ^ (2 ^ h)) * 2 := by
      exact mul_le_mul_of_nonneg_left hgeom (by positivity)
    _ = 2 / (2 : ℝ) ^ (2 ^ h) := by ring

private theorem shiftedCubicGeometricPartial_le (R : ℕ) :
    (∑ t ∈ Finset.range R,
        (((t + 2 : ℕ) : ℝ) ^ 3) * (1 / 2 : ℝ) ^ t) ≤ 416 := by
  have hpoint : ∀ t : ℕ,
      (((t + 2 : ℕ) : ℝ) ^ 3) ≤
        8 * (((t + 1 : ℕ) : ℝ) ^ 3) := by
    intro t
    have hnat : t + 2 ≤ 2 * (t + 1) := by omega
    have hreal : ((t + 2 : ℕ) : ℝ) ≤
        2 * ((t + 1 : ℕ) : ℝ) := by exact_mod_cast hnat
    calc
      (((t + 2 : ℕ) : ℝ) ^ 3) ≤
          (2 * ((t + 1 : ℕ) : ℝ)) ^ 3 :=
        pow_le_pow_left₀ (by positivity) hreal 3
      _ = 8 * (((t + 1 : ℕ) : ℝ) ^ 3) := by ring
  calc
    (∑ t ∈ Finset.range R,
        (((t + 2 : ℕ) : ℝ) ^ 3) * (1 / 2 : ℝ) ^ t) ≤
        8 * cubicGeometricPartial R := by
      rw [cubicGeometricPartial, Finset.mul_sum]
      apply Finset.sum_le_sum
      intro t ht
      simpa [div_eq_mul_inv, one_div, inv_pow, mul_assoc] using
        mul_le_mul_of_nonneg_right (hpoint t)
          (show 0 ≤ (1 / 2 : ℝ) ^ t by positivity)
    _ ≤ 8 * 52 :=
      mul_le_mul_of_nonneg_left (cubicGeometricPartial_le R) (by norm_num)
    _ = 416 := by norm_num

/-- Reindexed exceptional-depth sum when `b = k-v ≥ γ+5`, with
`r=b-γ`. -/
noncomputable def fordExceptionalHighDepthTail (b r R : ℕ) : ℝ :=
  ∑ t ∈ Finset.range R,
    ((b + t + 2 : ℕ) : ℝ) * ((t + 2 : ℕ) : ℝ) ^ 2 /
      (2 : ℝ) ^ (2 ^ (r + 1 + t))

theorem fordExceptionalHighDepthTail_le
    {b r : ℕ} (hb : 1 ≤ b) (R : ℕ) :
    fordExceptionalHighDepthTail b r R ≤
      1664 * (b : ℝ) / (2 : ℝ) ^ (2 ^ r) := by
  have hpoly : ∀ t : ℕ,
      ((b + t + 2 : ℕ) : ℝ) * ((t + 2 : ℕ) : ℝ) ^ 2 ≤
        (2 * (b : ℝ)) * ((t + 2 : ℕ) : ℝ) ^ 3 := by
    intro t
    have hnat : b + t + 2 ≤ 2 * b * (t + 2) := by
      have h1 := Nat.mul_le_mul_left b (show 1 ≤ t + 2 by omega)
      have h2 := Nat.mul_le_mul_right (t + 2) hb
      nlinarith
    have hreal : ((b + t + 2 : ℕ) : ℝ) ≤
        (2 * (b : ℝ)) * ((t + 2 : ℕ) : ℝ) := by exact_mod_cast hnat
    calc
      ((b + t + 2 : ℕ) : ℝ) * ((t + 2 : ℕ) : ℝ) ^ 2 ≤
          ((2 * (b : ℝ)) * ((t + 2 : ℕ) : ℝ)) *
            ((t + 2 : ℕ) : ℝ) ^ 2 :=
        mul_le_mul_of_nonneg_right hreal (by positivity)
      _ = (2 * (b : ℝ)) * ((t + 2 : ℕ) : ℝ) ^ 3 := by ring
  have hpow : (2 : ℝ) ^ (2 ^ r) ≤ (2 : ℝ) ^ (2 ^ (r + 1)) := by
    have hr : 2 ^ r ≤ 2 ^ (r + 1) := by
      rw [pow_succ]
      omega
    exact pow_le_pow_right₀ (by norm_num) hr
  have hinv : 1 / (2 : ℝ) ^ (2 ^ (r + 1)) ≤
      1 / (2 : ℝ) ^ (2 ^ r) := by
    exact one_div_le_one_div_of_le (by positivity) hpow
  calc
    fordExceptionalHighDepthTail b r R ≤
        (2 * (b : ℝ)) * (1 / (2 : ℝ) ^ (2 ^ (r + 1))) *
          (∑ t ∈ Finset.range R,
            (((t + 2 : ℕ) : ℝ) ^ 3) * (1 / 2 : ℝ) ^ t) := by
      rw [fordExceptionalHighDepthTail, Finset.mul_sum]
      apply Finset.sum_le_sum
      intro t ht
      have hterm := doubleExpTerm_le_geometric (r + 1) t
      rw [show r + 1 + t = (r + 1) + t by omega]
      calc
        ((b + t + 2 : ℕ) : ℝ) * ((t + 2 : ℕ) : ℝ) ^ 2 /
              (2 : ℝ) ^ (2 ^ ((r + 1) + t)) ≤
            ((2 * (b : ℝ)) * ((t + 2 : ℕ) : ℝ) ^ 3) *
              (1 / (2 : ℝ) ^ (2 ^ ((r + 1) + t))) := by
          rw [div_eq_mul_inv, one_div]
          exact mul_le_mul_of_nonneg_right (hpoly t) (by positivity)
        _ ≤ ((2 * (b : ℝ)) * ((t + 2 : ℕ) : ℝ) ^ 3) *
              ((1 / (2 : ℝ) ^ (2 ^ (r + 1))) *
                (1 / 2 : ℝ) ^ t) := by gcongr
        _ = (2 * (b : ℝ)) * (1 / (2 : ℝ) ^ (2 ^ (r + 1))) *
              ((((t + 2 : ℕ) : ℝ) ^ 3) * (1 / 2 : ℝ) ^ t) := by ring
    _ ≤ (2 * (b : ℝ)) * (1 / (2 : ℝ) ^ (2 ^ (r + 1))) * 416 := by
      gcongr
      exact shiftedCubicGeometricPartial_le R
    _ ≤ (2 * (b : ℝ)) * (1 / (2 : ℝ) ^ (2 ^ r)) * 416 := by
      gcongr
    _ = 832 * (b : ℝ) / (2 : ℝ) ^ (2 ^ r) := by ring
    _ ≤ 1664 * (b : ℝ) / (2 : ℝ) ^ (2 ^ r) := by
      gcongr
      norm_num

/-- Reindexed exceptional-depth sum in the complementary case.  Here
`δ = γ+5-b ≥ 1`. -/
noncomputable def fordExceptionalLowDepthTail (γ δ R : ℕ) : ℝ :=
  ∑ t ∈ Finset.range R,
    ((γ + t + 7 : ℕ) : ℝ) * ((δ + t + 2 : ℕ) : ℝ) ^ 2 /
      (2 : ℝ) ^ (2 ^ (6 + t))

theorem fordExceptionalLowDepthTail_le
    {γ δ : ℕ} (hδ : 1 ≤ δ) (R : ℕ) :
    fordExceptionalLowDepthTail γ δ R ≤
      52416 * ((γ + 1 : ℕ) : ℝ) * (δ : ℝ) ^ 2 := by
  have hpoly : ∀ t : ℕ,
      ((γ + t + 7 : ℕ) : ℝ) * ((δ + t + 2 : ℕ) : ℝ) ^ 2 ≤
        126 * ((γ + 1 : ℕ) : ℝ) * (δ : ℝ) ^ 2 *
          ((t + 1 : ℕ) : ℝ) ^ 3 := by
    intro t
    have hA : γ + t + 7 ≤ 7 * (γ + 1) * (t + 1) := by
      nlinarith [Nat.zero_le (γ * t)]
    have hB : δ + t + 2 ≤ 3 * δ * (t + 1) := by
      nlinarith [Nat.zero_le (δ * t)]
    have hAR : ((γ + t + 7 : ℕ) : ℝ) ≤
        7 * ((γ + 1 : ℕ) : ℝ) * ((t + 1 : ℕ) : ℝ) := by
      exact_mod_cast hA
    have hBR : ((δ + t + 2 : ℕ) : ℝ) ≤
        3 * (δ : ℝ) * ((t + 1 : ℕ) : ℝ) := by exact_mod_cast hB
    calc
      ((γ + t + 7 : ℕ) : ℝ) * ((δ + t + 2 : ℕ) : ℝ) ^ 2 ≤
          (7 * ((γ + 1 : ℕ) : ℝ) * ((t + 1 : ℕ) : ℝ)) *
            (3 * (δ : ℝ) * ((t + 1 : ℕ) : ℝ)) ^ 2 := by gcongr
      _ ≤ 126 * ((γ + 1 : ℕ) : ℝ) * (δ : ℝ) ^ 2 *
            ((t + 1 : ℕ) : ℝ) ^ 3 := by
        have hnon : 0 ≤ ((γ + 1 : ℕ) : ℝ) * (δ : ℝ) ^ 2 *
            ((t + 1 : ℕ) : ℝ) ^ 3 := by positivity
        nlinarith
  calc
    fordExceptionalLowDepthTail γ δ R ≤
        126 * ((γ + 1 : ℕ) : ℝ) * (δ : ℝ) ^ 2 *
          cubicGeometricPartial R := by
      rw [fordExceptionalLowDepthTail, cubicGeometricPartial,
        Finset.mul_sum]
      apply Finset.sum_le_sum
      intro t ht
      have hterm := doubleExpTerm_le_geometric 6 t
      calc
        ((γ + t + 7 : ℕ) : ℝ) * ((δ + t + 2 : ℕ) : ℝ) ^ 2 /
              (2 : ℝ) ^ (2 ^ (6 + t)) ≤
            (126 * ((γ + 1 : ℕ) : ℝ) * (δ : ℝ) ^ 2 *
              ((t + 1 : ℕ) : ℝ) ^ 3) *
                (1 / (2 : ℝ) ^ (2 ^ (6 + t))) := by
          rw [div_eq_mul_inv, one_div]
          exact mul_le_mul_of_nonneg_right (hpoly t) (by positivity)
        _ ≤ (126 * ((γ + 1 : ℕ) : ℝ) * (δ : ℝ) ^ 2 *
              ((t + 1 : ℕ) : ℝ) ^ 3) *
                ((1 / (2 : ℝ) ^ (2 ^ 6)) * (1 / 2 : ℝ) ^ t) := by
          gcongr
        _ ≤ 126 * ((γ + 1 : ℕ) : ℝ) * (δ : ℝ) ^ 2 *
              ((((t + 1 : ℕ) : ℝ) ^ 3) / (2 : ℝ) ^ t) := by
          have hhalf : 1 / (2 : ℝ) ^ (2 ^ 6) ≤ 1 := by norm_num
          calc
            (126 * ((γ + 1 : ℕ) : ℝ) * (δ : ℝ) ^ 2 *
                ((t + 1 : ℕ) : ℝ) ^ 3) *
                  ((1 / (2 : ℝ) ^ (2 ^ 6)) * (1 / 2 : ℝ) ^ t) ≤
              (126 * ((γ + 1 : ℕ) : ℝ) * (δ : ℝ) ^ 2 *
                ((t + 1 : ℕ) : ℝ) ^ 3) *
                  (1 * (1 / 2 : ℝ) ^ t) := by gcongr
            _ = 126 * ((γ + 1 : ℕ) : ℝ) * (δ : ℝ) ^ 2 *
                ((((t + 1 : ℕ) : ℝ) ^ 3) / (2 : ℝ) ^ t) := by
              simp [div_eq_mul_inv, inv_pow]
              ring
    _ ≤ 126 * ((γ + 1 : ℕ) : ℝ) * (δ : ℝ) ^ 2 * 52 := by
      gcongr
      exact cubicGeometricPartial_le R
    _ ≤ 52416 * ((γ + 1 : ℕ) : ℝ) * (δ : ℝ) ^ 2 := by
      have hnon : 0 ≤ ((γ + 1 : ℕ) : ℝ) * (δ : ℝ) ^ 2 := by
        positivity
      nlinarith

end Erdos446
