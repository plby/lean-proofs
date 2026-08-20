/-
Copyright (c) 2026 The Formal Conjectures Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Formal Conjectures Authors
-/

import ErdosProblems.Erdos446.LowerCoefficient
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Erdős Problem 446: the central cardinality sum

Ford's order-statistics estimate leaves a numerical sum whose `k`-th term
is

`x^k (1 + |v-k|^2) / ((k+1)! (2^(k-v)+1))`,

where in the application `x = 2 log log P` and
`v = floor (log log P / log 2)`.  This file proves the uniform finite
estimate needed in the upper bound.  We state the elementary numerical
hypotheses in the robust form

`4v/3 <= x <= 3v/2` and `8 <= v`.

The signed power `2^(k-v)` is represented without any ambiguity by
`signedTwoPower k v`: it is an ordinary power above the diagonal and the
reciprocal power below it.  The proof is finite.  On the left of `v`,
successive terms are bounded by a geometric ratio `7/8`; after the signed
power is included, successive terms on the right have ratio at most `3/4`.
Exact polynomial remainders bound the two finite geometric sums by `848`
and `88`, respectively.
-/

namespace Erdos446

open Finset Real
open scoped BigOperators

/-- The positive real number denoted informally by `2^(k-v)`. -/
noncomputable def signedTwoPower (k v : ℕ) : ℝ :=
  if v ≤ k then (2 : ℝ) ^ (k - v) else ((2 : ℝ) ^ (v - k))⁻¹

theorem signedTwoPower_pos (k v : ℕ) : 0 < signedTwoPower k v := by
  rw [signedTwoPower]
  split_ifs <;> positivity

theorem signedTwoPower_eq_pow_of_le {k v : ℕ} (hvk : v ≤ k) :
    signedTwoPower k v = (2 : ℝ) ^ (k - v) := by
  simp [signedTwoPower, hvk]

theorem signedTwoPower_eq_inv_pow_of_le {k v : ℕ} (hkv : k ≤ v) :
    signedTwoPower k v = ((2 : ℝ) ^ (v - k))⁻¹ := by
  rcases hkv.eq_or_lt with rfl | hkv
  · simp [signedTwoPower]
  · simp [signedTwoPower, Nat.not_le.mpr hkv]

/-- `signedTwoPower` is exactly the usual integer power notation; the
piecewise definition merely makes subsequent order estimates convenient. -/
theorem signedTwoPower_eq_zpow (k v : ℕ) :
    signedTwoPower k v = (2 : ℝ) ^ ((k : ℤ) - (v : ℤ)) := by
  by_cases hvk : v ≤ k
  · rw [signedTwoPower_eq_pow_of_le hvk, ← zpow_natCast]
    congr 1
    exact Int.ofNat_sub hvk
  · have hkv : k < v := Nat.lt_of_not_ge hvk
    rw [signedTwoPower_eq_inv_pow_of_le hkv.le, ← zpow_natCast, ← zpow_neg]
    congr 1
    rw [Int.ofNat_sub hkv.le]
    omega

/-- The factorial part of the `k`-th central-depth summand. -/
noncomputable def fordPoissonFactor (x : ℝ) (k : ℕ) : ℝ :=
  x ^ k / ((k + 1).factorial : ℝ)

/-- The exact numerical summand occurring after Ford's order-statistics
bound.  `Nat.dist v k` is the natural-number realization of `|v-k|`. -/
noncomputable def fordCentralDepthTerm (x : ℝ) (v k : ℕ) : ℝ :=
  fordPoissonFactor x k * (1 + (Nat.dist v k : ℝ) ^ 2) /
    (signedTwoPower k v + 1)

/-- A finite-cutoff version of the central sum.  The application uses
`R = 10*v+1`, corresponding to `0 <= k <= 10v`. -/
noncomputable def fordCentralDepthSum (x : ℝ) (v R : ℕ) : ℝ :=
  ∑ k ∈ Finset.range R, fordCentralDepthTerm x v k

/-- The central comparison term from Ford's calculation. -/
noncomputable def fordCentralDepthMain (x : ℝ) (v : ℕ) : ℝ :=
  x ^ v / ((v + 1).factorial : ℝ)

theorem fordPoissonFactor_nonneg {x : ℝ} (hx : 0 ≤ x) (k : ℕ) :
    0 ≤ fordPoissonFactor x k := by
  dsimp [fordPoissonFactor]
  positivity

theorem fordCentralDepthTerm_nonneg {x : ℝ} (hx : 0 ≤ x) (v k : ℕ) :
    0 ≤ fordCentralDepthTerm x v k := by
  rw [fordCentralDepthTerm]
  exact div_nonneg
    (mul_nonneg (fordPoissonFactor_nonneg hx k) (by positivity))
    (add_nonneg (signedTwoPower_pos k v).le zero_le_one)

private theorem fordPoissonFactor_succ {x : ℝ} (hx : x ≠ 0) (k : ℕ) :
    fordPoissonFactor x (k + 1) =
      fordPoissonFactor x k * x / (k + 2 : ℕ) := by
  rw [fordPoissonFactor, fordPoissonFactor, pow_succ]
  rw [show k + 1 + 1 = (k + 1) + 1 by omega, Nat.factorial_succ]
  push_cast
  field_simp

private theorem fordPoissonFactor_le_succ_mul
    {x : ℝ} (hx : 0 < x) {v k : ℕ} (_hkv : k < v)
    (hstep : ((k + 2 : ℕ) : ℝ) ≤ (7 / 8 : ℝ) * x) :
    fordPoissonFactor x k ≤
      fordPoissonFactor x (k + 1) * (7 / 8 : ℝ) := by
  have hfac : 0 ≤ fordPoissonFactor x k :=
    fordPoissonFactor_nonneg hx.le _
  rw [fordPoissonFactor_succ hx.ne' k]
  have hkpos : (0 : ℝ) < (k + 2 : ℕ) := by positivity
  have hratio : 1 ≤ x / ((k + 2 : ℕ) : ℝ) * (7 / 8 : ℝ) := by
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ hkpos).2
    nlinarith
  calc
    fordPoissonFactor x k = fordPoissonFactor x k * 1 := by ring
    _ ≤ fordPoissonFactor x k *
        (x / ((k + 2 : ℕ) : ℝ) * (7 / 8 : ℝ)) :=
      mul_le_mul_of_nonneg_left hratio hfac
    _ = fordPoissonFactor x k * x / ((k + 2 : ℕ) : ℝ) *
        (7 / 8 : ℝ) := by ring

/-- To the left of the central depth, the unweighted factorial factors
decay geometrically. -/
theorem fordPoissonFactor_left_decay
    {x : ℝ} {v k : ℕ} (hv : 8 ≤ v) (hkv : k ≤ v)
    (hx : (4 / 3 : ℝ) * (v : ℝ) ≤ x) :
    fordPoissonFactor x k ≤
      fordCentralDepthMain x v * (7 / 8 : ℝ) ^ (v - k) := by
  have hxpos : 0 < x := lt_of_lt_of_le (by positivity :
    0 < (4 / 3 : ℝ) * (v : ℝ)) hx
  have hglobal : ((v + 1 : ℕ) : ℝ) ≤ (7 / 8 : ℝ) * x := by
    have hvR : (8 : ℝ) ≤ v := by exact_mod_cast hv
    calc
      ((v + 1 : ℕ) : ℝ) ≤ (7 / 6 : ℝ) * (v : ℝ) := by
        push_cast
        linarith
      _ ≤ (7 / 8 : ℝ) * x := by nlinarith
  have hiter : ∀ n : ℕ, k ≤ n → n ≤ v →
      fordPoissonFactor x k ≤
        fordPoissonFactor x n * (7 / 8 : ℝ) ^ (n - k) := by
    intro n hkn hnv
    induction n, hkn using Nat.le_induction with
    | base => simp
    | succ n hkn ih =>
        have hnv' : n < v := by omega
        have hstep : ((n + 2 : ℕ) : ℝ) ≤ (7 / 8 : ℝ) * x := by
          calc
            ((n + 2 : ℕ) : ℝ) ≤ ((v + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega)
            _ ≤ (7 / 8 : ℝ) * x := hglobal
        have hratio := fordPoissonFactor_le_succ_mul hxpos hnv' hstep
        have hpow : n + 1 - k = (n - k) + 1 := by omega
        rw [hpow, pow_succ]
        calc
          fordPoissonFactor x k ≤
              fordPoissonFactor x n * (7 / 8 : ℝ) ^ (n - k) := ih (by omega)
          _ ≤ (fordPoissonFactor x (n + 1) * (7 / 8 : ℝ)) *
                (7 / 8 : ℝ) ^ (n - k) := by
            exact mul_le_mul_of_nonneg_right hratio (by positivity)
          _ = fordPoissonFactor x (n + 1) *
                ((7 / 8 : ℝ) ^ (n - k) * (7 / 8 : ℝ)) := by ring
  simpa [fordCentralDepthMain, fordPoissonFactor] using hiter v hkv le_rfl

private theorem discountedPoisson_succ
    {x : ℝ} (hx : x ≠ 0) (v d : ℕ) :
    fordPoissonFactor x (v + (d + 1)) / (2 : ℝ) ^ (d + 1) =
      (fordPoissonFactor x (v + d) / (2 : ℝ) ^ d) *
        (x / (2 * ((v + d + 2 : ℕ) : ℝ))) := by
  rw [show v + (d + 1) = (v + d) + 1 by omega,
    fordPoissonFactor_succ hx, pow_succ]
  field_simp

/-- Above the central depth, inclusion of `2^(k-v)` makes the factorial
factor decay geometrically. -/
theorem fordPoissonFactor_right_decay
    {x : ℝ} {v d : ℕ} (hx0 : 0 ≤ x)
    (hx : x ≤ (3 / 2 : ℝ) * (v : ℝ)) :
    fordPoissonFactor x (v + d) / (2 : ℝ) ^ d ≤
      fordCentralDepthMain x v * (3 / 4 : ℝ) ^ d := by
  by_cases hxzero : x = 0
  · subst x
    cases v with
    | zero =>
        cases d with
        | zero => simp [fordPoissonFactor, fordCentralDepthMain]
        | succ d =>
            simp [fordPoissonFactor, fordCentralDepthMain]
            exact pow_nonneg (by norm_num) _
    | succ v => simp [fordPoissonFactor, fordCentralDepthMain]
  have hxpos : 0 < x := lt_of_le_of_ne hx0 (Ne.symm hxzero)
  have hratio (d : ℕ) :
      x / (2 * ((v + d + 2 : ℕ) : ℝ)) ≤ (3 / 4 : ℝ) := by
    have hvnonneg : (0 : ℝ) ≤ v := by positivity
    have hden : (0 : ℝ) < 2 * ((v + d + 2 : ℕ) : ℝ) := by positivity
    apply (div_le_iff₀ hden).2
    have : (v : ℝ) ≤ ((v + d + 2 : ℕ) : ℝ) := by exact_mod_cast (by omega)
    nlinarith
  induction d with
  | zero => simp [fordCentralDepthMain, fordPoissonFactor]
  | succ d ih =>
      rw [discountedPoisson_succ hxzero v d, pow_succ]
      have hnonneg : 0 ≤ fordPoissonFactor x (v + d) / (2 : ℝ) ^ d := by
        exact div_nonneg (fordPoissonFactor_nonneg hx0 _) (by positivity)
      calc
        (fordPoissonFactor x (v + d) / (2 : ℝ) ^ d) *
            (x / (2 * ((v + d + 2 : ℕ) : ℝ))) ≤
          (fordPoissonFactor x (v + d) / (2 : ℝ) ^ d) * (3 / 4 : ℝ) :=
            mul_le_mul_of_nonneg_left (hratio d) hnonneg
        _ ≤ (fordCentralDepthMain x v * (3 / 4 : ℝ) ^ d) *
              (3 / 4 : ℝ) := by
            exact mul_le_mul_of_nonneg_right ih (by norm_num)
        _ = fordCentralDepthMain x v *
              ((3 / 4 : ℝ) ^ d * (3 / 4 : ℝ)) := by ring

/-- The polynomially weighted geometric partial sum with ratio `q`. -/
noncomputable def quadraticGeometricPartial (q : ℝ) (R : ℕ) : ℝ :=
  ∑ d ∈ Finset.range R, (1 + (d : ℝ) ^ 2) * q ^ d

private noncomputable def sevenEighthsRemainder (R : ℕ) : ℝ :=
  (7 / 8 : ℝ) ^ R *
    (8 * (R : ℝ) ^ 2 + 112 * (R : ℝ) + 848)

private theorem sevenEighthsRemainder_step (R : ℕ) :
    sevenEighthsRemainder R =
      (1 + (R : ℝ) ^ 2) * (7 / 8 : ℝ) ^ R +
        sevenEighthsRemainder (R + 1) := by
  rw [sevenEighthsRemainder, sevenEighthsRemainder, pow_succ]
  push_cast
  ring

theorem quadraticGeometricPartial_sevenEighths_le (R : ℕ) :
    quadraticGeometricPartial (7 / 8 : ℝ) R ≤ 848 := by
  have hid : quadraticGeometricPartial (7 / 8 : ℝ) R +
      sevenEighthsRemainder R = 848 := by
    induction R with
    | zero => norm_num [quadraticGeometricPartial, sevenEighthsRemainder]
    | succ R ih =>
        rw [quadraticGeometricPartial, Finset.sum_range_succ]
        change quadraticGeometricPartial (7 / 8 : ℝ) R +
            (1 + (R : ℝ) ^ 2) * (7 / 8 : ℝ) ^ R +
              sevenEighthsRemainder (R + 1) = 848
        calc
          quadraticGeometricPartial (7 / 8 : ℝ) R +
              (1 + (R : ℝ) ^ 2) * (7 / 8 : ℝ) ^ R +
                sevenEighthsRemainder (R + 1) =
            quadraticGeometricPartial (7 / 8 : ℝ) R +
              ((1 + (R : ℝ) ^ 2) * (7 / 8 : ℝ) ^ R +
                sevenEighthsRemainder (R + 1)) := by ring
          _ = quadraticGeometricPartial (7 / 8 : ℝ) R +
              sevenEighthsRemainder R := by rw [← sevenEighthsRemainder_step]
          _ = 848 := ih
  have hrem : 0 ≤ sevenEighthsRemainder R := by
    dsimp [sevenEighthsRemainder]
    positivity
  linarith

private noncomputable def threeFourthsRemainder (R : ℕ) : ℝ :=
  (3 / 4 : ℝ) ^ R *
    (4 * (R : ℝ) ^ 2 + 24 * (R : ℝ) + 88)

private theorem threeFourthsRemainder_step (R : ℕ) :
    threeFourthsRemainder R =
      (1 + (R : ℝ) ^ 2) * (3 / 4 : ℝ) ^ R +
        threeFourthsRemainder (R + 1) := by
  rw [threeFourthsRemainder, threeFourthsRemainder, pow_succ]
  push_cast
  ring

theorem quadraticGeometricPartial_threeFourths_le (R : ℕ) :
    quadraticGeometricPartial (3 / 4 : ℝ) R ≤ 88 := by
  have hid : quadraticGeometricPartial (3 / 4 : ℝ) R +
      threeFourthsRemainder R = 88 := by
    induction R with
    | zero => norm_num [quadraticGeometricPartial, threeFourthsRemainder]
    | succ R ih =>
        rw [quadraticGeometricPartial, Finset.sum_range_succ]
        change quadraticGeometricPartial (3 / 4 : ℝ) R +
            (1 + (R : ℝ) ^ 2) * (3 / 4 : ℝ) ^ R +
              threeFourthsRemainder (R + 1) = 88
        calc
          quadraticGeometricPartial (3 / 4 : ℝ) R +
              (1 + (R : ℝ) ^ 2) * (3 / 4 : ℝ) ^ R +
                threeFourthsRemainder (R + 1) =
            quadraticGeometricPartial (3 / 4 : ℝ) R +
              ((1 + (R : ℝ) ^ 2) * (3 / 4 : ℝ) ^ R +
                threeFourthsRemainder (R + 1)) := by ring
          _ = quadraticGeometricPartial (3 / 4 : ℝ) R +
              threeFourthsRemainder R := by rw [← threeFourthsRemainder_step]
          _ = 88 := ih
  have hrem : 0 ≤ threeFourthsRemainder R := by
    dsimp [threeFourthsRemainder]
    positivity
  linarith

/-- Pointwise estimate on the left half of the central sum. -/
theorem fordCentralDepthTerm_left_le
    {x : ℝ} {v k : ℕ} (hv : 8 ≤ v) (hkv : k ≤ v)
    (hx : (4 / 3 : ℝ) * (v : ℝ) ≤ x) :
    fordCentralDepthTerm x v k ≤
      fordCentralDepthMain x v *
        ((1 + ((v - k : ℕ) : ℝ) ^ 2) * (7 / 8 : ℝ) ^ (v - k)) := by
  have hx0 : 0 ≤ x := (lt_of_lt_of_le (by positivity :
    0 < (4 / 3 : ℝ) * (v : ℝ)) hx).le
  have hdecay := fordPoissonFactor_left_decay hv hkv hx
  have hdist : Nat.dist v k = v - k := by
    rw [Nat.dist_comm, Nat.dist_eq_sub_of_le hkv]
  have hden : 1 ≤ signedTwoPower k v + 1 := by
    have hp := (signedTwoPower_pos k v).le
    linarith
  have hnum : 0 ≤ fordPoissonFactor x k *
      (1 + (Nat.dist v k : ℝ) ^ 2) :=
    mul_nonneg (fordPoissonFactor_nonneg hx0 _) (by positivity)
  calc
    fordCentralDepthTerm x v k ≤
        fordPoissonFactor x k * (1 + (Nat.dist v k : ℝ) ^ 2) := by
      rw [fordCentralDepthTerm]
      exact (div_le_iff₀ (lt_of_lt_of_le zero_lt_one hden)).2 (by
        nlinarith)
    _ ≤ (fordCentralDepthMain x v * (7 / 8 : ℝ) ^ (v - k)) *
          (1 + (Nat.dist v k : ℝ) ^ 2) := by
      exact mul_le_mul_of_nonneg_right hdecay (by positivity)
    _ = fordCentralDepthMain x v *
          ((1 + ((v - k : ℕ) : ℝ) ^ 2) * (7 / 8 : ℝ) ^ (v - k)) := by
      rw [hdist]
      ring

/-- Pointwise estimate on the right half of the central sum. -/
theorem fordCentralDepthTerm_right_le
    {x : ℝ} {v k : ℕ} (hvk : v ≤ k) (hx0 : 0 ≤ x)
    (hx : x ≤ (3 / 2 : ℝ) * (v : ℝ)) :
    fordCentralDepthTerm x v k ≤
      fordCentralDepthMain x v *
        ((1 + ((k - v : ℕ) : ℝ) ^ 2) * (3 / 4 : ℝ) ^ (k - v)) := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hvk
  simp only [Nat.add_sub_cancel_left]
  have hpow : signedTwoPower (v + d) v = (2 : ℝ) ^ d := by
    rw [signedTwoPower_eq_pow_of_le (by omega)]
    congr 1
    omega
  have hdist : Nat.dist v (v + d) = d := by
    rw [Nat.dist_eq_sub_of_le (by omega)]
    omega
  have hdecay := fordPoissonFactor_right_decay (v := v) (d := d) hx0 hx
  have hpowpos : (0 : ℝ) < (2 : ℝ) ^ d := by positivity
  have hden : (2 : ℝ) ^ d ≤ signedTwoPower (v + d) v + 1 := by
    rw [hpow]
    linarith
  calc
    fordCentralDepthTerm x v (v + d) ≤
        fordPoissonFactor x (v + d) * (1 + (d : ℝ) ^ 2) /
          (2 : ℝ) ^ d := by
      rw [fordCentralDepthTerm, hdist]
      exact div_le_div_of_nonneg_left
        (mul_nonneg (fordPoissonFactor_nonneg hx0 _) (by positivity)) hpowpos hden
    _ = (fordPoissonFactor x (v + d) / (2 : ℝ) ^ d) *
          (1 + (d : ℝ) ^ 2) := by ring
    _ ≤ (fordCentralDepthMain x v * (3 / 4 : ℝ) ^ d) *
          (1 + (d : ℝ) ^ 2) := by
      exact mul_le_mul_of_nonneg_right hdecay (by positivity)
    _ = fordCentralDepthMain x v *
          ((1 + (d : ℝ) ^ 2) * (3 / 4 : ℝ) ^ d) := by ring

/-- Ford's complete finite central-depth sum.  The numerical constant is
absolute and the cutoff is the exact range `0 <= k <= 10v`. -/
theorem fordCentralDepthSum_ten_mul_le
    {x : ℝ} {v : ℕ} (hv : 8 ≤ v)
    (hx0 : (4 / 3 : ℝ) * (v : ℝ) ≤ x)
    (hx1 : x ≤ (3 / 2 : ℝ) * (v : ℝ)) :
    fordCentralDepthSum x v (10 * v + 1) ≤
      936 * fordCentralDepthMain x v := by
  have hxnonneg : 0 ≤ x := (lt_of_lt_of_le (by positivity :
    0 < (4 / 3 : ℝ) * (v : ℝ)) hx0).le
  have hsplit : 10 * v + 1 = (v + 1) + 9 * v := by omega
  rw [fordCentralDepthSum, hsplit, Finset.sum_range_add]
  have hleft :
      (∑ k ∈ Finset.range (v + 1), fordCentralDepthTerm x v k) ≤
        fordCentralDepthMain x v * 848 := by
    calc
      (∑ k ∈ Finset.range (v + 1), fordCentralDepthTerm x v k) ≤
          ∑ k ∈ Finset.range (v + 1),
            fordCentralDepthMain x v *
              ((1 + ((v - k : ℕ) : ℝ) ^ 2) *
                (7 / 8 : ℝ) ^ (v - k)) := by
        apply Finset.sum_le_sum
        intro k hk
        exact fordCentralDepthTerm_left_le hv
          (Nat.le_of_lt_succ (Finset.mem_range.mp hk)) hx0
      _ = fordCentralDepthMain x v *
          quadraticGeometricPartial (7 / 8 : ℝ) (v + 1) := by
        rw [quadraticGeometricPartial, ← Finset.mul_sum,
          ← Finset.sum_range_reflect]
        congr 1
        apply Finset.sum_congr rfl
        intro k hk
        have hk' : k < v + 1 := Finset.mem_range.mp hk
        have hkv : k ≤ v := Nat.le_of_lt_succ hk'
        have hinner : v + 1 - 1 - k = v - k := by omega
        have hreflect : v - (v - k) = k := by omega
        rw [hinner, hreflect]
      _ ≤ fordCentralDepthMain x v * 848 := by
        exact mul_le_mul_of_nonneg_left
          (quadraticGeometricPartial_sevenEighths_le (v + 1)) (by
            dsimp [fordCentralDepthMain]
            positivity)
  have hright :
      (∑ k ∈ Finset.range (9 * v),
          fordCentralDepthTerm x v (v + 1 + k)) ≤
        fordCentralDepthMain x v * 88 := by
    calc
      (∑ k ∈ Finset.range (9 * v),
          fordCentralDepthTerm x v (v + 1 + k)) ≤
        ∑ k ∈ Finset.range (9 * v),
          fordCentralDepthMain x v *
            ((1 + ((k + 1 : ℕ) : ℝ) ^ 2) *
              (3 / 4 : ℝ) ^ (k + 1)) := by
        apply Finset.sum_le_sum
        intro k hk
        simpa only [Nat.add_sub_cancel_left, Nat.add_comm, Nat.add_left_comm,
          Nat.add_assoc] using
          (fordCentralDepthTerm_right_le
            (x := x) (v := v) (k := v + 1 + k) (by omega) hxnonneg hx1)
      _ ≤ fordCentralDepthMain x v *
          quadraticGeometricPartial (3 / 4 : ℝ) (9 * v + 1) := by
        have hmain : 0 ≤ fordCentralDepthMain x v := by
          dsimp [fordCentralDepthMain]
          positivity
        rw [quadraticGeometricPartial, ← Finset.mul_sum]
        apply mul_le_mul_of_nonneg_left _ hmain
        rw [Finset.sum_range_succ']
        apply le_add_of_nonneg_right
        norm_num
      _ ≤ fordCentralDepthMain x v * 88 := by
        exact mul_le_mul_of_nonneg_left
          (quadraticGeometricPartial_threeFourths_le (9 * v + 1)) (by
            dsimp [fordCentralDepthMain]
            positivity)
  calc
    (∑ x_1 ∈ Finset.range (v + 1), fordCentralDepthTerm x v x_1) +
        ∑ x_1 ∈ Finset.range (9 * v),
          fordCentralDepthTerm x v (v + 1 + x_1) ≤
      fordCentralDepthMain x v * 848 + fordCentralDepthMain x v * 88 :=
        add_le_add hleft hright
    _ = 936 * fordCentralDepthMain x v := by ring

/-- The comparison term is exactly the lower-bound combinatorial weight
when `x = 2 log 2 * v`, up to the explicit factor `v/(v+1)`.  This is the
algebraic bridge used by the upper-bound assembly. -/
theorem fordCentralDepthMain_two_log_two_mul {v : ℕ} (hv : 0 < v) :
    fordCentralDepthMain ((2 * Real.log 2) * (v : ℝ)) v =
      fordCombinatorialWeight v * (v : ℝ) / (v + 1 : ℕ) := by
  rw [fordCentralDepthMain, fordCombinatorialWeight, Nat.factorial_succ]
  push_cast
  rw [mul_pow]
  have hvR : (v : ℝ) ≠ 0 := by exact_mod_cast hv.ne'
  rw [pow_sub₀ (v : ℝ) hvR (by omega : 1 ≤ v), pow_one]
  field_simp

/-- Moving the analytic parameter from `2 log 2 * v` to the upper endpoint
`2 log 2 * (v+1)` costs exactly the classical Euler factor
`(1+1/v)^(v-1)`. -/
theorem fordCentralDepthMain_two_log_two_succ_eq
    {v : ℕ} (hv : 0 < v) :
    fordCentralDepthMain ((2 * Real.log 2) * ((v + 1 : ℕ) : ℝ)) v =
      fordCombinatorialWeight v *
        (1 + ((v : ℝ)⁻¹)) ^ (v - 1) := by
  rw [fordCentralDepthMain, fordCombinatorialWeight, Nat.factorial_succ]
  push_cast
  rw [mul_pow]
  have hvR : (v : ℝ) ≠ 0 := by exact_mod_cast hv.ne'
  have hv1R : (v : ℝ) + 1 ≠ 0 := by positivity
  have hpow : ((v : ℝ) + 1) ^ v =
      ((v : ℝ) + 1) ^ (v - 1) * ((v : ℝ) + 1) := by
    calc
      ((v : ℝ) + 1) ^ v = ((v : ℝ) + 1) ^ ((v - 1) + 1) := by
        congr 1
        omega
      _ = ((v : ℝ) + 1) ^ (v - 1) * ((v : ℝ) + 1) := by
        rw [pow_succ]
  rw [show 1 + ((v : ℝ)⁻¹) = ((v : ℝ) + 1) / v by field_simp]
  rw [div_pow, pow_sub₀ (v : ℝ) hvR (by omega : 1 ≤ v), pow_one, hpow]
  field_simp

/-- If `x` lies below the exact upper endpoint supplied by the floor
relation defining `v`, then the central term is at most three times Ford's
combinatorial weight. -/
theorem fordCentralDepthMain_le_three_weight
    {x : ℝ} {v : ℕ} (hv : 0 < v) (hx0 : 0 ≤ x)
    (hx : x ≤ (2 * Real.log 2) * ((v + 1 : ℕ) : ℝ)) :
    fordCentralDepthMain x v ≤ 3 * fordCombinatorialWeight v := by
  have hendpoint0 : 0 ≤ (2 * Real.log 2) * ((v + 1 : ℕ) : ℝ) := by
    positivity
  have hmain : fordCentralDepthMain x v ≤
      fordCentralDepthMain ((2 * Real.log 2) * ((v + 1 : ℕ) : ℝ)) v := by
    rw [fordCentralDepthMain, fordCentralDepthMain]
    exact div_le_div_of_nonneg_right
      (pow_le_pow_left₀ hx0 hx v) (by positivity)
  have hpow : (1 + ((v : ℝ)⁻¹)) ^ (v - 1) ≤ Real.exp 1 := by
    calc
      (1 + ((v : ℝ)⁻¹)) ^ (v - 1) ≤
          (1 + ((v : ℝ)⁻¹)) ^ v := by
        apply pow_le_pow_right₀
        · have hinv : 0 ≤ ((v : ℝ)⁻¹) := by positivity
          linarith
        · omega
      _ ≤ Real.exp 1 := Real.one_add_inv_pow_le_exp
  have hpowThree : (1 + ((v : ℝ)⁻¹)) ^ (v - 1) ≤ 3 :=
    hpow.trans Real.exp_one_lt_three.le
  have hw : 0 ≤ fordCombinatorialWeight v := by
    dsimp [fordCombinatorialWeight]
    positivity
  calc
    fordCentralDepthMain x v ≤
        fordCentralDepthMain ((2 * Real.log 2) * ((v + 1 : ℕ) : ℝ)) v := hmain
    _ = fordCombinatorialWeight v *
          (1 + ((v : ℝ)⁻¹)) ^ (v - 1) :=
      fordCentralDepthMain_two_log_two_succ_eq hv
    _ ≤ fordCombinatorialWeight v * 3 :=
      mul_le_mul_of_nonneg_left hpowThree hw
    _ = 3 * fordCombinatorialWeight v := by ring

/-- Fully combined central-sum estimate in the form consumed by the Ford
upper bound.  The hypotheses `hx0` and `hx2` are the exact real inequalities
obtained from `v = floor (log log P / log 2)`; `hx1` is the coarse central
range inequality used only for geometric decay. -/
theorem fordCentralDepthSum_le_weight
    {x : ℝ} {v : ℕ} (hv : 8 ≤ v)
    (hx0 : (4 / 3 : ℝ) * (v : ℝ) ≤ x)
    (hx1 : x ≤ (3 / 2 : ℝ) * (v : ℝ))
    (hx2 : x ≤ (2 * Real.log 2) * ((v + 1 : ℕ) : ℝ)) :
    fordCentralDepthSum x v (10 * v + 1) ≤
      2808 * fordCombinatorialWeight v := by
  have hvpos : 0 < v := lt_of_lt_of_le (by omega : 0 < 8) hv
  have hxnonneg : 0 ≤ x := (lt_of_lt_of_le (by positivity :
    0 < (4 / 3 : ℝ) * (v : ℝ)) hx0).le
  have hsum := fordCentralDepthSum_ten_mul_le hv hx0 hx1
  have hmain := fordCentralDepthMain_le_three_weight hvpos hxnonneg hx2
  calc
    fordCentralDepthSum x v (10 * v + 1) ≤
        936 * fordCentralDepthMain x v := hsum
    _ ≤ 936 * (3 * fordCombinatorialWeight v) :=
      mul_le_mul_of_nonneg_left hmain (by norm_num)
    _ = 2808 * fordCombinatorialWeight v := by ring

/-- Consequently the full central sum at the canonical center is controlled
directly by `fordCombinatorialWeight`. -/
theorem fordCentralDepthSum_two_log_two_mul_le
    {v : ℕ} (hv : 8 ≤ v)
    (hlogLower : (2 / 3 : ℝ) ≤ Real.log 2)
    (hlogUpper : Real.log 2 ≤ (3 / 4 : ℝ)) :
    fordCentralDepthSum ((2 * Real.log 2) * (v : ℝ)) v (10 * v + 1) ≤
      936 * fordCombinatorialWeight v := by
  have hmain := fordCentralDepthSum_ten_mul_le hv
    (x := (2 * Real.log 2) * (v : ℝ))
    (by nlinarith [show (0 : ℝ) ≤ v by positivity])
    (by nlinarith [show (0 : ℝ) ≤ v by positivity])
  have hvNat : 0 < v := lt_of_lt_of_le (by omega : 0 < 8) hv
  rw [fordCentralDepthMain_two_log_two_mul hvNat] at hmain
  have hvpos : (0 : ℝ) < v := by exact_mod_cast hvNat
  have hratio : (v : ℝ) / (v + 1 : ℕ) ≤ 1 := by
    apply (div_le_one (by positivity : (0 : ℝ) < (v + 1 : ℕ))).2
    push_cast
    linarith
  have hw : 0 ≤ fordCombinatorialWeight v := by
    dsimp [fordCombinatorialWeight]
    positivity
  calc
    fordCentralDepthSum ((2 * Real.log 2) * (v : ℝ)) v (10 * v + 1) ≤
        936 * (fordCombinatorialWeight v * (v : ℝ) / (v + 1 : ℕ)) := hmain
    _ ≤ 936 * fordCombinatorialWeight v := by
      calc
        936 * (fordCombinatorialWeight v * (v : ℝ) / (v + 1 : ℕ)) =
            936 * (fordCombinatorialWeight v *
              ((v : ℝ) / (v + 1 : ℕ))) := by ring
        _ ≤ 936 * (fordCombinatorialWeight v * 1) := by
          gcongr
        _ = 936 * fordCombinatorialWeight v := by ring

end Erdos446
