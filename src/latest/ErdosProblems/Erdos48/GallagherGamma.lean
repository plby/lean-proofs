/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos48.GallagherDetectorWeight
import ErdosProblems.Erdos48.VariableRawLogFreeDensity
import ErdosProblems.Erdos48.DyadicDetectorShell
import Mathlib.Analysis.SumIntegralExpDecay

/-!
# Gamma bounds for Gallagher's cutoff energy

This file separates the terminal Abel-summation endpoint from the derivative
variation in Gallagher's smooth zero detector.  The endpoint is bounded by a
half-tilted von Mangoldt series and is exponentially small at the canonical
cutoff.  The derivative-only variation is bounded by explicit finite gamma
moments.  Algebraic normalization lemmas record the resulting cubic power of
the zero-detection width.
-/

open scoped BigOperators

noncomputable section

namespace Erdos48

/-- For integer `n ≥ 2`, shifting the logarithm by one costs at most a
factor two. -/
theorem log_natCast_succ_le_two_log {n : ℕ} (hn : 2 ≤ n) :
    Real.log (n + 1) ≤ 2 * Real.log n := by
  have hnR : (0 : ℝ) < n := by positivity
  have hsquare : (n + 1 : ℕ) ≤ n ^ 2 := by nlinarith
  calc
    Real.log (n + 1) ≤ Real.log (n ^ 2) := by
      apply Real.log_le_log (by positivity)
      exact_mod_cast hsquare
    _ = 2 * Real.log n := by
      rw [Real.log_pow]
      ring

/-- One binary shell of the logarithmic gamma sum. -/
theorem sum_detectorDyadicShell_logSucc_pow_rpow_le
    (Y N a p : ℕ) (hY : 1 ≤ Y) (eta : ℝ) (heta : 0 ≤ eta) :
    (∑ n ∈ detectorDyadicShell Y N a,
        Real.log (n + 1) ^ p * (n : ℝ) ^ (-2 * eta - 1)) ≤
      (2 : ℝ) ^ p * (((a + 1 : ℕ) : ℝ) * Real.log 2) ^ p *
        (2 ^ a : ℕ) ^ (-2 * eta) := by
  let A : ℕ := 2 ^ a
  have hA : 1 ≤ A := by
    dsimp [A]
    exact Nat.one_le_pow a 2 (by omega)
  have hcard : (detectorDyadicShell Y N a).card ≤ A := by
    apply (Finset.card_le_card (detectorDyadicShell_subset Y N a hY)).trans
    rw [Nat.card_Ioc]
    omega
  have hpoint : ∀ n ∈ detectorDyadicShell Y N a,
      Real.log (n + 1) ^ p * (n : ℝ) ^ (-2 * eta - 1) ≤
        ((2 : ℝ) ^ p *
          (((a + 1 : ℕ) : ℝ) * Real.log 2) ^ p) *
            (A : ℝ) ^ (-2 * eta - 1) := by
    intro n hn
    have hnBounds := Finset.mem_Ioc.mp
      (detectorDyadicShell_subset Y N a hY hn)
    have hnTwo : 2 ≤ n := by
      have : Y < n := (Finset.mem_Ioc.mp (Finset.mem_filter.mp hn).1).1
      omega
    have hnR : (0 : ℝ) < n := by positivity
    have hlog0 : 0 ≤ Real.log n := Real.log_natCast_nonneg n
    have hlogShell : Real.log n ≤ ((a + 1 : ℕ) : ℝ) * Real.log 2 := by
      calc
        Real.log n ≤ Real.log ((2 ^ (a + 1) : ℕ) : ℝ) := by
          apply Real.log_le_log hnR
          rw [pow_succ]
          exact_mod_cast (show n ≤ 2 ^ a * 2 by
            simpa [mul_comm] using hnBounds.2)
        _ = ((a + 1 : ℕ) : ℝ) * Real.log 2 := by
          rw [show ((2 ^ (a + 1) : ℕ) : ℝ) =
              (2 : ℝ) ^ (a + 1) by norm_cast,
            Real.log_pow]
    have hlogSucc0 : 0 ≤ Real.log (n + 1) := by
      simpa only [Nat.cast_add, Nat.cast_one] using
        Real.log_natCast_nonneg (n + 1)
    have hlogSucc :
        Real.log (n + 1) ≤
          2 * (((a + 1 : ℕ) : ℝ) * Real.log 2) :=
      (log_natCast_succ_le_two_log hnTwo).trans
        (mul_le_mul_of_nonneg_left hlogShell (by norm_num))
    have hlogPow :
        Real.log (n + 1) ^ p ≤
          (2 : ℝ) ^ p *
            (((a + 1 : ℕ) : ℝ) * Real.log 2) ^ p := by
      calc
        Real.log (n + 1) ^ p ≤
            (2 * (((a + 1 : ℕ) : ℝ) * Real.log 2)) ^ p :=
          pow_le_pow_left₀ hlogSucc0 hlogSucc p
        _ = _ := by rw [mul_pow]
    have hrpow :
        (n : ℝ) ^ (-2 * eta - 1) ≤
          (A : ℝ) ^ (-2 * eta - 1) := by
      apply Real.rpow_le_rpow_of_nonpos (by exact_mod_cast hA)
      · exact_mod_cast hnBounds.1.le
      · linarith
    exact mul_le_mul hlogPow hrpow (by positivity) (by positivity)
  calc
    (∑ n ∈ detectorDyadicShell Y N a,
        Real.log (n + 1) ^ p * (n : ℝ) ^ (-2 * eta - 1)) ≤
      ∑ _n ∈ detectorDyadicShell Y N a,
        ((2 : ℝ) ^ p *
          (((a + 1 : ℕ) : ℝ) * Real.log 2) ^ p) *
            (A : ℝ) ^ (-2 * eta - 1) :=
      Finset.sum_le_sum fun n hn ↦ hpoint n hn
    _ = ((detectorDyadicShell Y N a).card : ℝ) *
        (((2 : ℝ) ^ p *
          (((a + 1 : ℕ) : ℝ) * Real.log 2) ^ p) *
            (A : ℝ) ^ (-2 * eta - 1)) := by simp
    _ ≤ (A : ℝ) *
        (((2 : ℝ) ^ p *
          (((a + 1 : ℕ) : ℝ) * Real.log 2) ^ p) *
            (A : ℝ) ^ (-2 * eta - 1)) := by
      gcongr
    _ = (2 : ℝ) ^ p *
        (((a + 1 : ℕ) : ℝ) * Real.log 2) ^ p *
          (2 ^ a : ℕ) ^ (-2 * eta) := by
      have hApos : (0 : ℝ) < A := by positivity
      have hcombine :
          (A : ℝ) * (A : ℝ) ^ (-2 * eta - 1) =
            (A : ℝ) ^ (-2 * eta) := by
        calc
          (A : ℝ) * (A : ℝ) ^ (-2 * eta - 1) =
              (A : ℝ) ^ (1 : ℝ) *
                (A : ℝ) ^ (-2 * eta - 1) := by rw [Real.rpow_one]
          _ = (A : ℝ) ^ ((1 : ℝ) + (-2 * eta - 1)) :=
            (Real.rpow_add hApos 1 (-2 * eta - 1)).symm
          _ = (A : ℝ) ^ (-2 * eta) := by congr 1 <;> ring
      calc
        (A : ℝ) *
            (((2 : ℝ) ^ p *
              (((a + 1 : ℕ) : ℝ) * Real.log 2) ^ p) *
                (A : ℝ) ^ (-2 * eta - 1)) =
          (2 : ℝ) ^ p *
              (((a + 1 : ℕ) : ℝ) * Real.log 2) ^ p *
                ((A : ℝ) * (A : ℝ) ^ (-2 * eta - 1)) := by ring
        _ = (2 : ℝ) ^ p *
              (((a + 1 : ℕ) : ℝ) * Real.log 2) ^ p *
                (A : ℝ) ^ (-2 * eta) := by rw [hcombine]
        _ = (2 : ℝ) ^ p *
              (((a + 1 : ℕ) : ℝ) * Real.log 2) ^ p *
                (2 ^ a : ℕ) ^ (-2 * eta) := by rfl

/-- Shifted exponential power sums are bounded by the Mathlib gamma-sum
estimate; the two factors `2^c` come from shifting and from the integral
comparison itself. -/
theorem sum_range_succ_pow_mul_two_rpow_neg_le
    (p M : ℕ) {c : ℝ} (hc : 0 < c) :
    (∑ a ∈ Finset.range M,
        ((a + 1 : ℕ) : ℝ) ^ p * (2 : ℝ) ^ (-(c * a))) ≤
      (2 : ℝ) ^ (2 * c) * p.factorial /
        (Real.log 2 * c) ^ (p + 1) := by
  have hterm (a : ℕ) :
      ((a + 1 : ℕ) : ℝ) ^ p * (2 : ℝ) ^ (-(c * a)) =
        (2 : ℝ) ^ c *
          (((a + 1 : ℕ) : ℝ) ^ p *
            (2 : ℝ) ^ (-(c * (a + 1)))) := by
    have hexp :
        (2 : ℝ) ^ c * (2 : ℝ) ^ (-(c * (a + 1))) =
          (2 : ℝ) ^ (-(c * a)) := by
      rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
      congr 1
      push_cast
      ring
    rw [← hexp]
    ring
  calc
    (∑ a ∈ Finset.range M,
        ((a + 1 : ℕ) : ℝ) ^ p * (2 : ℝ) ^ (-(c * a))) =
      (2 : ℝ) ^ c *
        ∑ a ∈ Finset.range M,
          ((a + 1 : ℕ) : ℝ) ^ p *
            (2 : ℝ) ^ (-(c * (a + 1))) := by
      simp_rw [hterm]
      rw [Finset.mul_sum]
    _ = (2 : ℝ) ^ c *
        ∑ i ∈ Finset.Ico 1 (M + 1),
          (i : ℝ) ^ p * (2 : ℝ) ^ (-(c * i)) := by
      congr 1
      rw [Finset.sum_Ico_eq_sum_range]
      simp only [Nat.add_sub_cancel]
      apply Finset.sum_congr rfl
      intro a ha
      simp only [add_comm]
      push_cast
      rfl
    _ ≤ (2 : ℝ) ^ c *
        ∑ i ∈ Finset.Iic M,
          (i : ℝ) ^ p * (2 : ℝ) ^ (-(c * i)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro i hi
        rw [Finset.mem_Ico] at hi
        rw [Finset.mem_Iic]
        omega
      · intro i hi hi'
        positivity
    _ ≤ (2 : ℝ) ^ c *
        ((2 : ℝ) ^ c * p.factorial /
          (Real.log 2 * c) ^ (p + 1)) := by
      gcongr
      exact sum_Iic_pow_mul_two_pow_neg_le hc
    _ = (2 : ℝ) ^ (2 * c) * p.factorial /
        (Real.log 2 * c) ^ (p + 1) := by
      rw [show (2 : ℝ) ^ (2 * c) = (2 : ℝ) ^ c * (2 : ℝ) ^ c by
        rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
        congr 1
        ring]
      ring

/-- Dyadic summation followed by the gamma-sum estimate. -/
theorem sum_Ico_logSucc_pow_rpow_le_gamma
    (p : ℕ) {A N : ℕ} (hA : 2 ≤ A) (hAN : A ≤ N)
    {eta : ℝ} (heta : 0 < eta) :
    (∑ n ∈ Finset.Ico A N,
        Real.log (n + 1) ^ p * (n : ℝ) ^ (-2 * eta - 1)) ≤
      (2 : ℝ) ^ p * Real.log 2 ^ p *
        ((2 : ℝ) ^ (4 * eta) * p.factorial /
          (Real.log 2 * (2 * eta)) ^ (p + 1)) := by
  let Y : ℕ := A - 1
  let X : ℕ := N - 1
  let M : ℕ := Nat.log 2 (X - 1) + 1
  have hY : 1 ≤ Y := by dsimp [Y]; omega
  have hsets : Finset.Ico A N = Finset.Ioc Y X := by
    ext n
    simp only [Finset.mem_Ico, Finset.mem_Ioc]
    dsimp [Y, X]
    omega
  have hpairs :
      ((Finset.range M : Finset ℕ) : Set ℕ).PairwiseDisjoint
        (detectorDyadicShell Y X) := by
    intro a ha b hb hab
    exact disjoint_detectorDyadicShell_of_ne Y X hab
  have hterm (a : ℕ) :
      (2 : ℝ) ^ p * (((a + 1 : ℕ) : ℝ) * Real.log 2) ^ p *
          (2 ^ a : ℕ) ^ (-2 * eta) =
        ((2 : ℝ) ^ p * Real.log 2 ^ p) *
          (((a + 1 : ℕ) : ℝ) ^ p *
            (2 : ℝ) ^ (-(2 * eta * a))) := by
    have hcast : ((2 ^ a : ℕ) : ℝ) = (2 : ℝ) ^ a := by norm_cast
    have hrpow :
        ((2 ^ a : ℕ) : ℝ) ^ (-2 * eta) =
          (2 : ℝ) ^ (-(2 * eta * a)) := by
      rw [hcast, ← Real.rpow_natCast]
      rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
      congr 1
      push_cast
      ring
    rw [hrpow, mul_pow]
    ring
  rw [hsets]
  calc
    (∑ n ∈ Finset.Ioc Y X,
        Real.log (n + 1) ^ p * (n : ℝ) ^ (-2 * eta - 1)) =
      ∑ a ∈ Finset.range M,
        ∑ n ∈ detectorDyadicShell Y X a,
          Real.log (n + 1) ^ p * (n : ℝ) ^ (-2 * eta - 1) := by
      rw [← Finset.sum_biUnion hpairs]
      rw [show (Finset.range M).biUnion (detectorDyadicShell Y X) =
          Finset.Ioc Y X by
        simpa only [M] using biUnion_detectorDyadicShell Y X]
    _ ≤ ∑ a ∈ Finset.range M,
        ((2 : ℝ) ^ p * (((a + 1 : ℕ) : ℝ) * Real.log 2) ^ p *
          (2 ^ a : ℕ) ^ (-2 * eta)) := by
      apply Finset.sum_le_sum
      intro a ha
      exact sum_detectorDyadicShell_logSucc_pow_rpow_le
        Y X a p hY eta heta.le
    _ = ((2 : ℝ) ^ p * Real.log 2 ^ p) *
        ∑ a ∈ Finset.range M,
          (((a + 1 : ℕ) : ℝ) ^ p *
            (2 : ℝ) ^ (-(2 * eta * a))) := by
      simp_rw [hterm]
      rw [Finset.mul_sum]
    _ ≤ ((2 : ℝ) ^ p * Real.log 2 ^ p) *
        ((2 : ℝ) ^ (2 * (2 * eta)) * p.factorial /
          (Real.log 2 * (2 * eta)) ^ (p + 1)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact sum_range_succ_pow_mul_two_rpow_neg_le p M (by positivity)
    _ = (2 : ℝ) ^ p * Real.log 2 ^ p *
        ((2 : ℝ) ^ (4 * eta) * p.factorial /
          (Real.log 2 * (2 * eta)) ^ (p + 1)) := by
      congr 3
      ring_nf

/-- Splitting the two logarithmic derivative contributions. -/
theorem gallagherLogDerivativeMajorant_sq_le_two_moments
    (eta : ℝ) (k n : ℕ) :
    gallagherLogDerivativeMajorant eta k n ^ 2 ≤
      2 * (k : ℝ) ^ 2 * Real.log (n + 1) ^ (2 * (k - 1)) +
        2 * eta ^ 2 * Real.log (n + 1) ^ (2 * k) := by
  let L : ℝ := Real.log (n + 1)
  let a : ℝ := (k : ℝ) * L ^ (k - 1)
  let b : ℝ := eta * L ^ k
  have hab : (a + b) ^ 2 ≤ 2 * a ^ 2 + 2 * b ^ 2 := by
    nlinarith [sq_nonneg (a - b)]
  have hpowA : (L ^ (k - 1)) ^ 2 = L ^ (2 * (k - 1)) := by
    rw [← pow_mul]
    congr 1
    omega
  have hpowB : (L ^ k) ^ 2 = L ^ (2 * k) := by
    rw [← pow_mul]
    congr 1
    omega
  change (a + b) ^ 2 ≤
    2 * (k : ℝ) ^ 2 * L ^ (2 * (k - 1)) +
      2 * eta ^ 2 * L ^ (2 * k)
  calc
    (a + b) ^ 2 ≤ 2 * a ^ 2 + 2 * b ^ 2 := hab
    _ = 2 * (k : ℝ) ^ 2 * L ^ (2 * (k - 1)) +
        2 * eta ^ 2 * L ^ (2 * k) := by
      dsimp [a, b]
      rw [mul_pow, mul_pow, hpowA, hpowB]
      ring

/-- Gamma bound for the derivative part of the variation factor.  The
fixed upper-endpoint term is deliberately absent. -/
theorem sum_Ico_gallagherLogDerivativeMajorant_sq_rpow_le_gamma
    (k : ℕ) {A N : ℕ} (hA : 2 ≤ A) (hAN : A ≤ N)
    {eta : ℝ} (heta : 0 < eta) :
    (∑ n ∈ Finset.Ico A N,
        gallagherLogDerivativeMajorant eta k n ^ 2 *
          (n : ℝ) ^ (-2 * eta - 1)) ≤
      2 * (k : ℝ) ^ 2 *
        ((2 : ℝ) ^ (2 * (k - 1)) * Real.log 2 ^ (2 * (k - 1)) *
          ((2 : ℝ) ^ (4 * eta) * (2 * (k - 1)).factorial /
            (Real.log 2 * (2 * eta)) ^ (2 * (k - 1) + 1))) +
      2 * eta ^ 2 *
        ((2 : ℝ) ^ (2 * k) * Real.log 2 ^ (2 * k) *
          ((2 : ℝ) ^ (4 * eta) * (2 * k).factorial /
            (Real.log 2 * (2 * eta)) ^ (2 * k + 1))) := by
  let r : ℕ → ℝ := fun n ↦ (n : ℝ) ^ (-2 * eta - 1)
  have hr0 : ∀ n, 0 ≤ r n := fun n ↦ by dsimp [r]; positivity
  have hpoint : ∀ n,
      gallagherLogDerivativeMajorant eta k n ^ 2 * r n ≤
        (2 * (k : ℝ) ^ 2 * Real.log (n + 1) ^ (2 * (k - 1))) * r n +
        (2 * eta ^ 2 * Real.log (n + 1) ^ (2 * k)) * r n := by
    intro n
    rw [← add_mul]
    exact mul_le_mul_of_nonneg_right
      (gallagherLogDerivativeMajorant_sq_le_two_moments eta k n) (hr0 n)
  calc
    (∑ n ∈ Finset.Ico A N,
        gallagherLogDerivativeMajorant eta k n ^ 2 * r n) ≤
      ∑ n ∈ Finset.Ico A N,
        ((2 * (k : ℝ) ^ 2 * Real.log (n + 1) ^ (2 * (k - 1))) * r n +
        (2 * eta ^ 2 * Real.log (n + 1) ^ (2 * k)) * r n) := by
      exact Finset.sum_le_sum fun n hn ↦ hpoint n
    _ = 2 * (k : ℝ) ^ 2 *
          (∑ n ∈ Finset.Ico A N,
            Real.log (n + 1) ^ (2 * (k - 1)) * r n) +
        2 * eta ^ 2 *
          (∑ n ∈ Finset.Ico A N,
            Real.log (n + 1) ^ (2 * k) * r n) := by
      simp_rw [Finset.sum_add_distrib, Finset.mul_sum]
      ring_nf
    _ ≤ 2 * (k : ℝ) ^ 2 *
        ((2 : ℝ) ^ (2 * (k - 1)) * Real.log 2 ^ (2 * (k - 1)) *
          ((2 : ℝ) ^ (4 * eta) * (2 * (k - 1)).factorial /
            (Real.log 2 * (2 * eta)) ^ (2 * (k - 1) + 1))) +
      2 * eta ^ 2 *
        ((2 : ℝ) ^ (2 * k) * Real.log 2 ^ (2 * k) *
          ((2 : ℝ) ^ (4 * eta) * (2 * k).factorial /
            (Real.log 2 * (2 * eta)) ^ (2 * k + 1))) := by
      apply add_le_add
      · apply mul_le_mul_of_nonneg_left _ (by positivity)
        simpa only [r] using
          sum_Ico_logSucc_pow_rpow_le_gamma (2 * (k - 1)) hA hAN heta
      · apply mul_le_mul_of_nonneg_left _ (by positivity)
        simpa only [r] using
          sum_Ico_logSucc_pow_rpow_le_gamma (2 * k) hA hAN heta

/-- The cutoff-independent gamma majorant for the derivative-only
variation. -/
noncomputable def gallagherDerivativeGammaBound (eta : ℝ) (k : ℕ) : ℝ :=
  2 * (k : ℝ) ^ 2 *
      ((2 : ℝ) ^ (2 * (k - 1)) * Real.log 2 ^ (2 * (k - 1)) *
        ((2 : ℝ) ^ (4 * eta) * (2 * (k - 1)).factorial /
          (Real.log 2 * (2 * eta)) ^ (2 * (k - 1) + 1))) +
    2 * eta ^ 2 *
      ((2 : ℝ) ^ (2 * k) * Real.log 2 ^ (2 * k) *
        ((2 : ℝ) ^ (4 * eta) * (2 * k).factorial /
          (Real.log 2 * (2 * eta)) ^ (2 * k + 1)))

theorem sum_Ico_gallagherLogDerivativeMajorant_sq_rpow_le_gammaBound
    (k : ℕ) {A N : ℕ} (hA : 2 ≤ A) (hAN : A ≤ N)
    {eta : ℝ} (heta : 0 < eta) :
    (∑ n ∈ Finset.Ico A N,
        gallagherLogDerivativeMajorant eta k n ^ 2 *
          (n : ℝ) ^ (-2 * eta - 1)) ≤
      gallagherDerivativeGammaBound eta k := by
  simpa only [gallagherDerivativeGammaBound] using
    sum_Ico_gallagherLogDerivativeMajorant_sq_rpow_le_gamma
      k hA hAN heta

/-- Abel summation with the upper endpoint kept outside Cauchy--Schwarz.
This is the form needed when the endpoint coefficient is bounded directly,
while only the convergent derivative variation is paired with the cutoff
energy. -/
theorem norm_sum_Ioc_mul_sq_le_two_endpoint_add_two_variation
    (f w : ℕ → ℂ) {A N : ℕ} (hA : 0 < A) (hAN : A ≤ N) :
    ‖∑ n ∈ Finset.Ioc A N, f n * w n‖ ^ 2 ≤
      2 * ‖(∑ n ∈ Finset.Ioc A N, f n) * w N‖ ^ 2 +
        2 *
          ((∑ m ∈ Finset.Ico A N,
              ‖∑ n ∈ Finset.Ioc A m, f n‖ ^ 2 / (m : ℝ)) *
            ∑ m ∈ Finset.Ico A N,
              (m : ℝ) * ‖w m - w (m + 1)‖ ^ 2) := by
  let P : ℕ → ℂ := fun m ↦ ∑ n ∈ Finset.Ioc A m, f n
  let V : ℂ := ∑ m ∈ Finset.Ico A N, P m * (w m - w (m + 1))
  have hpos : ∀ m ∈ Finset.Ico A N, 0 < (m : ℝ) := by
    intro m hm
    exact_mod_cast hA.trans_le (Finset.mem_Ico.mp hm).1
  have hcauchy :
      ‖V‖ ^ 2 ≤
        (∑ m ∈ Finset.Ico A N, ‖P m‖ ^ 2 / (m : ℝ)) *
          ∑ m ∈ Finset.Ico A N,
            (m : ℝ) * ‖w m - w (m + 1)‖ ^ 2 := by
    simpa only [V] using norm_sum_mul_sq_le_weighted
      (Finset.Ico A N) (fun m ↦ (m : ℝ)) hpos P
        (fun m ↦ w m - w (m + 1))
  rw [sum_Ioc_mul_eq_prefix_mul_add_sum_prefix_mul_sub f w hAN]
  change ‖P N * w N + V‖ ^ 2 ≤ _
  have htriangle : ‖P N * w N + V‖ ≤ ‖P N * w N‖ + ‖V‖ :=
    norm_add_le _ _
  have hsquare :
      ‖P N * w N + V‖ ^ 2 ≤ (‖P N * w N‖ + ‖V‖) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) htriangle 2
  calc
    ‖P N * w N + V‖ ^ 2 ≤ (‖P N * w N‖ + ‖V‖) ^ 2 := hsquare
    _ ≤ 2 * ‖P N * w N‖ ^ 2 + 2 * ‖V‖ ^ 2 := by
      nlinarith [sq_nonneg (‖P N * w N‖ - ‖V‖)]
    _ ≤ 2 * ‖P N * w N‖ ^ 2 +
        2 *
          ((∑ m ∈ Finset.Ico A N, ‖P m‖ ^ 2 / (m : ℝ)) *
            ∑ m ∈ Finset.Ico A N,
              (m : ℝ) * ‖w m - w (m + 1)‖ ^ 2) := by gcongr

/-- The unweighted oscillatory coefficient has modulus at most `Λ(n)/n`. -/
theorem norm_gallagherBaseCoefficient_le_vonMangoldt_rpow_neg_one
    {q n : ℕ} (chi : DirichletCharacter ℂ q) (t : ℝ) :
    ‖gallagherBaseCoefficient chi t n‖ ≤
      ArithmeticFunction.vonMangoldt n * (n : ℝ) ^ (-(1 : ℝ)) := by
  have hscalar :
      0 ≤ ArithmeticFunction.vonMangoldt n * (n : ℝ) ^ (-(1 : ℝ)) := by
    positivity
  have him :
      (Complex.I * (((-t * Real.log n) : ℝ) : ℂ)).re = 0 := by
    rw [Complex.mul_re]
    simp only [Complex.I_re, Complex.I_im, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, one_mul, sub_self]
  unfold gallagherBaseCoefficient
  rw [norm_mul, norm_mul, Complex.norm_real,
    Real.norm_of_nonneg hscalar, Complex.norm_exp, him, Real.exp_zero,
    mul_one]
  exact mul_le_of_le_one_right hscalar
    (chi.norm_le_one (n : ZMod q))

/-- Tilting `Λ(n)/n` by a positive exponent converts a finite prefix into
a multiple of the convergent positive von Mangoldt series. -/
theorem norm_gallagherBaseCoefficient_le_cutoff_rpow_mul_majorant
    {q n N : ℕ} (chi : DirichletCharacter ℂ q) (t delta : ℝ)
    (hdelta : 0 ≤ delta) (hn : 0 < n) (hnN : n ≤ N) :
    ‖gallagherBaseCoefficient chi t n‖ ≤
      (N : ℝ) ^ delta * weightedVonMangoldtMajorant delta 0 n := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hNR : (0 : ℝ) < N := by exact_mod_cast hn.trans_le hnN
  have hrpow : (n : ℝ) ^ delta ≤ (N : ℝ) ^ delta := by
    exact Real.rpow_le_rpow hnR.le (by exact_mod_cast hnN) hdelta
  have hsplit :
      (n : ℝ) ^ (-(1 : ℝ)) =
        (n : ℝ) ^ delta * (n : ℝ) ^ (-(1 + delta)) := by
    calc
      (n : ℝ) ^ (-(1 : ℝ)) =
          (n : ℝ) ^ (delta + (-(1 + delta))) := by
            congr 1
            ring
      _ = (n : ℝ) ^ delta * (n : ℝ) ^ (-(1 + delta)) :=
        Real.rpow_add hnR delta (-(1 + delta))
  refine (norm_gallagherBaseCoefficient_le_vonMangoldt_rpow_neg_one
    chi t).trans ?_
  unfold weightedVonMangoldtMajorant
  simp only [pow_zero, one_mul]
  rw [hsplit]
  have hweight :
      0 ≤ ArithmeticFunction.vonMangoldt n *
        (n : ℝ) ^ (-(1 + delta)) := by positivity
  calc
    ArithmeticFunction.vonMangoldt n *
        ((n : ℝ) ^ delta * (n : ℝ) ^ (-(1 + delta))) =
      (n : ℝ) ^ delta *
        (ArithmeticFunction.vonMangoldt n *
          (n : ℝ) ^ (-(1 + delta))) := by ring
    _ ≤ (N : ℝ) ^ delta *
        (ArithmeticFunction.vonMangoldt n *
          (n : ℝ) ^ (-(1 + delta))) :=
      mul_le_mul_of_nonneg_right hrpow hweight

/-- A uniform tilted bound for every partial sum of the unweighted
Gallagher coefficients. -/
theorem norm_sum_Ioc_gallagherBaseCoefficient_le_tilted_tsum
    {q : ℕ} (chi : DirichletCharacter ℂ q) (t delta : ℝ)
    (hdelta : 0 < delta) {A N : ℕ} :
    ‖∑ n ∈ Finset.Ioc A N, gallagherBaseCoefficient chi t n‖ ≤
      (N : ℝ) ^ delta *
        ∑' n, weightedVonMangoldtMajorant delta 0 n := by
  calc
    ‖∑ n ∈ Finset.Ioc A N, gallagherBaseCoefficient chi t n‖ ≤
        ∑ n ∈ Finset.Ioc A N,
          ‖gallagherBaseCoefficient chi t n‖ := norm_sum_le _ _
    _ ≤ ∑ n ∈ Finset.Ioc A N,
        (N : ℝ) ^ delta * weightedVonMangoldtMajorant delta 0 n := by
      apply Finset.sum_le_sum
      intro n hnmem
      exact norm_gallagherBaseCoefficient_le_cutoff_rpow_mul_majorant
        chi t delta hdelta.le (by
          have := (Finset.mem_Ioc.mp hnmem).1
          omega) (Finset.mem_Ioc.mp hnmem).2
    _ = (N : ℝ) ^ delta *
        ∑ n ∈ Finset.Ioc A N,
          weightedVonMangoldtMajorant delta 0 n := by
      rw [Finset.mul_sum]
    _ ≤ (N : ℝ) ^ delta *
        ∑' n, weightedVonMangoldtMajorant delta 0 n := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact (summable_weightedVonMangoldtMajorant delta hdelta 0).sum_le_tsum
        (Finset.Ioc A N) (fun n hn ↦ by
          unfold weightedVonMangoldtMajorant
          positivity)

/-- Choosing the half-tilt `delta = eta/2` and using the Chebyshev bound
gives a fully explicit prefix estimate in the actual detector range. -/
theorem norm_sum_Ioc_gallagherBaseCoefficient_le_halfTilt
    {q : ℕ} (chi : DirichletCharacter ℂ q) (t : ℝ)
    {eta : ℝ} (heta : 0 < eta) (heta1 : eta ≤ 1) {A N : ℕ} :
    ‖∑ n ∈ Finset.Ioc A N, gallagherBaseCoefficient chi t n‖ ≤
      (N : ℝ) ^ (eta / 2) *
        (6 * (Real.log 4 + 4) / eta) := by
  have htsum := weightedVonMangoldtMajorant_tsum_le
    (eta / 2) (by positivity) (by linarith) 0
  calc
    ‖∑ n ∈ Finset.Ioc A N, gallagherBaseCoefficient chi t n‖ ≤
        (N : ℝ) ^ (eta / 2) *
          ∑' n, weightedVonMangoldtMajorant (eta / 2) 0 n :=
      norm_sum_Ioc_gallagherBaseCoefficient_le_tilted_tsum
        chi t (eta / 2) (by positivity)
    _ ≤ (N : ℝ) ^ (eta / 2) *
        (3 * (Real.log 4 + 4) * (0 : ℕ).factorial *
          (2 / (eta / 2)) ^ 0 / (eta / 2)) := by
      exact mul_le_mul_of_nonneg_left htsum (by positivity)
    _ = (N : ℝ) ^ (eta / 2) *
        (6 * (Real.log 4 + 4) / eta) := by
      simp only [Nat.factorial_zero, Nat.cast_one, pow_zero, mul_one]
      field_simp [heta.ne']
      ring

/-- Squaring the half-tilted prefix together with the terminal smooth
weight leaves the exponentially decaying factor `N^(-eta)`. -/
theorem cutoffHalfTilt_mul_gallagherWeight_sq
    (C eta : ℝ) (k : ℕ) {N : ℕ} (hN : 0 < N) :
    ((N : ℝ) ^ (eta / 2) * C * gallagherWeight eta k N) ^ 2 =
      C ^ 2 * Real.log N ^ (2 * k) * (N : ℝ) ^ (-eta) := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hhalfSq :
      ((N : ℝ) ^ (eta / 2)) ^ 2 = (N : ℝ) ^ eta := by
    calc
      ((N : ℝ) ^ (eta / 2)) ^ 2 =
          ((N : ℝ) ^ (eta / 2)) ^ (2 : ℝ) :=
        (Real.rpow_two _).symm
      _ = (N : ℝ) ^ ((eta / 2) * 2) :=
        (Real.rpow_mul hNR.le (eta / 2) 2).symm
      _ = (N : ℝ) ^ eta := by congr 1 <;> ring
  have hnegativeSq :
      ((N : ℝ) ^ (-eta)) ^ 2 = (N : ℝ) ^ (-2 * eta) := by
    calc
      ((N : ℝ) ^ (-eta)) ^ 2 =
          ((N : ℝ) ^ (-eta)) ^ (2 : ℝ) := (Real.rpow_two _).symm
      _ = (N : ℝ) ^ ((-eta) * 2) :=
        (Real.rpow_mul hNR.le (-eta) 2).symm
      _ = (N : ℝ) ^ (-2 * eta) := by congr 1 <;> ring
  have hcombine :
      (N : ℝ) ^ eta * (N : ℝ) ^ (-2 * eta) =
        (N : ℝ) ^ (-eta) := by
    rw [← Real.rpow_add hNR]
    congr 1
    ring
  have hlogSq :
      (Real.log N ^ k) ^ 2 = Real.log N ^ (2 * k) := by
    rw [← pow_mul]
    congr 1
    omega
  unfold gallagherWeight
  rw [mul_pow, mul_pow, mul_pow, hhalfSq, hlogSq, hnegativeSq]
  rw [← hcombine]
  ring

/-- The Abel endpoint admits an explicit exponentially decaying bound.
The factor `N^(-eta)` is `exp(-R)` as soon as
`N ≥ exp (R / eta)`. -/
theorem norm_gallagherAbelEndpoint_sq_le_halfTilt
    {q : ℕ} (chi : DirichletCharacter ℂ q) (t : ℝ) (k : ℕ)
    {eta : ℝ} (heta : 0 < eta) (heta1 : eta ≤ 1)
    {A N : ℕ} (hA : 0 < A) (hAN : A ≤ N) :
    ‖(∑ n ∈ Finset.Ioc A N, gallagherBaseCoefficient chi t n) *
        (gallagherWeight eta k N : ℂ)‖ ^ 2 ≤
      (6 * (Real.log 4 + 4) / eta) ^ 2 *
        Real.log N ^ (2 * k) * (N : ℝ) ^ (-eta) := by
  have hN : 0 < N := hA.trans_le hAN
  have hprefix := norm_sum_Ioc_gallagherBaseCoefficient_le_halfTilt
    chi t heta heta1 (A := A) (N := N)
  have hweight0 : 0 ≤ gallagherWeight eta k N := by
    unfold gallagherWeight
    positivity
  have hproduct :
      ‖(∑ n ∈ Finset.Ioc A N, gallagherBaseCoefficient chi t n) *
          (gallagherWeight eta k N : ℂ)‖ ≤
        (N : ℝ) ^ (eta / 2) *
          (6 * (Real.log 4 + 4) / eta) *
            gallagherWeight eta k N := by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hweight0]
    exact mul_le_mul_of_nonneg_right hprefix hweight0
  calc
    ‖(∑ n ∈ Finset.Ioc A N, gallagherBaseCoefficient chi t n) *
        (gallagherWeight eta k N : ℂ)‖ ^ 2 ≤
      ((N : ℝ) ^ (eta / 2) *
        (6 * (Real.log 4 + 4) / eta) *
          gallagherWeight eta k N) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) hproduct 2
    _ = (6 * (Real.log 4 + 4) / eta) ^ 2 *
        Real.log N ^ (2 * k) * (N : ℝ) ^ (-eta) :=
      cutoffHalfTilt_mul_gallagherWeight_sq
        (6 * (Real.log 4 + 4) / eta) eta k hN

/-- At an exponential cutoff, the residual half-tilt is exponentially
small. -/
theorem natCast_rpow_neg_eta_le_exp_neg
    {eta R : ℝ} (heta : 0 < eta) {N : ℕ}
    (hN : Real.exp (R / eta) ≤ (N : ℝ)) :
    (N : ℝ) ^ (-eta) ≤ Real.exp (-R) := by
  have hpow := Real.rpow_le_rpow_of_nonpos
    (Real.exp_pos (R / eta)) hN (by linarith : -eta ≤ 0)
  calc
    (N : ℝ) ^ (-eta) ≤ (Real.exp (R / eta)) ^ (-eta) := hpow
    _ = Real.exp (-R) := by
      rw [Real.rpow_def_of_pos (Real.exp_pos (R / eta)), Real.log_exp]
      congr 1
      field_simp [heta.ne']

/-- In particular the canonical cutoff `ceil (exp (R/eta))` contributes
at most `exp (-R)` to the endpoint power. -/
theorem zeroDetectorCutoff_rpow_neg_eta_le_exp_neg
    {eta R : ℝ} (heta : 0 < eta) :
    (zeroDetectorCutoff R eta : ℝ) ^ (-eta) ≤ Real.exp (-R) := by
  exact natCast_rpow_neg_eta_le_exp_neg heta
    (exp_div_le_zeroDetectorCutoff R eta)

/-- Algebraic core of the normalization cancellation.  A gamma moment of
degree `p`, multiplied by a detector normalization of order `j` with
`2*j = p+4`, leaves exactly three powers of `eta`. -/
theorem normalizedGammaMoment_algebra
    {eta L C D F : ℝ} (heta : eta ≠ 0) (hL : L ≠ 0) (hF : F ≠ 0)
    {j p : ℕ} (hjp : 2 * j = p + 4) :
    (((2 * eta) ^ j / F) ^ 2) *
        (C * ((2 : ℝ) ^ p * L ^ p *
          (D / (L * (2 * eta)) ^ (p + 1)))) =
      eta ^ 3 *
        (8 * C * (2 : ℝ) ^ p * D / (F ^ 2 * L)) := by
  have htwoeta : 2 * eta ≠ 0 := by positivity
  have hpowj : ((2 * eta) ^ j) ^ 2 = (2 * eta) ^ (2 * j) := by
    rw [← pow_mul]
    congr 1
    omega
  have hsplit : (2 * eta) ^ (2 * j) =
      (2 * eta) ^ (p + 1) * (2 * eta) ^ 3 := by
    rw [hjp, show p + 4 = (p + 1) + 3 by omega, pow_add]
  rw [div_pow, hpowj, hsplit, mul_pow]
  field_simp
  ring

/-- Companion cancellation for the logarithmic term already carrying the
factor `eta^2`: here a single remaining power from the normalization gives
the third power of `eta`. -/
theorem normalizedEtaSqGammaMoment_algebra
    {eta L C D F : ℝ} (heta : eta ≠ 0) (hL : L ≠ 0) (hF : F ≠ 0)
    {j p : ℕ} (hjp : 2 * j = p + 2) :
    (((2 * eta) ^ j / F) ^ 2) *
        (C * eta ^ 2 * ((2 : ℝ) ^ p * L ^ p *
          (D / (L * (2 * eta)) ^ (p + 1)))) =
      eta ^ 3 *
        (2 * C * (2 : ℝ) ^ p * D / (F ^ 2 * L)) := by
  have htwoeta : 2 * eta ≠ 0 := by positivity
  have hpowj : ((2 * eta) ^ j) ^ 2 = (2 * eta) ^ (2 * j) := by
    rw [← pow_mul]
    congr 1
    omega
  have hsplit : (2 * eta) ^ (2 * j) =
      (2 * eta) ^ (p + 1) * (2 * eta) := by
    rw [hjp, show p + 2 = (p + 1) + 1 by omega, pow_add, pow_one]
  rw [div_pow, hpowj, hsplit, mul_pow]
  field_simp
  ring

/-- The eta-independent part of the normalized derivative gamma bound.
All dependence on a small positive `eta` outside the harmless factor
`2^(4*eta)` has been extracted as `eta^3`. -/
noncomputable def normalizedGallagherDerivativeGammaCoefficient
    (eta : ℝ) (J k : ℕ) : ℝ :=
  (((578 : ℝ) ^ J / 2) ^ 2) *
    (16 * (k : ℝ) ^ 2 * (2 : ℝ) ^ (2 * (k - 1)) *
        ((2 : ℝ) ^ (4 * eta) * (2 * (k - 1)).factorial) /
          (((k.factorial : ℕ) : ℝ) ^ 2 * Real.log 2) +
      4 * (2 : ℝ) ^ (2 * k) *
        ((2 : ℝ) ^ (4 * eta) * (2 * k).factorial) /
          (((k.factorial : ℕ) : ℝ) ^ 2 * Real.log 2))

/-- After inserting the variable detector normalization, the complete
derivative Gamma bound contains exactly three powers of the zero-width
parameter.  This is the cancellation needed in Gallagher's log-free
density estimate. -/
theorem variableDetectorNormalization_sq_mul_gallagherDerivativeGammaBound
    {eta : ℝ} (heta : 0 < eta) (J j : ℕ) (hj : 2 ≤ j) :
    variableDetectorNormalization eta J j ^ 2 *
        gallagherDerivativeGammaBound eta (j - 1) =
      eta ^ 3 *
        normalizedGallagherDerivativeGammaCoefficient eta J (j - 1) := by
  have hetaNe : eta ≠ 0 := ne_of_gt heta
  have hlogTwo : Real.log 2 ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
  have hfac : (((j - 1).factorial : ℕ) : ℝ) ≠ 0 := by positivity
  have hfirst := normalizedGammaMoment_algebra
    (eta := eta) (L := Real.log 2)
    (C := 2 * ((j - 1 : ℕ) : ℝ) ^ 2)
    (D := (2 : ℝ) ^ (4 * eta) * (2 * ((j - 1) - 1)).factorial)
    (F := (((j - 1).factorial : ℕ) : ℝ))
    hetaNe hlogTwo hfac
    (j := j) (p := 2 * ((j - 1) - 1)) (by omega)
  have hsecond := normalizedEtaSqGammaMoment_algebra
    (eta := eta) (L := Real.log 2) (C := 2)
    (D := (2 : ℝ) ^ (4 * eta) * (2 * (j - 1)).factorial)
    (F := (((j - 1).factorial : ℕ) : ℝ))
    hetaNe hlogTwo hfac
    (j := j) (p := 2 * (j - 1)) (by omega)
  unfold variableDetectorNormalization gallagherDerivativeGammaBound
    normalizedGallagherDerivativeGammaCoefficient
  let G : ℝ := (578 : ℝ) ^ J / 2
  let A : ℝ := ((2 * eta) ^ j /
    (((j - 1).factorial : ℕ) : ℝ)) ^ 2
  let U : ℝ := 2 * ((j - 1 : ℕ) : ℝ) ^ 2 *
    ((2 : ℝ) ^ (2 * ((j - 1) - 1)) *
      Real.log 2 ^ (2 * ((j - 1) - 1)) *
      ((2 : ℝ) ^ (4 * eta) * (2 * ((j - 1) - 1)).factorial /
        (Real.log 2 * (2 * eta)) ^ (2 * ((j - 1) - 1) + 1)))
  let V : ℝ := 2 * eta ^ 2 *
    ((2 : ℝ) ^ (2 * (j - 1)) * Real.log 2 ^ (2 * (j - 1)) *
      ((2 : ℝ) ^ (4 * eta) * (2 * (j - 1)).factorial /
        (Real.log 2 * (2 * eta)) ^ (2 * (j - 1) + 1)))
  let U' : ℝ :=
    16 * ((j - 1 : ℕ) : ℝ) ^ 2 * (2 : ℝ) ^ (2 * ((j - 1) - 1)) *
      ((2 : ℝ) ^ (4 * eta) * (2 * ((j - 1) - 1)).factorial) /
        ((((j - 1).factorial : ℕ) : ℝ) ^ 2 * Real.log 2)
  let V' : ℝ :=
    4 * (2 : ℝ) ^ (2 * (j - 1)) *
      ((2 : ℝ) ^ (4 * eta) * (2 * (j - 1)).factorial) /
        ((((j - 1).factorial : ℕ) : ℝ) ^ 2 * Real.log 2)
  have hfirst' : A * U = eta ^ 3 * U' := by
    dsimp only [A, U, U']
    convert hfirst using 1 <;> ring
  have hsecond' : A * V = eta ^ 3 * V' := by
    dsimp only [A, V, V']
    convert hsecond using 1 <;> ring
  change (G * (2 * eta) ^ j /
      (((j - 1).factorial : ℕ) : ℝ)) ^ 2 * (U + V) =
    eta ^ 3 * (G ^ 2 * (U' + V'))
  calc
    (G * (2 * eta) ^ j /
        (((j - 1).factorial : ℕ) : ℝ)) ^ 2 * (U + V) =
        G ^ 2 * (A * U + A * V) := by dsimp [A]; ring
    _ = G ^ 2 * (eta ^ 3 * U' + eta ^ 3 * V') := by
      rw [hfirst', hsecond']
    _ = eta ^ 3 * (G ^ 2 * (U' + V')) := by ring

/-- Endpoint estimate specialized to the canonical exponential cutoff. -/
theorem norm_gallagherAbelEndpoint_zeroDetectorCutoff_sq_le
    {q : ℕ} (chi : DirichletCharacter ℂ q) (t : ℝ) (k : ℕ)
    {eta R : ℝ} (heta : 0 < eta) (heta1 : eta ≤ 1)
    {A : ℕ} (hA : 0 < A) (hAN : A ≤ zeroDetectorCutoff R eta) :
    ‖(∑ n ∈ Finset.Ioc A (zeroDetectorCutoff R eta),
          gallagherBaseCoefficient chi t n) *
        (gallagherWeight eta k (zeroDetectorCutoff R eta) : ℂ)‖ ^ 2 ≤
      (6 * (Real.log 4 + 4) / eta) ^ 2 *
        Real.log (zeroDetectorCutoff R eta) ^ (2 * k) *
          Real.exp (-R) := by
  refine (norm_gallagherAbelEndpoint_sq_le_halfTilt
    chi t k heta heta1 hA hAN).trans ?_
  gcongr
  exact zeroDetectorCutoff_rpow_neg_eta_le_exp_neg heta

/-- The variable detector after endpoint separation.  Only the derivative
variation is multiplied by the partial-sum energy, and the endpoint is the
explicit exponentially decaying term proved above. -/
theorem norm_variableBandZeroDetectorPolynomial_sq_le_separatedGamma
    {q : ℕ} (chi : DirichletCharacter ℂ q)
    (E : ℕ) {eta : ℝ} (heta : 0 < eta) (heta1 : eta ≤ 1)
    (j N : ℕ) (t : ℝ)
    (hA : 2 ≤ variableDetectorLowerCutoff E eta j)
    (hcut : variableDetectorLowerCutoff E eta j ≤ N) :
    ‖variableBandZeroDetectorPolynomial chi E eta j N t‖ ^ 2 ≤
      2 * ((6 * (Real.log 4 + 4) / eta) ^ 2 *
        Real.log N ^ (2 * (j - 1)) * (N : ℝ) ^ (-eta)) +
      2 *
        ((∑ m ∈ Finset.Ico (variableDetectorLowerCutoff E eta j) N,
            ‖∑ n ∈ Finset.Ioc (variableDetectorLowerCutoff E eta j) m,
                gallagherBaseCoefficient chi t n‖ ^ 2 / (m : ℝ)) *
          gallagherDerivativeGammaBound eta (j - 1)) := by
  let A : ℕ := variableDetectorLowerCutoff E eta j
  have hA' : 2 ≤ A := by simpa only [A] using hA
  have hApos : 0 < A := by omega
  rw [variableBandZeroDetectorPolynomial_eq_gallagherAbelSum]
  have hab := norm_sum_Ioc_mul_sq_le_two_endpoint_add_two_variation
    (fun n ↦ gallagherBaseCoefficient chi t n)
    (fun n ↦ (gallagherWeight eta (j - 1) n : ℂ)) hApos hcut
  have hendpoint := norm_gallagherAbelEndpoint_sq_le_halfTilt
    chi t (j - 1) heta heta1 hApos hcut
  have hvar :
      (∑ m ∈ Finset.Ico A N,
          (m : ℝ) *
            ‖(gallagherWeight eta (j - 1) m : ℂ) -
                (gallagherWeight eta (j - 1) (m + 1) : ℂ)‖ ^ 2) ≤
        gallagherDerivativeGammaBound eta (j - 1) := by
    calc
      (∑ m ∈ Finset.Ico A N,
          (m : ℝ) *
            ‖(gallagherWeight eta (j - 1) m : ℂ) -
                (gallagherWeight eta (j - 1) (m + 1) : ℂ)‖ ^ 2) ≤
        ∑ m ∈ Finset.Ico A N,
          (m : ℝ) * gallagherWeightSlopeMajorant eta (j - 1) m ^ 2 := by
          apply Finset.sum_le_sum
          intro m hm
          have hmpos : 0 < m := by
            have := (Finset.mem_Ico.mp hm).1
            omega
          have hstep := abs_gallagherWeight_sub_succ_le
            heta.le (j - 1) hmpos
          have hnorm :
              ‖(gallagherWeight eta (j - 1) m : ℂ) -
                  (gallagherWeight eta (j - 1) (m + 1) : ℂ)‖ =
                |gallagherWeight eta (j - 1) m -
                  gallagherWeight eta (j - 1) (m + 1)| := by
            rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
          rw [hnorm]
          gcongr
      _ = ∑ m ∈ Finset.Ico A N,
          gallagherLogDerivativeMajorant eta (j - 1) m ^ 2 *
            (m : ℝ) ^ (-2 * eta - 1) := by
          apply Finset.sum_congr rfl
          intro m hm
          exact natCast_mul_gallagherWeightSlopeMajorant_sq
            eta (j - 1) (by
              have := (Finset.mem_Ico.mp hm).1
              omega)
      _ ≤ gallagherDerivativeGammaBound eta (j - 1) :=
        sum_Ico_gallagherLogDerivativeMajorant_sq_rpow_le_gammaBound
          (j - 1) hA' hcut heta
  have henergy0 :
      0 ≤ ∑ m ∈ Finset.Ico A N,
        ‖∑ n ∈ Finset.Ioc A m, gallagherBaseCoefficient chi t n‖ ^ 2 /
          (m : ℝ) := by positivity
  refine hab.trans ?_
  apply add_le_add
  · exact mul_le_mul_of_nonneg_left hendpoint (by norm_num)
  · apply mul_le_mul_of_nonneg_left _ (by norm_num)
    exact mul_le_mul_of_nonneg_left hvar henergy0

end Erdos48
