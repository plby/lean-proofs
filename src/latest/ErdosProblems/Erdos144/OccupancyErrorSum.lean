/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ErdosProblems.Erdos144.ScaleLimits
import ErdosProblems.Erdos144.StrongMertens

/-!
# Summing the logarithmic-block occupancy errors

This file is the elementary summation layer between the quantitative prime
estimate and the finite CRT transfer in the proof of Erdős Problem 144.  The
analytic input is deliberately exposed as an eventual pointwise bound.  The
four terms in that bound are disposed of respectively by the harmonic-mass
estimate, the reciprocal-square tail estimate, the twenty-fifth-power scale
separation, and the same reciprocal-square tail estimate once more.
-/

open Filter Topology Finset

namespace Erdos144.OccupancyErrorSum

open Erdos144.Harmonic
open Erdos144.PrimeBlocks

noncomputable section

/-- The majorant produced by the strong theta estimate and the quadratic
Bonferroni correction.  The first summand is written as `(1 / i) / K`, which
is algebraically identical to `1 / (K * i)` and makes its sum exactly the
harmonic interval mass divided by the mesh. -/
def occupancyErrorMajorant (A : ℝ) (K i : ℕ) : ℝ :=
  ((1 : ℝ) / i) / K + 1 / ((i : ℝ) * (i + 1)) +
    A * (((K : ℝ) / i) ^ 25) + 8 / (i : ℝ) ^ 2

/-- The displayed majorant agrees with the denominator arrangement emitted
by the analytic mass estimate. -/
lemma occupancyErrorMajorant_eq (A : ℝ) (K i : ℕ) :
    occupancyErrorMajorant A K i =
      1 / ((K : ℝ) * i) + 1 / ((i : ℝ) * (i + 1)) +
        A * (((K : ℝ) / i) ^ 25) + 8 / (i : ℝ) ^ 2 := by
  unfold occupancyErrorMajorant
  simp only [one_div, mul_inv]
  ring

/-- The reciprocal-square tail on a finite interval is bounded by the
reciprocal of its left endpoint. -/
lemma sum_Ioc_one_div_sq_le {C N : ℕ} (hC : 0 < C) (hCN : C ≤ N) :
    (∑ i ∈ Ioc C N, (1 : ℝ) / (i : ℝ) ^ 2) ≤ 1 / (C : ℝ) := by
  calc
    (∑ i ∈ Ioc C N, (1 : ℝ) / (i : ℝ) ^ 2) =
        ∑ i ∈ Ioc C N, ((i : ℝ) ^ 2)⁻¹ := by
      simp only [one_div]
    _ ≤ (C : ℝ)⁻¹ - (N : ℝ)⁻¹ :=
      sum_Ioc_inv_sq_le_sub hC.ne' hCN
    _ ≤ (C : ℝ)⁻¹ := sub_le_self _ (by positivity)
    _ = 1 / (C : ℝ) := by rw [one_div]

/-- A single reciprocal-product term is bounded by the corresponding
reciprocal square. -/
lemma one_div_mul_succ_le_one_div_sq {i : ℕ} (hi : 0 < i) :
    (1 : ℝ) / ((i : ℝ) * (i + 1)) ≤ 1 / (i : ℝ) ^ 2 := by
  apply one_div_le_one_div_of_le (by positivity)
  nlinarith

/-- The explicit reservoir really is an interval in the stated order. -/
lemma lowerScale_le_finalTop (s : ℕ) : lowerScale s ≤ finalTop s := by
  rw [lowerScale, finalTop, stageTop]
  apply Nat.pow_le_pow_right (by norm_num)
  omega

/-- Finite summation of the pointwise majorant.  This is the only place where
the length of the reservoir is used; its cardinality is bounded by `N`. -/
theorem sum_occupancyErrorMajorant_le {A : ℝ} (hA : 0 ≤ A)
    {C N K : ℕ} (hC : 0 < C) (hCN : C ≤ N) :
    (∑ i ∈ Ioc C N, occupancyErrorMajorant A K i) ≤
      (∑ i ∈ Ioc C N, (1 : ℝ) / i) / K +
        A * (N : ℝ) * (((K : ℝ) / C) ^ 25) + 9 / (C : ℝ) := by
  have hpoint : ∀ i ∈ Ioc C N,
      occupancyErrorMajorant A K i ≤
        ((1 : ℝ) / i) / K +
          A * (((K : ℝ) / C) ^ 25) + 9 * ((1 : ℝ) / (i : ℝ) ^ 2) := by
    intro i hi
    have hiC : C < i := (mem_Ioc.mp hi).1
    have hi0 : 0 < i := hC.trans hiC
    have hratio : (K : ℝ) / i ≤ (K : ℝ) / C := by
      apply div_le_div_of_nonneg_left (by positivity) (by positivity)
      exact_mod_cast hiC.le
    have hpow : ((K : ℝ) / i) ^ 25 ≤ ((K : ℝ) / C) ^ 25 := by
      exact pow_le_pow_left₀ (by positivity) hratio 25
    have hprod := one_div_mul_succ_le_one_div_sq hi0
    unfold occupancyErrorMajorant
    have hApow := mul_le_mul_of_nonneg_left hpow hA
    have hEight : 8 / (i : ℝ) ^ 2 =
        8 * ((1 : ℝ) / (i : ℝ) ^ 2) := by ring
    rw [hEight]
    linarith
  have hfirst :
      (∑ i ∈ Ioc C N, ((1 : ℝ) / i) / K) =
        (∑ i ∈ Ioc C N, (1 : ℝ) / i) / K := by
    simp only [sum_div]
  have hsquare :
      (∑ i ∈ Ioc C N, 9 * ((1 : ℝ) / (i : ℝ) ^ 2)) =
        9 * (∑ i ∈ Ioc C N, (1 : ℝ) / (i : ℝ) ^ 2) := by
    rw [mul_sum]
  calc
    (∑ i ∈ Ioc C N, occupancyErrorMajorant A K i) ≤
        ∑ i ∈ Ioc C N,
          (((1 : ℝ) / i) / K + A * (((K : ℝ) / C) ^ 25) +
            9 * ((1 : ℝ) / (i : ℝ) ^ 2)) :=
      sum_le_sum fun i hi ↦ hpoint i hi
    _ = (∑ i ∈ Ioc C N, (1 : ℝ) / i) / K +
          ((Ioc C N).card : ℝ) *
            (A * (((K : ℝ) / C) ^ 25)) +
          9 * (∑ i ∈ Ioc C N, (1 : ℝ) / (i : ℝ) ^ 2) := by
      rw [sum_add_distrib, sum_add_distrib, hfirst, hsquare]
      simp only [sum_const, nsmul_eq_mul]
    _ ≤ (∑ i ∈ Ioc C N, (1 : ℝ) / i) / K +
          (N : ℝ) * (A * (((K : ℝ) / C) ^ 25)) +
          9 * (1 / (C : ℝ)) := by
      have hcard : ((Ioc C N).card : ℝ) ≤ N := by
        rw [Nat.card_Ioc]
        exact_mod_cast Nat.sub_le N C
      have hcoef : 0 ≤ A * (((K : ℝ) / C) ^ 25) := by positivity
      gcongr
      exact sum_Ioc_one_div_sq_le hC hCN
    _ = (∑ i ∈ Ioc C N, (1 : ℝ) / i) / K +
          A * (N : ℝ) * (((K : ℝ) / C) ^ 25) + 9 / (C : ℝ) := by
      ring

/-- The sum of the explicit majorant tends to zero on the scales used in the
proof of Erdős Problem 144. -/
theorem tendsto_sum_occupancyErrorMajorant_zero (A : ℝ) (hA : 0 ≤ A) :
    Tendsto
      (fun s ↦ ∑ i ∈ Ioc (lowerScale s) (finalTop s),
        occupancyErrorMajorant A (transferMesh s) i)
      atTop (nhds 0) := by
  let H : ℕ → ℝ := fun s ↦
    (∑ i ∈ Ioc (lowerScale s) (finalTop s), (1 : ℝ) / i) /
      transferMesh s
  let P : ℕ → ℝ := fun s ↦
    A * (finalTop s : ℝ) *
      (((transferMesh s : ℝ) / lowerScale s) ^ 25)
  let R : ℕ → ℝ := fun s ↦ 9 / (lowerScale s : ℝ)
  have hH : Tendsto H atTop (nhds 0) := by
    simpa only [H] using tendsto_harmonicIntervalMass_div_transferMesh_zero
  have hP : Tendsto P atTop (nhds 0) := by
    have h :=
      (tendsto_finalTop_mul_transferRatio_pow_zero 25 (by omega)).const_mul A
    simpa only [P, mul_assoc, mul_zero] using h
  have hLowerNat : Tendsto lowerScale atTop atTop := by
    exact (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : 1 < (8 : ℕ))).comp
      tendsto_lowerExponent_atTop
  have hLower : Tendsto (fun s ↦ (lowerScale s : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hLowerNat
  have hR : Tendsto R atTop (nhds 0) := by
    simpa only [R] using tendsto_const_nhds.div_atTop hLower
  apply squeeze_zero' (g := fun s ↦ H s + P s + R s)
  · filter_upwards with s
    exact sum_nonneg fun i hi ↦ by
      unfold occupancyErrorMajorant
      positivity
  · filter_upwards with s
    exact sum_occupancyErrorMajorant_le hA
      (by simp [lowerScale]) (lowerScale_le_finalTop s)
  · simpa only [H, P, R, zero_add, add_zero] using (hH.add hP).add hR

/-- Generic interface for the analytic layer.  Any eventually nonnegative
family satisfying the pointwise occupancy majorant has vanishing total error
on the explicit reservoir. -/
theorem tendsto_sum_zero_of_eventually_le_occupancyErrorMajorant
    (f : ℕ → ℕ → ℝ) (A : ℝ) (hA : 0 ≤ A)
    (hf0 : ∀ᶠ s : ℕ in atTop, ∀ i ∈ Ioc (lowerScale s) (finalTop s),
      0 ≤ f s i)
    (hf : ∀ᶠ s : ℕ in atTop, ∀ i ∈ Ioc (lowerScale s) (finalTop s),
      f s i ≤ occupancyErrorMajorant A (transferMesh s) i) :
    Tendsto
      (fun s ↦ ∑ i ∈ Ioc (lowerScale s) (finalTop s), f s i)
      atTop (nhds 0) := by
  apply squeeze_zero'
    (g := fun s ↦ ∑ i ∈ Ioc (lowerScale s) (finalTop s),
      occupancyErrorMajorant A (transferMesh s) i)
  · filter_upwards [hf0] with s hs
    exact sum_nonneg hs
  · filter_upwards [hf] with s hs
    exact sum_le_sum hs
  · exact tendsto_sum_occupancyErrorMajorant_zero A hA

/-- Exact downstream interface for logarithmic prime-block occupancies.  The
pointwise hypothesis is precisely the conclusion of
`abs_logBlockOccupancy_sub_inv_le_massPow_twenty_five`. -/
theorem tendsto_sum_abs_logBlockOccupancy_sub_inv_zero_of_eventually_le
    (A : ℝ) (hA : 0 ≤ A)
    (hpoint : ∀ᶠ s : ℕ in atTop,
      ∀ i ∈ Ioc (lowerScale s) (finalTop s),
        |logBlockOccupancy (transferMesh s) i - (i : ℝ)⁻¹| ≤
          1 / ((transferMesh s : ℝ) * i) +
            1 / ((i : ℝ) * (i + 1)) +
            A * (((transferMesh s : ℝ) / i) ^ 25) +
            8 / (i : ℝ) ^ 2) :
    Tendsto
      (fun s ↦ ∑ i ∈ Ioc (lowerScale s) (finalTop s),
        |logBlockOccupancy (transferMesh s) i - (i : ℝ)⁻¹|)
      atTop (nhds 0) := by
  apply tendsto_sum_zero_of_eventually_le_occupancyErrorMajorant
    (fun s i ↦ |logBlockOccupancy (transferMesh s) i - (i : ℝ)⁻¹|) A hA
  · filter_upwards with s i hi
    exact abs_nonneg _
  · filter_upwards [hpoint] with s hs
    intro i hi
    rw [occupancyErrorMajorant_eq]
    exact hs i hi

/-- The same estimate in the exact subtype-indexed, doubled form consumed by
`FinalTransfer.hasDensity_one_of_harmonic_prob_and_occupancy_error`. -/
theorem tendsto_two_mul_sum_subtype_abs_logBlockOccupancy_sub_inv_zero_of_eventually_le
    (A : ℝ) (hA : 0 ≤ A)
    (hpoint : ∀ᶠ s : ℕ in atTop,
      ∀ i ∈ Ioc (lowerScale s) (finalTop s),
        |logBlockOccupancy (transferMesh s) i - (i : ℝ)⁻¹| ≤
          1 / ((transferMesh s : ℝ) * i) +
            1 / ((i : ℝ) * (i + 1)) +
            A * (((transferMesh s : ℝ) / i) ^ 25) +
            8 / (i : ℝ) ^ 2) :
    Tendsto
      (fun s ↦ 2 * ∑ i : ↥(Ioc (lowerScale s) (finalTop s)),
        |logBlockOccupancy (transferMesh s) i.1 - 1 / (i.1 : ℝ)|)
      atTop (nhds 0) := by
  have hfinite :=
    tendsto_sum_abs_logBlockOccupancy_sub_inv_zero_of_eventually_le A hA hpoint
  have hsubtype : Tendsto
      (fun s ↦ ∑ i : ↥(Ioc (lowerScale s) (finalTop s)),
        |logBlockOccupancy (transferMesh s) i.1 - 1 / (i.1 : ℝ)|)
      atTop (nhds 0) := by
    refine hfinite.congr' (Eventually.of_forall fun s ↦ ?_)
    change (∑ i ∈ Ioc (lowerScale s) (finalTop s),
        |logBlockOccupancy (transferMesh s) i - (i : ℝ)⁻¹|) =
      ∑ i : ↥(Ioc (lowerScale s) (finalTop s)),
        |logBlockOccupancy (transferMesh s) i.1 - 1 / (i.1 : ℝ)|
    simpa only [one_div] using
      Finset.sum_subtype (Ioc (lowerScale s) (finalTop s)) (by simp)
        (fun i ↦ |logBlockOccupancy (transferMesh s) i - (i : ℝ)⁻¹|)
  simpa only [mul_zero] using hsubtype.const_mul 2

end

end Erdos144.OccupancyErrorSum
