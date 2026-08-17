/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ErdosProblems.Erdos144.StrongMertens
import ErdosProblems.Erdos144.OccupancyErrorSum
import ErdosProblems.Erdos144.ScaleLimits

/-!
# Quantitative prime-block asymptotics on the Erdős 144 scales

This file specializes the pointwise strong-Mertens estimate to the explicit
scales of `Erdos144.Harmonic`.  The lower logarithmic coordinate divided by
the mesh tends to infinity, so the endpoint threshold and the polynomial
versus exponential comparison hold uniformly throughout the reservoir.  The
twenty-fifth-power scale separation also makes the analytic tail smaller
than `1 / i`.  Summing the resulting Bonferroni majorant gives the required
total-variation error tending to zero.
-/

open Filter Topology Finset

namespace Erdos144.PrimeBlockAsymptotic

open Erdos144.Harmonic
open Erdos144.PrimeBlocks
open Erdos144.StrongMertens
open Erdos144.OccupancyErrorSum

noncomputable section

/-- A fixed polynomial is eventually dominated by the exponential. -/
lemma eventually_pow_twenty_four_le_exp :
    ∀ᶠ t : ℝ in atTop, t ^ 24 ≤ Real.exp t := by
  have hdom := (isLittleO_pow_exp_pos_mul_atTop 24 one_pos).eventuallyLE
  filter_upwards [hdom, eventually_ge_atTop (0 : ℝ)] with t ht hnonneg
  simpa [Real.norm_eq_abs, abs_of_nonneg hnonneg,
    abs_of_pos (Real.exp_pos t)] using ht

/-- The polynomial/exponential comparison needed in the endpoint estimate
holds uniformly at every coordinate in the harmonic reservoir. -/
lemma eventually_forall_mem_pow_twenty_four_le_exp :
    ∀ᶠ s : ℕ in atTop,
      ∀ i ∈ Ioc (lowerScale s) (finalTop s),
        (((i : ℝ) / transferMesh s) ^ 24) ≤
          Real.exp ((i : ℝ) / transferMesh s) := by
  have hpoly := eventually_pow_twenty_four_le_exp
  rw [eventually_atTop] at hpoly
  obtain ⟨T, hT⟩ := hpoly
  have hscale := tendsto_lowerScale_div_transferMesh_atTop.eventually
    (eventually_ge_atTop T)
  filter_upwards [hscale] with s hs
  intro i hi
  apply hT
  calc
    T ≤ (lowerScale s : ℝ) / transferMesh s := hs
    _ ≤ (i : ℝ) / transferMesh s := by
      apply div_le_div_of_nonneg_right
      · exact_mod_cast (mem_Ioc.mp hi).1.le
      · positivity

/-- The lower logarithmic coordinate eventually exceeds the fixed elementary
threshold used in the floor estimates, uniformly over the reservoir. -/
lemma eventually_forall_mem_two_log_two_le_ratio :
    ∀ᶠ s : ℕ in atTop,
      ∀ i ∈ Ioc (lowerScale s) (finalTop s),
        2 * Real.log 2 ≤ (i : ℝ) / transferMesh s := by
  have hscale := tendsto_lowerScale_div_transferMesh_atTop.eventually
    (eventually_ge_atTop (2 * Real.log 2))
  filter_upwards [hscale] with s hs
  intro i hi
  calc
    2 * Real.log 2 ≤ (lowerScale s : ℝ) / transferMesh s := hs
    _ ≤ (i : ℝ) / transferMesh s := by
      apply div_le_div_of_nonneg_right
      · exact_mod_cast (mem_Ioc.mp hi).1.le
      · positivity

/-- Once the lower endpoint has passed a fixed integer threshold, so have
both endpoints of every logarithmic block in the reservoir. -/
lemma eventually_forall_mem_floor_endpoints (X0 : ℕ) :
    ∀ᶠ s : ℕ in atTop,
      ∀ i ∈ Ioc (lowerScale s) (finalTop s),
        X0 ≤ ⌊Real.exp ((i : ℝ) / transferMesh s)⌋₊ ∧
          X0 ≤ ⌊Real.exp (((i + 1 : ℕ) : ℝ) / transferMesh s)⌋₊ := by
  filter_upwards
    [eventually_nat_le_floor_exp_lowerScale_div_transferMesh X0] with s hs
  intro i hi
  have hKNat : 0 < transferMesh s := by
    rw [transferMesh_eq]
    exact pow_pos (cardinalCutoff_pos s) 2
  have hK : (0 : ℝ) < transferMesh s := by exact_mod_cast hKNat
  have hCi : (lowerScale s : ℝ) / transferMesh s ≤
      (i : ℝ) / transferMesh s := by
    apply div_le_div_of_nonneg_right
    · exact_mod_cast (mem_Ioc.mp hi).1.le
    · exact hK.le
  have hii : (i : ℝ) / transferMesh s ≤
      ((i + 1 : ℕ) : ℝ) / transferMesh s := by
    apply div_le_div_of_nonneg_right
    · norm_num
    · exact hK.le
  have hfloorA : ⌊Real.exp ((lowerScale s : ℝ) / transferMesh s)⌋₊ ≤
      ⌊Real.exp ((i : ℝ) / transferMesh s)⌋₊ :=
    Nat.floor_mono (Real.exp_le_exp.mpr hCi)
  have hfloorB : ⌊Real.exp ((i : ℝ) / transferMesh s)⌋₊ ≤
      ⌊Real.exp (((i + 1 : ℕ) : ℝ) / transferMesh s)⌋₊ :=
    Nat.floor_mono (Real.exp_le_exp.mpr hii)
  exact ⟨hs.trans hfloorA, hs.trans (hfloorA.trans hfloorB)⟩

/-- The scale-separation limit makes the twenty-fifth-power pointwise tail
smaller than `1 / i`, uniformly throughout the reservoir. -/
lemma eventually_forall_mem_analytic_tail_le_inv (A : ℝ) (hA : 0 ≤ A) :
    ∀ᶠ s : ℕ in atTop,
      ∀ i ∈ Ioc (lowerScale s) (finalTop s),
        A * (((transferMesh s : ℝ) / i) ^ 25) ≤ 1 / (i : ℝ) := by
  have hlim : Tendsto
      (fun s ↦ A * ((finalTop s : ℝ) *
        (((transferMesh s : ℝ) / lowerScale s) ^ 25)))
      atTop (nhds 0) := by
    simpa only [mul_zero] using
      tendsto_finalTop_mul_transferRatio_pow_twenty_five_zero.const_mul A
  have hone : ∀ᶠ s : ℕ in atTop,
      A * ((finalTop s : ℝ) *
        (((transferMesh s : ℝ) / lowerScale s) ^ 25)) ≤ 1 := by
    filter_upwards [(tendsto_order.1 hlim).2 1 zero_lt_one] with s hs
    exact hs.le
  filter_upwards [hone] with s hs
  intro i hi
  have hCi : lowerScale s < i := (mem_Ioc.mp hi).1
  have hiN : i ≤ finalTop s := (mem_Ioc.mp hi).2
  have hCNat : 0 < lowerScale s := by simp [lowerScale]
  have hC0 : (0 : ℝ) < lowerScale s := by exact_mod_cast hCNat
  have hiNat : 0 < i := hCNat.trans_le hCi.le
  have hi0 : (0 : ℝ) < i := by exact_mod_cast hiNat
  have hN0 : (0 : ℝ) < finalTop s := by
    exact hi0.trans_le (by exact_mod_cast hiN)
  have hratio : (transferMesh s : ℝ) / i ≤
      (transferMesh s : ℝ) / lowerScale s := by
    apply div_le_div_of_nonneg_left (by positivity) hC0
    exact_mod_cast hCi.le
  have hpow : ((transferMesh s : ℝ) / i) ^ 25 ≤
      ((transferMesh s : ℝ) / lowerScale s) ^ 25 :=
    pow_le_pow_left₀ (by positivity) hratio 25
  calc
    A * (((transferMesh s : ℝ) / i) ^ 25) ≤
        A * (((transferMesh s : ℝ) / lowerScale s) ^ 25) :=
      mul_le_mul_of_nonneg_left hpow hA
    _ ≤ 1 / (finalTop s : ℝ) := by
      apply (le_div_iff₀ hN0).2
      simpa only [mul_assoc, mul_left_comm, mul_comm] using hs
    _ ≤ 1 / (i : ℝ) :=
      one_div_le_one_div_of_le hi0 (by exact_mod_cast hiN)

/-- Uniform pointwise prime-block occupancy estimate on the explicit scales. -/
theorem exists_eventually_uniform_logBlockOccupancy_bound :
    ∃ A : ℝ, 0 < A ∧
      ∀ᶠ s : ℕ in atTop,
        ∀ i ∈ Ioc (lowerScale s) (finalTop s),
          |logBlockOccupancy (transferMesh s) i - (i : ℝ)⁻¹| ≤
            1 / ((transferMesh s : ℝ) * i) +
              1 / ((i : ℝ) * (i + 1)) +
              A * (((transferMesh s : ℝ) / i) ^ 25) +
              8 / (i : ℝ) ^ 2 := by
  obtain ⟨A, hA, X0, hX0, hmass⟩ := exists_logBlockMassError_le_pow 24
  refine ⟨A, hA, ?_⟩
  filter_upwards [eventually_forall_mem_pow_twenty_four_le_exp,
    eventually_forall_mem_two_log_two_le_ratio,
    eventually_forall_mem_floor_endpoints X0,
    eventually_forall_mem_analytic_tail_le_inv A hA.le] with s hpoly hlog hfloor htail
  intro i hi
  have hK : 0 < transferMesh s := by
    rw [transferMesh_eq]
    exact pow_pos (cardinalCutoff_pos s) 2
  have hi0 : 0 < i := by
    have hC : 0 < lowerScale s := by simp [lowerScale]
    have hCi : lowerScale s < i := (mem_Ioc.mp hi).1
    omega
  have hmass' := hmass (transferMesh s) i hK hi0 (hlog i hi)
    (hpoly i hi) (hfloor i hi).1 (hfloor i hi).2
  exact abs_logBlockOccupancy_sub_inv_le_massPow_twenty_five
    hK hi0 hA.le hmass' (htail i hi)

/-- The total discrepancy between logarithmic prime-block occupancy and the
ideal harmonic coordinate mass tends to zero. -/
theorem tendsto_sum_abs_logBlockOccupancy_sub_inv_zero :
    Tendsto
      (fun s ↦ ∑ i ∈ Ioc (lowerScale s) (finalTop s),
        |logBlockOccupancy (transferMesh s) i - (i : ℝ)⁻¹|)
      atTop (nhds 0) := by
  obtain ⟨A, hA, hpoint⟩ := exists_eventually_uniform_logBlockOccupancy_bound
  exact tendsto_sum_abs_logBlockOccupancy_sub_inv_zero_of_eventually_le
    A hA.le hpoint

/-- The exact doubled, subtype-indexed discrepancy limit consumed by the
final CRT transfer theorem. -/
theorem tendsto_two_mul_sum_subtype_abs_logBlockOccupancy_sub_inv_zero :
    Tendsto
      (fun s ↦ 2 * ∑ i : ↥(Ioc (lowerScale s) (finalTop s)),
        |logBlockOccupancy (transferMesh s) i.1 - 1 / (i.1 : ℝ)|)
      atTop (nhds 0) := by
  obtain ⟨A, hA, hpoint⟩ := exists_eventually_uniform_logBlockOccupancy_bound
  exact
    tendsto_two_mul_sum_subtype_abs_logBlockOccupancy_sub_inv_zero_of_eventually_le
      A hA.le hpoint

end

end Erdos144.PrimeBlockAsymptotic
