/-
Copyright (c) 2026 The Formal Conjectures Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Formal Conjectures Authors
-/

import ErdosProblems.Erdos446.FixedLowerEnergyZeroDeficit

/-!
# Erdős Problem 446: the complete prefix-energy moment bound

This file partitions the exact deficit-indexed energy sum into its four
boundary and interior pieces.  Combining their finite Abel and Smirnov
estimates gives the uniform moment bound used in the fixed-multiplicity
lower construction.
-/

namespace Erdos446

open Finset Real
open scoped BigOperators

/-- Exact partition of the deficit-indexed moment into its endpoint,
zero-deficit interior, positive-deficit interior, and zero-prefix edge. -/
theorem fixedLowerDeficitEnergySum_decomposition
    {k : ℕ} (hk : 1 ≤ k) :
    fixedLowerDeficitEnergySum k =
      smirnovOccupancyMass k 1 k +
        fixedEnergyZeroDeficitInterior k +
        fixedEnergyPositiveDeficitInteriorSum k +
        fixedEnergyZeroPrefixEdge k := by
  let T : ℕ → ℕ → ℝ := fun d p ↦
    (1 / (2 : ℝ) ^ d) *
      smirnovOccupancyMass (k - p) 1 (k - p + d) *
      smirnovOccupancyMass p (d + 1) (p - d)
  let D : ℕ → ℝ := fun d ↦
    ∑ p ∈ (Finset.Icc d k).filter (fun p ↦ 1 ≤ k - p + d), T d p
  have hrange : Finset.range k = insert 0 (Finset.Ico 1 k) := by
    ext d
    simp
    omega
  have hDzero : D 0 =
      smirnovOccupancyMass k 1 k +
        ∑ p ∈ Finset.Ico 1 k,
          smirnovOccupancyMass (k - p) 1 (k - p) *
            smirnovOccupancyMass p 1 p := by
    have hset : (Finset.Icc 0 k).filter (fun p ↦ 1 ≤ k - p + 0) =
        Finset.range k := by
      ext p
      simp
      omega
    simp only [D]
    rw [hset, hrange, Finset.sum_insert (by simp)]
    have hm0 : smirnovOccupancyMass 0 1 0 = 1 := by
      simpa using smirnovOccupancyMass_zero_eq_one 0 0
    simp only [T, Nat.sub_zero, Nat.add_zero, pow_zero, one_div, inv_one,
      one_mul, hm0, mul_one]
  have hDtop : D k = 0 := by
    simp only [D]
    apply Finset.sum_eq_zero
    intro p hp
    have hpk : p = k := by
      simp only [Finset.mem_filter, Finset.mem_Icc] at hp
      omega
    subst p
    simp only [T, Nat.sub_self, zero_add]
    rw [smirnovOccupancyMass_zero_length_eq_zero (by omega : 0 < k)]
    ring
  have hDinterior : ∀ d ∈ Finset.Ico 1 k,
      D d = fixedEnergyDeficitInterior k d +
        (1 / (2 : ℝ) ^ d) * smirnovOccupancyMass 0 1 d *
          smirnovOccupancyMass k (d + 1) (k - d) := by
    intro d hdMem
    have hd := Finset.mem_Ico.mp hdMem
    have hfilter :
        (Finset.Icc d k).filter (fun p ↦ 1 ≤ k - p + d) =
          Finset.Icc d k := by
      ext p
      simp only [Finset.mem_filter, Finset.mem_Icc]
      constructor
      · exact fun h ↦ h.1
      · intro h
        exact ⟨h, by omega⟩
    have hicc : Finset.Icc d k =
        insert d (Finset.Ico (d + 1) (k + 1)) := by
      ext p
      simp
      omega
    have hico : Finset.Ico (d + 1) (k + 1) =
        insert k (Finset.Ico (d + 1) k) := by
      ext p
      simp
      omega
    simp only [D]
    rw [hfilter, hicc, Finset.sum_insert (by simp)]
    have hdiag : T d d = 0 := by
      dsimp only [T]
      simp only [Nat.sub_self]
      rw [smirnovOccupancyMass_zero_length_eq_zero hd.1]
      ring
    rw [hdiag, zero_add, hico, Finset.sum_insert (by simp)]
    rw [fixedEnergyDeficitInterior]
    dsimp only [T]
    simp only [Nat.sub_self, zero_add, Nat.add_comm]
    ring
  rw [fixedLowerDeficitEnergySum]
  change (∑ d ∈ Finset.range (k + 1), D d) = _
  rw [Finset.sum_range_succ, hDtop, add_zero, hrange,
    Finset.sum_insert (by simp), hDzero]
  have hinteriorSum :
      (∑ d ∈ Finset.Ico 1 k, D d) =
        fixedEnergyPositiveDeficitInteriorSum k +
          fixedEnergyZeroPrefixEdge k := by
    rw [fixedEnergyPositiveDeficitInteriorSum,
      fixedEnergyZeroPrefixEdge, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl hDinterior
  rw [hinteriorSum, fixedEnergyZeroDeficitInterior]
  ring

/-- The complete prefix-energy moment is bounded by an absolute constant
times Ford's natural composition scale. -/
theorem fixedLowerPrefixEnergyMoment_le_scale
    {k : ℕ} (hk : 1 ≤ k) :
    fixedLowerPrefixEnergyMoment k ≤
      8000 * Real.exp 4 *
        ((k : ℝ) ^ k / ((k + 1).factorial : ℝ)) := by
  let S : ℝ := (k : ℝ) ^ k / ((k + 1).factorial : ℝ)
  have hS : 0 ≤ S := by
    dsimp [S]
    positivity
  have he : (1 : ℝ) ≤ Real.exp 4 := by
    rw [← Real.exp_zero]
    exact Real.exp_le_exp.mpr (by norm_num)
  by_cases hkTwo : 2 ≤ k
  · have hpositive : fixedEnergyPositiveDeficitInteriorSum k ≤
        4608 * Real.exp 4 * S := by
      simpa [S] using fixedEnergyPositiveDeficitInteriorSum_le_scale hkTwo
    have hzero : fixedEnergyZeroDeficitInterior k ≤
        288 * Real.exp 4 * S := by
      simpa [S] using fixedEnergyZeroDeficitInterior_le_scale hkTwo
    have hedge : fixedEnergyZeroPrefixEdge k ≤
        3072 * S := by
      simpa [S] using fixedEnergyZeroPrefixEdge_le_scale hk
    have hendpoint : smirnovOccupancyMass k 1 k ≤ 3 * S := by
      simpa [S] using fixedEnergyEndpoint_le_scale hk
    have hscaleExp : S ≤ Real.exp 4 * S := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right he hS
    have hedgeExp : fixedEnergyZeroPrefixEdge k ≤
        3072 * Real.exp 4 * S := by
      calc
        fixedEnergyZeroPrefixEdge k ≤ 3072 * S := hedge
        _ ≤ 3072 * (Real.exp 4 * S) :=
          mul_le_mul_of_nonneg_left hscaleExp (by norm_num)
        _ = 3072 * Real.exp 4 * S := by ring
    have hendpointExp : smirnovOccupancyMass k 1 k ≤
        3 * Real.exp 4 * S := by
      calc
        smirnovOccupancyMass k 1 k ≤ 3 * S := hendpoint
        _ ≤ 3 * (Real.exp 4 * S) :=
          mul_le_mul_of_nonneg_left hscaleExp (by norm_num)
        _ = 3 * Real.exp 4 * S := by ring
    rw [fixedLowerPrefixEnergyMoment_eq_deficitSum,
      fixedLowerDeficitEnergySum_decomposition hk]
    dsimp only [S] at hpositive hzero hedgeExp hendpointExp ⊢
    linarith
  · have hkOne : k = 1 := by omega
    subst k
    have hmoment : fixedLowerPrefixEnergyMoment 1 =
        smirnovOccupancyMass 1 1 1 := by
      rw [fixedLowerPrefixEnergyMoment_eq_deficitSum,
        fixedLowerDeficitEnergySum_decomposition (by norm_num)]
      simp [fixedEnergyZeroDeficitInterior,
        fixedEnergyPositiveDeficitInteriorSum,
        fixedEnergyZeroPrefixEdge]
    have hendpoint : smirnovOccupancyMass 1 1 1 ≤ 3 * S := by
      simpa [S] using fixedEnergyEndpoint_le_scale (k := 1) (by norm_num)
    have hcoeff : (3 : ℝ) ≤ 8000 * Real.exp 4 := by
      nlinarith
    calc
      fixedLowerPrefixEnergyMoment 1 = smirnovOccupancyMass 1 1 1 := hmoment
      _ ≤ 3 * S := hendpoint
      _ ≤ (8000 * Real.exp 4) * S :=
        mul_le_mul_of_nonneg_right hcoeff hS
      _ = 8000 * Real.exp 4 *
          ((((1 : ℕ) : ℝ) ^ 1) /
            (((1 : ℕ) + 1).factorial : ℝ)) := by
        dsimp [S]

end Erdos446
