/-
Copyright (c) 2026 The Formal Conjectures Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Formal Conjectures Authors
-/

import ErdosProblems.Erdos446.UpperTrimmedCentralAssembly

/-!
# Erdős Problem 446: unconditional squarefree cluster endpoint

The one-sided trimming argument is now instantiated with the quantitative
Mertens constants.  The retained/residual low-cardinality calculation and
the elementary high-cardinality tail together prove the exact
`SmoothSquarefreeClusterUpperBlockCount` interface consumed by the final
upper assembly.
-/

namespace Erdos446

open Filter Finset Real
open scoped BigOperators Topology

noncomputable section

/-- The actual finite block calculation required by the final sieve/cluster
assembly.  No analytic or combinatorial assumptions remain. -/
theorem exists_smoothSquarefreeClusterUpperBlockCount :
    ∃ M : ℕ, ∃ D : ℝ, ∃ Y : ℕ,
      0 < D ∧ SmoothSquarefreeClusterUpperBlockCount M D Y := by
  obtain ⟨C, hC, J, hmass⟩ :=
    exists_primeBlockMass_geometric_error_threshold
  let M : ℕ := J
  have hhighEventually :=
    eventually_highSquarefreeClusterTail_le_fordCombinatorialWeight M
  rw [eventually_atTop] at hhighEventually
  obtain ⟨Yhigh, hYhigh⟩ := hhighEventually
  let lowCoefficient : ℝ :=
    (smallPrimeClusterFactor M *
      Real.exp (4 * (C + 1) / (2 : ℝ) ^ M)) *
      (sharpBlockLayerScale M *
        (2 * fordWeightedLayerMassConstant * 936))
  let D : ℝ := lowCoefficient + 1
  let Y : ℕ := max Yhigh (fordConstructionScale M 1)
  have hsmallNonneg : 0 ≤ smallPrimeClusterFactor M :=
    smallPrimeClusterFactor_nonneg M
  have hscaleNonneg : 0 ≤ sharpBlockLayerScale M :=
    (sharpBlockLayerScale_pos M).le
  have hweightedNonneg : 0 ≤ fordWeightedLayerMassConstant :=
    fordWeightedLayerMassConstant_nonneg
  have hlowCoefficient : 0 ≤ lowCoefficient := by
    dsimp [lowCoefficient]
    exact mul_nonneg
      (mul_nonneg hsmallNonneg (Real.exp_pos _).le)
      (mul_nonneg hscaleNonneg
        (mul_nonneg (mul_nonneg (by norm_num) hweightedNonneg)
          (by norm_num)))
  have hD : 0 < D := by
    dsimp [D]
    linarith
  refine ⟨M, D, Y, hD, ?_⟩
  intro y hy
  have hyHigh : Yhigh ≤ y := (le_max_left _ _).trans hy
  have hyScale : fordConstructionScale M 1 ≤ y :=
    (le_max_right _ _).trans hy
  let V : ℕ := fordScaleDepth M y
  let K : ℕ := upperPrimeBlockCount M y
  have hVpos : 0 < V := fordScaleDepth_pos hyScale
  have hKshift : K = V + 8 ∨ K = V + 9 := by
    simpa only [K, V] using upperPrimeBlockCount_eq_shift_or_succ hyScale
  have hK8 : 8 ≤ K := by
    rcases hKshift with hK | hK
    · rw [hK]
      omega
    · rw [hK]
      omega
  have hVK : V ≤ K := by
    rcases hKshift with hK | hK
    · rw [hK]
      omega
    · rw [hK]
      omega
  have hLK : 10 * V ≤ 10 * K := Nat.mul_le_mul_left 10 hVK
  have hcover : primesUpTo (2 * y) ⊆
      trimmedAuxiliaryPrimePool M K ∪ retainedPrimePool M K := by
    simpa only [K] using
      primesUpTo_two_mul_subset_trimmed_union_retained hyScale
  have hlow := sum_lowSquarefreeClusterLayers_le_weight
    hC.le (J := J) (M := M) (K := K) (P := 2 * y) (L := 10 * V)
    (by simp [M]) hmass hK8 hLK hcover
  have htail : highSquarefreeClusterTail M y ≤
      fordCombinatorialWeight V := by
    simpa only [V] using hYhigh y hyHigh
  have hweightMono : fordCombinatorialWeight V ≤
      fordCombinatorialWeight K := by
    rcases hKshift with hK | hK
    · rw [hK]
      exact fordCombinatorialWeight_le_add hVpos
    · rw [hK]
      exact fordCombinatorialWeight_le_add hVpos
  have htail' : highSquarefreeClusterTail M y ≤
      fordCombinatorialWeight K := htail.trans hweightMono
  have hsplit := squarefreeClusterMass_le_low_add_tail
    (2 * y) (10 * V)
  have hweightNonneg : 0 ≤ fordCombinatorialWeight K := by
    dsimp [fordCombinatorialWeight]
    positivity
  calc
    squarefreeClusterMass (2 * y) ≤
        (∑ k ∈ Finset.range (10 * V + 1),
          squarefreeClusterLayer (2 * y) k) +
          highSquarefreeClusterTail M y := by
      simpa only [highSquarefreeClusterTail, V] using hsplit
    _ ≤ lowCoefficient * fordCombinatorialWeight K +
          fordCombinatorialWeight K := by
      apply add_le_add
      · simpa only [lowCoefficient] using hlow
      · exact htail'
    _ = D * fordCombinatorialWeight K := by
      dsimp [D]
      ring
    _ = D * fordCombinatorialWeight (upperPrimeBlockCount M y) := by
      rfl

end

end Erdos446
