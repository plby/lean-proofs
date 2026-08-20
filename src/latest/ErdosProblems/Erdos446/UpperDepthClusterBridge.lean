/-
Copyright (c) 2026 The Formal Conjectures Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Formal Conjectures Authors
-/

import ErdosProblems.Erdos446.UpperDepthComparison
import ErdosProblems.Erdos446.UpperBridgeAudit

/-!
# Erdős Problem 446: terminal-block cluster bound to final upper interface

This module lets the finite upper calculation state its result at the actual
number of retained prime blocks.  Constant-shift stability then supplies the
`SmoothSquarefreeClusterModelUpper` input expected by the final assembly.
-/

namespace Erdos446

open Filter Real Asymptotics
open scoped Topology

def SmoothSquarefreeClusterUpperBlockCount
    (M : ℕ) (D : ℝ) (Y : ℕ) : Prop :=
  ∀ y : ℕ, Y ≤ y →
    squarefreeClusterMass (2 * y) ≤
      D * fordCombinatorialWeight (upperPrimeBlockCount M y)

theorem exists_smoothSquarefreeClusterModelUpper_of_upperBlockCount
    {M : ℕ} {D : ℝ} {Y : ℕ} (hD : 0 < D)
    (h : SmoothSquarefreeClusterUpperBlockCount M D Y) :
    ∃ D' : ℝ, ∃ Y' : ℕ, 0 < D' ∧
      SmoothSquarefreeClusterModelUpper M D' Y' := by
  rcases (fordCombinatorialWeight_upperPrimeBlockCount_isTheta M).1.bound with
    ⟨c, hc⟩
  rw [eventually_atTop] at hc
  obtain ⟨Yc, hYc⟩ := hc
  let E : ℝ := |c| + 1
  let D' : ℝ := D * E
  let Y' : ℕ := max Y Yc
  have hE : 0 < E := by dsimp [E]; positivity
  have hD' : 0 < D' := by dsimp [D']; positivity
  refine ⟨D', Y', hD', ?_⟩
  intro y hy
  have hyY : Y ≤ y := (le_max_left _ _).trans hy
  have hyc : Yc ≤ y := (le_max_right _ _).trans hy
  have hcountNonneg :
      0 ≤ fordCombinatorialWeight (upperPrimeBlockCount M y) := by
    dsimp [fordCombinatorialWeight]
    positivity
  have hscaleNonneg :
      0 ≤ fordCombinatorialWeight (fordScaleDepth M y) := by
    dsimp [fordCombinatorialWeight]
    positivity
  have hnorm := hYc y hyc
  have hweight : fordCombinatorialWeight (upperPrimeBlockCount M y) ≤
      E * fordCombinatorialWeight (fordScaleDepth M y) := by
    have hcE : c ≤ E := by
      dsimp [E]
      linarith [le_abs_self c]
    have hraw : fordCombinatorialWeight (upperPrimeBlockCount M y) ≤
        c * fordCombinatorialWeight (fordScaleDepth M y) := by
      simpa only [Real.norm_eq_abs, abs_of_nonneg hcountNonneg,
        abs_of_nonneg hscaleNonneg] using hnorm
    exact hraw.trans (mul_le_mul_of_nonneg_right hcE hscaleNonneg)
  calc
    squarefreeClusterMass (2 * y) ≤
        D * fordCombinatorialWeight (upperPrimeBlockCount M y) := h y hyY
    _ ≤ D * (E * fordCombinatorialWeight (fordScaleDepth M y)) := by
      exact mul_le_mul_of_nonneg_left hweight hD.le
    _ = D' * fordCombinatorialWeight (fordScaleDepth M y) := by
      dsimp [D']
      ring

theorem delta_isTheta_growth446_of_sieveCluster_upperBlockCount
    {M : ℕ} {A D : ℝ} {YSieve YCluster : ℕ}
    (hA : 0 < A) (hD : 0 < D)
    (hSieve : DyadicUpperSieveClusterReduction A YSieve)
    (hCluster :
      SmoothSquarefreeClusterUpperBlockCount M D YCluster) :
    delta =Θ[atTop] growth446 := by
  obtain ⟨D', Y', hD', hCluster'⟩ :=
    exists_smoothSquarefreeClusterModelUpper_of_upperBlockCount hD hCluster
  exact delta_isTheta_growth446_of_sieveCluster
    hA hD' hSieve hCluster'

end Erdos446
