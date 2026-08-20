/-
Copyright (c) 2026 The Formal Conjectures Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Formal Conjectures Authors
-/

import ErdosProblems.Erdos446.ScaleSelection
import Mathlib.Analysis.SpecialFunctions.Stirling

/-!
# Erdős Problem 446: the Stirling coefficient in the lower bound

This file isolates the part of Ford's finite lower bound which depends on
the construction depth.  Stirling's formula turns the cyclic-composition
factor into the exponential base `2 * exp 1 * log 2`, with the required
power `K^(-3/2)`.
-/

namespace Erdos446

open Filter Real Asymptotics
open scoped Topology

noncomputable def fordCombinatorialWeight (K : ℕ) : ℝ :=
  (2 * Real.log 2 : ℝ) ^ K *
    ((K : ℝ) ^ (K - 1) / (K.factorial : ℝ))

noncomputable def fordStirlingModel (K : ℕ) : ℝ :=
  (2 * Real.log 2 * Real.exp 1 : ℝ) ^ K /
    ((K : ℝ) * Real.sqrt (2 * (K : ℝ) * Real.pi))

private theorem ford_stirling_quotient_eq_model {K : ℕ} (hK : 0 < K) :
    ((2 * Real.log 2 : ℝ) ^ K * (K : ℝ) ^ (K - 1)) /
        (Real.sqrt (2 * (K : ℝ) * Real.pi) *
          ((K : ℝ) / Real.exp 1) ^ K) =
      fordStirlingModel K := by
  have hKR : (K : ℝ) ≠ 0 := by exact_mod_cast hK.ne'
  have hExp : Real.exp (1 : ℝ) ≠ 0 := (Real.exp_pos 1).ne'
  have hSqrt : Real.sqrt (2 * (K : ℝ) * Real.pi) ≠ 0 := by
    positivity
  rw [pow_sub₀ (K : ℝ) hKR (by omega : 1 ≤ K), pow_one, div_pow]
  dsimp [fordStirlingModel]
  rw [mul_pow]
  field_simp
  ring

theorem fordCombinatorialWeight_isTheta_stirlingModel :
    fordCombinatorialWeight =Θ[atTop] fordStirlingModel := by
  have hquot :=
    (isTheta_refl
      (fun K : ℕ ↦
        (2 * Real.log 2 : ℝ) ^ K * (K : ℝ) ^ (K - 1)) atTop).div
      Stirling.factorial_isEquivalent_stirling.isTheta
  have heq :
      (fun K : ℕ ↦
          ((2 * Real.log 2 : ℝ) ^ K * (K : ℝ) ^ (K - 1)) /
            (Real.sqrt (2 * (K : ℝ) * Real.pi) *
              ((K : ℝ) / Real.exp 1) ^ K)) =ᶠ[atTop]
        fordStirlingModel := by
    filter_upwards [eventually_gt_atTop 0] with K hK
    exact ford_stirling_quotient_eq_model hK
  have hmodel := hquot.trans heq.isTheta
  have hdef : fordCombinatorialWeight =ᶠ[atTop]
      fun K : ℕ ↦
        ((2 * Real.log 2 : ℝ) ^ K * (K : ℝ) ^ (K - 1)) /
          (K.factorial : ℝ) := by
    filter_upwards [] with K
    dsimp [fordCombinatorialWeight]
    ring
  exact hdef.isTheta.trans hmodel

end Erdos446
