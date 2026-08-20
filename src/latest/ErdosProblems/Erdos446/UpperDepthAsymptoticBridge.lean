/-
Copyright (c) 2026 The Formal Conjectures Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Formal Conjectures Authors
-/

import ErdosProblems.Erdos446.UpperDepthComparison
import ErdosProblems.Erdos446.UpperAsymptoticAssembly

/-!
# Erdős Problem 446: upper cutoff model at Ford's final scale

The prime-block calculation naturally produces the weight at the number of
blocks actually retained up to `2*y`.  This file converts that expression
directly to the model used by the final upper assembly.
-/

namespace Erdos446

open Filter Real Asymptotics
open scoped Topology

noncomputable def upperPrimeBlockDensityModel (M y : ℕ) : ℝ :=
  fordCombinatorialWeight (upperPrimeBlockCount M y) /
    Real.log (y : ℝ) ^ 2

theorem upperPrimeBlockDensityModel_isTheta_fordUpperDensityModel (M : ℕ) :
    upperPrimeBlockDensityModel M =Θ[atTop] fordUpperDensityModel M := by
  have hweight := fordCombinatorialWeight_upperPrimeBlockCount_isTheta M
  have hinv :
      (fun y : ℕ ↦ (Real.log (y : ℝ) ^ 2)⁻¹) =Θ[atTop]
        (fun y : ℕ ↦ (Real.log (y : ℝ) ^ 2)⁻¹) :=
    isTheta_refl _ _
  have hmul := hweight.mul hinv
  have hleft : upperPrimeBlockDensityModel M =ᶠ[atTop]
      fun y : ℕ ↦ fordCombinatorialWeight (upperPrimeBlockCount M y) *
        (Real.log (y : ℝ) ^ 2)⁻¹ :=
    Eventually.of_forall fun y ↦ by
      dsimp [upperPrimeBlockDensityModel]
      rw [div_eq_mul_inv]
  have hright : fordUpperDensityModel M =ᶠ[atTop]
      fun y : ℕ ↦ fordCombinatorialWeight (fordScaleDepth M y) *
        (Real.log (y : ℝ) ^ 2)⁻¹ :=
    Eventually.of_forall fun y ↦ by
      dsimp [fordUpperDensityModel]
      rw [div_eq_mul_inv]
  exact hleft.isTheta.trans (hmul.trans hright.isTheta.symm)

theorem upperPrimeBlockDensityModel_isTheta_growth446 (M : ℕ) :
    upperPrimeBlockDensityModel M =Θ[atTop] growth446 :=
  (upperPrimeBlockDensityModel_isTheta_fordUpperDensityModel M).trans
    (fordUpperDensityModel_isTheta_growth446 M)

end Erdos446
