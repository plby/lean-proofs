/-
Copyright (c) 2026 The Formal Conjectures Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Formal Conjectures Authors
-/

import ErdosProblems.Erdos446.LowerModelAsymptotic

/-!
# Erdős Problem 446: the fixed-multiplicity lower model

The `r` distinguished isolated divisors contribute a factor
`2^(K(r-1))`, while the exact-multiplicity sieve costs `log(y)^(r+1)`.
At Ford's selected depth `2^K = Θ(log y)`, these two changes cancel.  This
file proves that cancellation precisely: for every fixed positive `r`, the
resulting model still has order `growth446`.
-/

namespace Erdos446

open Filter Real Asymptotics
open scoped Topology

/-- The model obtained after inserting the `r`th isolated-divisor moment
and the `r+1` logarithmic sieve factors. -/
noncomputable def fordFixedMultiplicityDepthDensityModel
    (r M y : ℕ) : ℝ :=
  (((2 : ℝ) ^ fordScaleDepth M y) ^ (r - 1) * fordDepthModel M y) /
    Real.log (y : ℝ) ^ (r + 1)

theorem eventually_fordFixedMultiplicityDepthDensityModel_pos
    (r M : ℕ) :
    ∀ᶠ y : ℕ in atTop, 0 < fordFixedMultiplicityDepthDensityModel r M y := by
  filter_upwards
      [(Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
        (eventually_gt_atTop 0),
       (tendsto_fordScaleDepth_atTop M).eventually (eventually_gt_atTop 0)]
      with y hlog hK
  have hKR : (0 : ℝ) < fordScaleDepth M y := by exact_mod_cast hK
  dsimp [fordFixedMultiplicityDepthDensityModel, fordDepthModel]
  positivity

/-- The fixed-`r` isolated-divisor model has exactly Ford's union-density
scale. -/
theorem fordFixedMultiplicityDepthDensityModel_isTheta_growth446
    {r : ℕ} (hr : 1 ≤ r) (M : ℕ) :
    fordFixedMultiplicityDepthDensityModel r M =Θ[atTop] growth446 := by
  have hdepthPow := ((log_nat_isTheta_pow_fordScaleDepth M).pow (r - 1)).symm
  have hnum := hdepthPow.mul (fordDepthModel_isTheta_logModel M)
  have hquot := hnum.div
    (isTheta_refl (fun y : ℕ ↦ Real.log (y : ℝ) ^ (r + 1)) atTop)
  have heq :
      (fun y : ℕ ↦
        ((Real.log (y : ℝ) ^ (r - 1)) *
          (Real.log (y : ℝ) ^ (2 - alpha446) /
            Real.log (Real.log (y : ℝ)) ^ (3 / 2 : ℝ))) /
          Real.log (y : ℝ) ^ (r + 1)) =ᶠ[atTop] growth446 := by
    filter_upwards [(Real.tendsto_log_atTop.comp
      tendsto_natCast_atTop_atTop).eventually (eventually_gt_atTop 0)]
      with y hlog
    let x : ℝ := Real.log (y : ℝ)
    let z : ℝ := Real.log (Real.log (y : ℝ)) ^ (3 / 2 : ℝ)
    have hx : 0 < x := hlog
    have hrCast : ((r - 1 : ℕ) : ℝ) = (r : ℝ) - 1 := by
      rw [Nat.cast_sub hr]
      norm_num
    have hrAddCast : ((r + 1 : ℕ) : ℝ) = (r : ℝ) + 1 := by
      push_cast
      ring
    have hpower :
        (x ^ (r - 1) * x ^ (2 - alpha446)) / x ^ (r + 1) =
          x ^ (-alpha446) := by
      rw [← Real.rpow_natCast, ← Real.rpow_natCast,
        ← Real.rpow_add hx, ← Real.rpow_sub hx]
      congr 1
      rw [hrCast, hrAddCast]
      ring
    dsimp [growth446, growthDenominator446]
    change ((x ^ (r - 1)) * (x ^ (2 - alpha446) / z)) /
        x ^ (r + 1) = (x ^ alpha446 * z)⁻¹
    rw [show ((x ^ (r - 1)) * (x ^ (2 - alpha446) / z)) /
        x ^ (r + 1) =
          ((x ^ (r - 1) * x ^ (2 - alpha446)) / x ^ (r + 1)) / z by ring,
      hpower, Real.rpow_neg hx.le]
    ring
  have hdef : fordFixedMultiplicityDepthDensityModel r M =ᶠ[atTop]
      fun y : ℕ ↦
        (((2 : ℝ) ^ fordScaleDepth M y) ^ (r - 1) *
          fordDepthModel M y) / Real.log (y : ℝ) ^ (r + 1) :=
    Eventually.of_forall fun _ ↦ rfl
  exact hdef.isTheta.trans (hquot.trans heq.isTheta)

end Erdos446
