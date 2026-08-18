/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.PZ.Intersection.SourceFunctionalSlabAsymptotics

namespace Erdos186.PZ.Intersection

noncomputable section

set_option autoImplicit false

/-- A dense eligible input inherits the fixed-density power of the source
population in its selected dilation. -/
theorem fixed_dense_power_le_scaleDenSum_mul_dilation
    {beta eta : ℝ}
    (context : Reduction.HigherDimensionalContext beta eta)
    {rankCeiling N r : ℕ} {X : Finset (LatticePoint r)}
    (I : Reduction.EligibleInput context X)
    {delta : ℝ} (heta : 0 ≤ eta) (hdelta : 0 ≤ delta)
    (hrank : r ≤ rankCeiling)
    (hdense : delta * (N : ℝ) ≤ (X.card : ℝ)) :
    delta ^ eta * (N : ℝ) ^ eta ≤
      (Reduction.scaleDenSum context rankCeiling : ℝ) *
        (I.selectedCFP.dilation : ℝ) := by
  have hpopulationPow : delta ^ eta * (N : ℝ) ^ eta ≤
      (X.card : ℝ) ^ eta := by
    rw [← Real.mul_rpow hdelta (Nat.cast_nonneg N)]
    exact Real.rpow_le_rpow
      (mul_nonneg hdelta (Nat.cast_nonneg N)) hdense heta
  exact hpopulationPow.trans (I.scale_lower.trans
    (eligibleInput_scale_le_scaleDenSum_mul_dilation context I hrank))

end

end Erdos186.PZ.Intersection
