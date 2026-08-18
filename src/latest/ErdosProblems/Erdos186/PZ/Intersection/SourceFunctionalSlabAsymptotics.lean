/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.PZ.Intersection.SourceFunctionalSlabNumerics

namespace Erdos186.PZ.Intersection

open Filter
open scoped BigOperators Topology

noncomputable section

set_option autoImplicit false

/-- The selected CFP dilation controls its input scale, with a denominator
uniform over every rank below `rankCeiling`. -/
theorem eligibleInput_scale_le_scaleDenSum_mul_dilation
    {beta eta : ℝ}
    (context : Reduction.HigherDimensionalContext beta eta)
    {rankCeiling r : ℕ} {X : Finset (LatticePoint r)}
    (I : Reduction.EligibleInput context X) (hrank : r ≤ rankCeiling) :
    (I.scale : ℝ) ≤ (Reduction.scaleDenSum context rankCeiling : ℝ) *
      (I.selectedCFP.dilation : ℝ) := by
  have hscaleNat := I.selectedCFP.witness.scale_lower
  have hscaleNum : I.selectedCFP.witness.scaleNum = context.scaleNum r :=
    I.selectedCFP_scaleNum
  have hscaleDen : I.selectedCFP.witness.scaleDen = context.scaleDen r :=
    I.selectedCFP_scaleDen
  have hnum : 1 ≤ context.scaleNum r := context.scaleNum_pos r
  have hscaleNat' : I.scale ≤
      context.scaleDen r * I.selectedCFP.dilation := by
    calc
      I.scale = 1 * I.scale := by simp
      _ ≤ context.scaleNum r * I.scale := Nat.mul_le_mul_right _ hnum
      _ ≤ context.scaleDen r * I.selectedCFP.dilation := by
        rw [hscaleNum, hscaleDen] at hscaleNat
        exact hscaleNat
  have hden := Reduction.scaleDen_le_scaleDenSum context hrank
  exact_mod_cast hscaleNat'.trans
    (Nat.mul_le_mul_right I.selectedCFP.dilation hden)

end

end Erdos186.PZ.Intersection
