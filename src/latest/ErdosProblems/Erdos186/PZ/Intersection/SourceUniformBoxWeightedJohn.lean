/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.PZ.Intersection.BoxWeightedFunctionalSlab

/-!
# Rank-uniform constants for the box-weighted John contradiction

The geometric constant in the box-weighted slab argument depends only on
the ambient rank.  This file gives that choice a deterministic name and
bounds it over a fixed rank ceiling, so all analytic thresholds may be
chosen before the terminal input is known.
-/

namespace Erdos186.PZ.Intersection

noncomputable section

set_option autoImplicit false

/-- A deterministic factor bound for the box-weighted John contradiction
in a fixed positive rank.  Rank zero is assigned the harmless value one. -/
def sourceBoxWeightedJohnFactorBound (d : ℕ) : ℕ :=
  if hd : 0 < d then
    Classical.choose (exists_boxWeightedFunctionalSlabContradictionConstants
      d hd)
  else 1

/-- A deterministic John constant in a fixed positive rank. -/
def sourceBoxWeightedJohnConstant (d : ℕ) : ℝ :=
  if hd : 0 < d then
    Classical.choose (Classical.choose_spec
      (exists_boxWeightedFunctionalSlabContradictionConstants d hd))
  else 1

theorem sourceBoxWeightedJohnConstant_one_le (d : ℕ) :
    1 ≤ sourceBoxWeightedJohnConstant d := by
  by_cases hd : 0 < d
  · rw [sourceBoxWeightedJohnConstant, dif_pos hd]
    exact (Classical.choose_spec (Classical.choose_spec
      (exists_boxWeightedFunctionalSlabContradictionConstants d hd))).1
  · simp only [sourceBoxWeightedJohnConstant, dif_neg hd, le_refl]

/-- The defining contradiction theorem for the deterministic rank
constant. -/
theorem sourceBoxWeightedJohnContradiction
    (d : ℕ) (hd : 0 < d) :
    ∀ {s D k loss referenceVolume boxFactor : ℕ}
      {A : Finset (LatticePoint d)}
      (W : CFP.EnhancedCFPWitness A s D k loss)
      (B : IntegerBox d)
      (f : (Fin d → ℝ) →L[ℝ] ℝ) (t gamma : ℝ),
      W.rank = d →
      ConvexDensity.IsConvexBody (OneStepAssembly.boxRealization B) →
      f ≠ 0 → 0 < t →
      (0 : LatticePoint d) ∈ B.carrier →
      W.core ⊆ B.carrier →
      (∀ x ∈ W.core,
        |f (realVector x)| < t * boxCoefficientMass B f) →
      1 ≤ (2 * (d : ℝ) * t) * (B.carrier.card : ℝ) →
      B.carrier.card ≤ boxFactor * referenceVolume →
      0 < referenceVolume → 0 < gamma →
      gamma * (referenceVolume : ℝ) ≤
        (W.progression.volume : ℝ) →
      (2 : ℝ) ^ d * (2 * (W.scaleDen : ℝ)) ^ d * (3 : ℝ) ^ d *
          sourceBoxWeightedJohnConstant d * boxFactor < (k : ℝ) * gamma →
      (2 : ℝ) ^ d * (2 * (W.scaleDen : ℝ)) ^ d * (3 : ℝ) ^ d *
          sourceBoxWeightedJohnConstant d *
            (2 * (d : ℝ) * t) * boxFactor < gamma →
      False := by
  rw [sourceBoxWeightedJohnConstant, dif_pos hd]
  exact (Classical.choose_spec (Classical.choose_spec
    (exists_boxWeightedFunctionalSlabContradictionConstants d hd))).2

/-- A single constant dominating all box-weighted John constants up to a
fixed rank ceiling. -/
def sourceBoxWeightedJohnUniformConstant (rankCeiling : ℕ) : ℝ :=
  ∑ d ∈ Finset.range (rankCeiling + 1), sourceBoxWeightedJohnConstant d

theorem sourceBoxWeightedJohnConstant_le_uniform
    {d rankCeiling : ℕ} (hrank : d ≤ rankCeiling) :
    sourceBoxWeightedJohnConstant d ≤
      sourceBoxWeightedJohnUniformConstant rankCeiling := by
  unfold sourceBoxWeightedJohnUniformConstant
  exact Finset.single_le_sum
    (s := Finset.range (rankCeiling + 1))
    (f := sourceBoxWeightedJohnConstant)
    (a := d)
    (fun i _hi ↦ zero_le_one.trans (sourceBoxWeightedJohnConstant_one_le i))
    (by simp only [Finset.mem_range]; omega)

theorem sourceBoxWeightedJohnUniformConstant_one_le
    (rankCeiling : ℕ) :
    1 ≤ sourceBoxWeightedJohnUniformConstant rankCeiling := by
  exact (sourceBoxWeightedJohnConstant_one_le 0).trans
    (sourceBoxWeightedJohnConstant_le_uniform (show 0 ≤ rankCeiling by omega))

/-- The box-weighted contradiction with the rank-uniform constant. -/
theorem sourceBoxWeightedJohnContradiction_uniform
    {d rankCeiling : ℕ} (hd : 0 < d) (hrank : d ≤ rankCeiling) :
    ∀ {s D k loss referenceVolume boxFactor : ℕ}
      {A : Finset (LatticePoint d)}
      (W : CFP.EnhancedCFPWitness A s D k loss)
      (B : IntegerBox d)
      (f : (Fin d → ℝ) →L[ℝ] ℝ) (t gamma : ℝ),
      W.rank = d →
      ConvexDensity.IsConvexBody (OneStepAssembly.boxRealization B) →
      f ≠ 0 → 0 < t →
      (0 : LatticePoint d) ∈ B.carrier →
      W.core ⊆ B.carrier →
      (∀ x ∈ W.core,
        |f (realVector x)| < t * boxCoefficientMass B f) →
      1 ≤ (2 * (d : ℝ) * t) * (B.carrier.card : ℝ) →
      B.carrier.card ≤ boxFactor * referenceVolume →
      0 < referenceVolume → 0 < gamma →
      gamma * (referenceVolume : ℝ) ≤
        (W.progression.volume : ℝ) →
      (2 : ℝ) ^ d * (2 * (W.scaleDen : ℝ)) ^ d * (3 : ℝ) ^ d *
          sourceBoxWeightedJohnUniformConstant rankCeiling * boxFactor <
            (k : ℝ) * gamma →
      (2 : ℝ) ^ d * (2 * (W.scaleDen : ℝ)) ^ d * (3 : ℝ) ^ d *
          sourceBoxWeightedJohnUniformConstant rankCeiling *
            (2 * (d : ℝ) * t) * boxFactor < gamma →
      False := by
  intro s D k loss referenceVolume boxFactor A W B f t gamma hWrank hB hf ht
    hzero hcore hslab hscale hbox href hgamma hlower hlow hfull
  apply sourceBoxWeightedJohnContradiction d hd W B f t gamma hWrank hB hf ht
    hzero hcore hslab hscale hbox href hgamma hlower
  · calc
      (2 : ℝ) ^ d * (2 * (W.scaleDen : ℝ)) ^ d * (3 : ℝ) ^ d *
            sourceBoxWeightedJohnConstant d * boxFactor ≤
          (2 : ℝ) ^ d * (2 * (W.scaleDen : ℝ)) ^ d * (3 : ℝ) ^ d *
            sourceBoxWeightedJohnUniformConstant rankCeiling * boxFactor := by
        gcongr
        exact sourceBoxWeightedJohnConstant_le_uniform hrank
      _ < (k : ℝ) * gamma := hlow
  · calc
      (2 : ℝ) ^ d * (2 * (W.scaleDen : ℝ)) ^ d * (3 : ℝ) ^ d *
            sourceBoxWeightedJohnConstant d * (2 * (d : ℝ) * t) *
              boxFactor ≤
          (2 : ℝ) ^ d * (2 * (W.scaleDen : ℝ)) ^ d * (3 : ℝ) ^ d *
            sourceBoxWeightedJohnUniformConstant rankCeiling *
              (2 * (d : ℝ) * t) * boxFactor := by
        have heta : 0 ≤ 2 * (d : ℝ) * t := by positivity
        gcongr
        exact sourceBoxWeightedJohnConstant_le_uniform hrank
      _ < gamma := hfull

end

end Erdos186.PZ.Intersection
