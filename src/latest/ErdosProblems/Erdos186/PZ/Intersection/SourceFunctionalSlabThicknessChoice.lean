/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.PZ.Intersection.SourceFunctionalSlabNumerics

/-!
# A uniform thickness for the source functional slab

The forward and reverse slab constants, and every rank below a fixed ceiling,
are absorbed into one finite number.  Dividing `gamma` by twice that number
plus one gives a common positive thickness and leaves a strict margin in both
full-rank inequalities.
-/

namespace Erdos186.PZ.Intersection

noncomputable section

set_option autoImplicit false

/-- Common thickness used for the forward and reverse source slabs. -/
def sourceFunctionalSlabThickness {beta eta : ℝ}
    (context : Reduction.HigherDimensionalContext beta eta)
    (rankCeiling : ℕ) (forwardConstant reverseConstant gamma : ℝ) : ℝ :=
  gamma / (2 * (sourceFunctionalSlabTermBound context rankCeiling
    forwardConstant reverseConstant + 1))

theorem sourceFunctionalSlabThickness_pos {beta eta : ℝ}
    {context : Reduction.HigherDimensionalContext beta eta}
    {rankCeiling : ℕ} {forwardConstant reverseConstant gamma : ℝ}
    (hforward : 0 ≤ forwardConstant) (hreverse : 0 ≤ reverseConstant)
    (hgamma : 0 < gamma) :
    0 < sourceFunctionalSlabThickness context rankCeiling
      forwardConstant reverseConstant gamma := by
  unfold sourceFunctionalSlabThickness
  have hbound := sourceFunctionalSlabTermBound_nonneg
    (context := context) (rankCeiling := rankCeiling) hforward hreverse
  exact div_pos hgamma (mul_pos (by norm_num) (by linarith))

/-- The expanded full-rank expression in the slab-cardinality API is exactly
the fixed full term times the chosen thickness. -/
theorem sourceFunctionalSlabFullExpression_eq {beta eta : ℝ}
    {context : Reduction.HigherDimensionalContext beta eta}
    (constant t : ℝ) (r : ℕ) :
    (2 : ℝ) ^ r * (2 * (context.scaleDen r : ℝ)) ^ r *
          (3 : ℝ) ^ r * constant * (2 * (r : ℝ) * t) *
          ((((2 * context.scaleDen r + 1) ^ r * 2 ^ r : ℕ) : ℝ)) =
      sourceFunctionalSlabFullTerm context constant r * t := by
  unfold sourceFunctionalSlabFullTerm sourceFunctionalSlabFixedTerm
  ring

theorem sourceFunctionalSlabFullTerm_mul_thickness_lt {beta eta : ℝ}
    {context : Reduction.HigherDimensionalContext beta eta}
    {rankCeiling r : ℕ} {forwardConstant reverseConstant gamma : ℝ}
    (hforward : 0 ≤ forwardConstant) (hreverse : 0 ≤ reverseConstant)
    (hgamma : 0 < gamma) (hrank : r ≤ rankCeiling) :
    sourceFunctionalSlabFullTerm context forwardConstant r *
        sourceFunctionalSlabThickness context rankCeiling
          forwardConstant reverseConstant gamma < gamma := by
  let B := sourceFunctionalSlabTermBound context rankCeiling
    forwardConstant reverseConstant
  have hB : 0 ≤ B := sourceFunctionalSlabTermBound_nonneg
    (context := context) hforward hreverse
  have hterm : sourceFunctionalSlabFullTerm context forwardConstant r ≤ B :=
    sourceFunctionalSlabFullTerm_le_bound hforward hreverse hrank
  have hdenom : 0 < 2 * (B + 1) := by positivity
  have ht : sourceFunctionalSlabThickness context rankCeiling
      forwardConstant reverseConstant gamma = gamma / (2 * (B + 1)) := rfl
  rw [ht]
  calc
    sourceFunctionalSlabFullTerm context forwardConstant r *
          (gamma / (2 * (B + 1))) ≤
        B * (gamma / (2 * (B + 1))) := by
      gcongr
    _ = gamma * (B / (2 * (B + 1))) := by ring
    _ < gamma * 1 := by
      apply mul_lt_mul_of_pos_left _ hgamma
      exact (div_lt_one hdenom).2 (by linarith)
    _ = gamma := by ring

theorem sourceFunctionalSlabReverseFullTerm_mul_thickness_lt
    {beta eta : ℝ}
    {context : Reduction.HigherDimensionalContext beta eta}
    {rankCeiling r : ℕ} {forwardConstant reverseConstant gamma : ℝ}
    (hforward : 0 ≤ forwardConstant) (hreverse : 0 ≤ reverseConstant)
    (hgamma : 0 < gamma) (hrank : r ≤ rankCeiling) :
    sourceFunctionalSlabFullTerm context reverseConstant r *
        sourceFunctionalSlabThickness context rankCeiling
          forwardConstant reverseConstant gamma < gamma := by
  let B := sourceFunctionalSlabTermBound context rankCeiling
    forwardConstant reverseConstant
  have hB : 0 ≤ B := sourceFunctionalSlabTermBound_nonneg
    (context := context) hforward hreverse
  have hterm : sourceFunctionalSlabFullTerm context reverseConstant r ≤ B :=
    sourceFunctionalSlabReverseFullTerm_le_bound hforward hreverse hrank
  have hdenom : 0 < 2 * (B + 1) := by positivity
  have ht : sourceFunctionalSlabThickness context rankCeiling
      forwardConstant reverseConstant gamma = gamma / (2 * (B + 1)) := rfl
  rw [ht]
  calc
    sourceFunctionalSlabFullTerm context reverseConstant r *
          (gamma / (2 * (B + 1))) ≤
        B * (gamma / (2 * (B + 1))) := by
      gcongr
    _ = gamma * (B / (2 * (B + 1))) := by ring
    _ < gamma * 1 := by
      apply mul_lt_mul_of_pos_left _ hgamma
      exact (div_lt_one hdenom).2 (by linarith)
    _ = gamma := by ring

end

end Erdos186.PZ.Intersection
