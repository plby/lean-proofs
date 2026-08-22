/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/
/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Formal Conjectures Authors
-/

import ErdosProblems.Erdos1165.HLOZGapBetaNumerics
import ErdosProblems.Erdos1165.HLOZGapRandomClockScreen

/-!
# Numerical closure for the random-clock HLOZ gap screen

This file transports the uniform adjacent-beta-band calculation to the
literal fields of `RandomClockBand`.  Natural thresholds and lazy caps may
vary with `m`; the projection to a fixed finite scale/index template is the
only finiteness needed by the calculation.
-/

open Filter Real
open scoped BigOperators ENNReal

namespace Erdos1165.HLOZGapRandomClockNumerics

open HLOZGapBetaNumerics HLOZGapBetaArithmetic HLOZGapMeshEscape
open HLOZGapRandomClockScreen HLOZPathEvents HLOZProposition48Candidates
open ScreeningInstantiation

noncomputable section

/-- The complete geometric-return sum for a dynamic family of literal
random-clock bands.  The two field equalities are the exact deterministic
output required from beta-band extraction. -/
theorem eventually_randomClockBand_geometric_sum_le
    (bands : ℕ → Finset RandomClockBand)
    (index : RandomClockBand → ℕ)
    (templates : Finset (GapScale × ℕ)) (B : ℕ)
    {c : ℝ} (hc : 0 < c)
    (hscale : ∀ p ∈ templates, p.1 ∈ lowGapMesh)
    (hprojects : ∀ m band, band ∈ bands m →
      (band.scale, index band) ∈ templates)
    (hcard : ∀ m, (bands m).card ≤ B)
    (hbeta : ∀ m band, band ∈ bands m →
      band.beta = deficitExponent48 (meshExponent band.scale)
        (index band + 1))
    (hreturns : ∀ m band, band ∈ bands m →
      band.returns = requiredReturns48 m
        (deficitExponent48 (meshExponent band.scale) (index band))) :
    ∀ᶠ m : ℕ in atTop,
      ∑ band ∈ bands m,
        (candidateBudget48 m band.beta : ℝ≥0∞) *
          Gap.geometricReturnCost (meshPointEscapeChance m band.scale)
            band.returns ≤
        ENNReal.ofReal (Real.exp (-c * Real.log (m : ℝ) ^ 2)) := by
  have hcanonical :=
    eventually_sum_dynamic_adjacent_deficitBand_geometric_cost_le
      bands RandomClockBand.scale index templates B hc
      (fun p hp ↦ meshExponent_add_delta_le_kappaOne_of_mem_lowGapMesh
        (hscale p hp))
      hprojects hcard
  filter_upwards [hcanonical] with m hcanonicalM
  calc
    ∑ band ∈ bands m,
        (candidateBudget48 m band.beta : ℝ≥0∞) *
          Gap.geometricReturnCost (meshPointEscapeChance m band.scale)
            band.returns =
      ∑ band ∈ bands m,
        ((candidateBudget48 m
            (deficitExponent48 (meshExponent band.scale)
              (index band + 1)) : ℕ) : ℝ≥0∞) *
          Gap.geometricReturnCost (meshPointEscapeChance m band.scale)
            (requiredReturns48 m
              (deficitExponent48 (meshExponent band.scale) (index band))) := by
      apply Finset.sum_congr rfl
      intro band hband
      rw [hbeta m band hband, hreturns m band hband]
    _ ≤ ENNReal.ofReal (Real.exp (-c * Real.log (m : ℝ) ^ 2)) :=
      hcanonicalM

/-- Extraction-friendly form of the complete return-cost estimate.  A real
path decomposition naturally gives an upper beta endpoint and a lower return
count, rather than definitional equalities.  This formulation also covers the
terminal band, whose candidate exponent is clipped at `1` after the next
affine beta-mesh point has crossed `1`. -/
theorem eventually_randomClockBand_geometric_sum_le_of_bounds
    (bands : ℕ → Finset RandomClockBand)
    (index : RandomClockBand → ℕ)
    (templates : Finset (GapScale × ℕ)) (B : ℕ)
    {c : ℝ} (hc : 0 < c)
    (hscale : ∀ p ∈ templates, p.1 ∈ lowGapMesh)
    (hprojects : ∀ m band, band ∈ bands m →
      (band.scale, index band) ∈ templates)
    (hcard : ∀ m, (bands m).card ≤ B)
    (hbeta : ∀ m band, band ∈ bands m →
      band.beta ≤ deficitExponent48 (meshExponent band.scale)
        (index band + 1))
    (hreturns : ∀ m band, band ∈ bands m →
      requiredReturns48 m
          (deficitExponent48 (meshExponent band.scale) (index band)) ≤
        band.returns) :
    ∀ᶠ m : ℕ in atTop,
      ∑ band ∈ bands m,
        (candidateBudget48 m band.beta : ℝ≥0∞) *
          Gap.geometricReturnCost (meshPointEscapeChance m band.scale)
            band.returns ≤
        ENNReal.ofReal (Real.exp (-c * Real.log (m : ℝ) ^ 2)) := by
  have hcanonical :=
    eventually_sum_dynamic_adjacent_deficitBand_geometric_cost_le
      bands RandomClockBand.scale index templates B hc
      (fun p hp ↦ meshExponent_add_delta_le_kappaOne_of_mem_lowGapMesh
        (hscale p hp))
      hprojects hcard
  filter_upwards [hcanonical, eventually_ge_atTop 1] with m hcanonicalM hm
  calc
    ∑ band ∈ bands m,
        (candidateBudget48 m band.beta : ℝ≥0∞) *
          Gap.geometricReturnCost (meshPointEscapeChance m band.scale)
            band.returns ≤
      ∑ band ∈ bands m,
        ((candidateBudget48 m
            (deficitExponent48 (meshExponent band.scale)
              (index band + 1)) : ℕ) : ℝ≥0∞) *
          Gap.geometricReturnCost (meshPointEscapeChance m band.scale)
            (requiredReturns48 m
              (deficitExponent48 (meshExponent band.scale) (index band))) := by
      apply Finset.sum_le_sum
      intro band hband
      apply mul_le_mul
      · exact_mod_cast candidateBudget48_mono_beta hm (hbeta m band hband)
      · exact geometricReturnCost_anti_returns
          (meshPointEscapeChance_pos m band.scale).le
          (meshPointEscapeChance_le_one m band.scale)
          (hreturns m band hband)
      · exact bot_le
      · exact bot_le
    _ ≤ ENNReal.ofReal (Real.exp (-c * Real.log (m : ℝ) ^ 2)) :=
      hcanonicalM

/-- Level-dependent decoding form of the extraction-friendly estimate.  It
is the appropriate endpoint for a `Finset.image` construction of literal
random-clock bands, since the source beta tag need not be recoverable from a
band uniformly in `m`. -/
theorem eventually_randomClockBand_geometric_sum_le_of_dynamic_bounds
    (bands : ℕ → Finset RandomClockBand)
    (index : ℕ → RandomClockBand → ℕ)
    (templates : Finset (GapScale × ℕ)) (B : ℕ)
    {c : ℝ} (hc : 0 < c)
    (hscale : ∀ p ∈ templates, p.1 ∈ lowGapMesh)
    (hprojects : ∀ m band, band ∈ bands m →
      (band.scale, index m band) ∈ templates)
    (hcard : ∀ m, (bands m).card ≤ B)
    (hbeta : ∀ m band, band ∈ bands m →
      band.beta ≤ deficitExponent48 (meshExponent band.scale)
        (index m band + 1))
    (hreturns : ∀ m band, band ∈ bands m →
      requiredReturns48 m
          (deficitExponent48 (meshExponent band.scale) (index m band)) ≤
        band.returns) :
    ∀ᶠ m : ℕ in atTop,
      ∑ band ∈ bands m,
        (candidateBudget48 m band.beta : ℝ≥0∞) *
          Gap.geometricReturnCost (meshPointEscapeChance m band.scale)
            band.returns ≤
        ENNReal.ofReal (Real.exp (-c * Real.log (m : ℝ) ^ 2)) := by
  have hcanonical :=
    eventually_sum_dynamic_indexed_deficitBand_geometric_cost_le
      bands (fun _ ↦ RandomClockBand.scale) index templates B hc
      (fun p hp ↦ meshExponent_add_delta_le_kappaOne_of_mem_lowGapMesh
        (hscale p hp))
      hprojects hcard
  filter_upwards [hcanonical, eventually_ge_atTop 1] with m hcanonicalM hm
  calc
    ∑ band ∈ bands m,
        (candidateBudget48 m band.beta : ℝ≥0∞) *
          Gap.geometricReturnCost (meshPointEscapeChance m band.scale)
            band.returns ≤
      ∑ band ∈ bands m,
        ((candidateBudget48 m
            (deficitExponent48 (meshExponent band.scale)
              (index m band + 1)) : ℕ) : ℝ≥0∞) *
          Gap.geometricReturnCost (meshPointEscapeChance m band.scale)
            (requiredReturns48 m
              (deficitExponent48 (meshExponent band.scale)
                (index m band))) := by
      apply Finset.sum_le_sum
      intro band hband
      apply mul_le_mul
      · exact_mod_cast candidateBudget48_mono_beta hm (hbeta m band hband)
      · exact geometricReturnCost_anti_returns
          (meshPointEscapeChance_pos m band.scale).le
          (meshPointEscapeChance_le_one m band.scale)
          (hreturns m band hband)
      · exact bot_le
      · exact bot_le
    _ ≤ ENNReal.ofReal (Real.exp (-c * Real.log (m : ℝ) ^ 2)) :=
      hcanonicalM

end

end Erdos1165.HLOZGapRandomClockNumerics
