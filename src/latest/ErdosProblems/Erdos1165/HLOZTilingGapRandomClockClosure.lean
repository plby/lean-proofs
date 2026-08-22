/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/
/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Formal Conjectures Authors
-/

import ErdosProblems.Erdos1165.HLOZTilingGapRandomClockScreen
import ErdosProblems.Erdos1165.HLOZGapRandomClockNumerics

/-!
# Quantitative closure of the genuine all-tiling random-clock screen

The state-dependent tiling screen has the same beta-band return sum as the
canonical screen.  This module eliminates that sum and packages the exact
two remaining probability inputs: the all-tiling lazy-overflow event and the
all-tiling dynamic Proposition 4.8 candidate overflow.
-/

open Filter
open scoped BigOperators ENNReal

namespace Erdos1165.HLOZTilingGapRandomClockClosure

open HLOZGapBetaArithmetic HLOZGapBetaNumerics HLOZGapEstimate
open HLOZGapRandomClockNumerics HLOZGapRandomClockScreen
open HLOZTilingGapRandomClockScreen HLOZPathEvents
open HLOZProposition48Candidates

noncomputable section

abbrev DominoTiling := Tilings.Tiling

/-- Complete all-six tiling closure.  No physical creation time appears in
the finite union or in the numerical multiplicity. -/
theorem hasGapDeficitReturnHarnack_of_tilingLazyRandomClock_bounds
    {c : ℝ} (hc : 0 < c)
    (cap : DominoTiling → ℕ → ℕ)
    (bands : DominoTiling → ℕ → Finset RandomClockBand)
    (index : ℕ → RandomClockBand → ℕ)
    (templates : DominoTiling → Finset (GapScale × ℕ))
    (B : DominoTiling → ℕ)
    (hextract : ∀ t m,
      TilingLazyGoodRandomClockExtraction t
        (onTimeLowGapDeficitExceptionalEvent t m) m
        (levelCutoffTime upperTailDelta m) (cap t m) (bands t m))
    (lazyCost candidateCost : DominoTiling → ℕ → ℝ≥0∞)
    (hlazy : ∀ t, ∀ᶠ m : ℕ in atTop,
      simpleRandomWalk (tilingLazyOverflowExceptionalEvent t m (cap t m)) ≤
        lazyCost t m)
    (hcandidate : ∀ t, ∀ᶠ m : ℕ in atTop,
      simpleRandomWalk
          (tilingRandomClockCandidateOverflow t m
            (levelCutoffTime upperTailDelta m) (bands t m)) ≤
        candidateCost t m)
    (hother : ∀ t, ∀ᶠ m : ℕ in atTop,
      lazyCost t m + candidateCost t m ≤
        ENNReal.ofReal
          (Real.exp (-(2 * c) * Real.log (m : ℝ) ^ 2)))
    (hscale : ∀ t p, p ∈ templates t → p.1 ∈ lowGapMesh)
    (hprojects : ∀ t m band, band ∈ bands t m →
      (band.scale, index m band) ∈ templates t)
    (hcard : ∀ t m, (bands t m).card ≤ B t)
    (hbeta : ∀ t m band, band ∈ bands t m →
      band.beta ≤ deficitExponent48 (meshExponent band.scale)
        (index m band + 1))
    (hreturns : ∀ t m band, band ∈ bands t m →
      requiredReturns48 m
          (deficitExponent48 (meshExponent band.scale) (index m band)) ≤
        band.returns) :
    HLOZUpperEstimates.HasGapDeficitReturnHarnack c := by
  intro t
  have hreturn :=
    eventually_randomClockBand_geometric_sum_le_of_dynamic_bounds
      (bands t) index (templates t) (B t) (c := 2 * c) (by linarith)
      (hscale t) (hprojects t) (hcard t) (hbeta t) (hreturns t)
  have habsorb := eventually_nat_mul_exp_neg_two_log_sq_le_exp_neg 2 hc
  filter_upwards [hlazy t, hcandidate t, hother t, hreturn, habsorb]
    with m hlazyM hcandidateM hotherM hreturnM habsorbM
  let q : ℝ≥0∞ := ENNReal.ofReal
    (Real.exp (-(2 * c) * Real.log (m : ℝ) ^ 2))
  refine (measure_gapEvent_le_tilingLazyRandomClockScreen t
    (onTimeLowGapDeficitExceptionalEvent t m) m
    (levelCutoffTime upperTailDelta m) (cap t m) (bands t m)
    (hextract t m)).trans ?_
  calc
    simpleRandomWalk (tilingLazyOverflowExceptionalEvent t m (cap t m)) +
        (simpleRandomWalk
            (tilingRandomClockCandidateOverflow t m
              (levelCutoffTime upperTailDelta m) (bands t m)) +
          ∑ band ∈ bands t m,
            (candidateBudget48 m band.beta : ℝ≥0∞) *
              Gap.geometricReturnCost
                (HLOZGapMeshEscape.meshPointEscapeChance m band.scale)
                band.returns) ≤
      lazyCost t m +
        (candidateCost t m +
          ∑ band ∈ bands t m,
            (candidateBudget48 m band.beta : ℝ≥0∞) *
              Gap.geometricReturnCost
                (HLOZGapMeshEscape.meshPointEscapeChance m band.scale)
                band.returns) := by gcongr
    _ = (lazyCost t m + candidateCost t m) +
        ∑ band ∈ bands t m,
          (candidateBudget48 m band.beta : ℝ≥0∞) *
            Gap.geometricReturnCost
              (HLOZGapMeshEscape.meshPointEscapeChance m band.scale)
              band.returns := by ac_rfl
    _ ≤ q + q := add_le_add hotherM hreturnM
    _ = (2 : ℝ≥0∞) * q := (two_mul q).symm
    _ ≤ ENNReal.ofReal (Real.exp (-c * Real.log (m : ℝ) ^ 2)) :=
      habsorbM

end

end Erdos1165.HLOZTilingGapRandomClockClosure
