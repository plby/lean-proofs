/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/
/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Formal Conjectures Authors
-/

import ErdosProblems.Erdos1165.HLOZGapRandomClockNumerics
import ErdosProblems.Erdos1165.HLOZLazyOverflow

/-!
# Quantitative closure of the low-scale random-clock gap screen

This module combines the literal lazy-bad/lazy-good random-clock screen with
the adjacent-beta-band calculation.  The geometric-return sum is completely
discharged here, including a clipped terminal beta band via upper/lower band
bounds.  The remaining inputs are precisely the pathwise band extraction and
the two stopped product-law costs (lazy overflow and candidate overflow).
-/

open Filter
open scoped BigOperators ENNReal

namespace Erdos1165.HLOZGapRandomClockClosure

open HLOZGapBetaArithmetic HLOZGapBetaNumerics HLOZGapEstimate
open HLOZGapRandomClockNumerics
open HLOZGapRandomClockScreen HLOZLazyOverflow HLOZPathEvents
open HLOZProposition48Candidates

noncomputable section

/-- For one tiling, the low-scale gap estimate after the geometric-return
cost has been eliminated.  Both other exceptional costs are allowed to share
one rate bound; the spare factor of two in their exponent absorbs their sum
with the return cost. -/
theorem eventually_measure_onTimeLowGapDeficitExceptionalEvent_le_exp
    {c : ℝ} (hc : 0 < c) (t : DominoTiling)
    (cap : ℕ → ℕ) (laws : StoppedLazyLawFamily cap)
    (bands : ℕ → Finset RandomClockBand)
    (index : ℕ → RandomClockBand → ℕ)
    (templates : Finset (GapScale × ℕ)) (B : ℕ)
    (hextract : ∀ m,
      LazyGoodRandomClockExtraction
        (onTimeLowGapDeficitExceptionalEvent t m) m
        (levelCutoffTime upperTailDelta m) (cap m) (bands m))
    (overflowCost : ℕ → ℝ≥0∞)
    (hoverflow : ∀ᶠ m : ℕ in atTop,
      simpleRandomWalk
          (candidateOverflow (bands m)
            (randomClockBandSites m (levelCutoffTime upperTailDelta m))
            (fun band ↦ candidateBudget48 m band.beta)) ≤
        overflowCost m)
    (hother : ∀ᶠ m : ℕ in atTop,
      stoppedLazyOverflowCost laws m + overflowCost m ≤
        ENNReal.ofReal
          (Real.exp (-(2 * c) * Real.log (m : ℝ) ^ 2)))
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
      simpleRandomWalk (onTimeLowGapDeficitExceptionalEvent t m) ≤
        ENNReal.ofReal (Real.exp (-c * Real.log (m : ℝ) ^ 2)) := by
  have hreturn :=
    eventually_randomClockBand_geometric_sum_le_of_dynamic_bounds
      bands index templates B (c := 2 * c) (by linarith) hscale hprojects
      hcard hbeta hreturns
  have habsorb :=
    eventually_nat_mul_exp_neg_two_log_sq_le_exp_neg 2 hc
  have hnumeric : ∀ᶠ m : ℕ in atTop,
      stoppedLazyOverflowCost laws m +
          (overflowCost m +
            ∑ band ∈ bands m,
              (candidateBudget48 m band.beta : ℝ≥0∞) *
                Gap.geometricReturnCost
                  (HLOZGapMeshEscape.meshPointEscapeChance m band.scale)
                  band.returns) ≤
        ENNReal.ofReal (Real.exp (-c * Real.log (m : ℝ) ^ 2)) := by
    filter_upwards [hother, hreturn, habsorb] with m hotherM hreturnM habsorbM
    let q : ℝ≥0∞ := ENNReal.ofReal
      (Real.exp (-(2 * c) * Real.log (m : ℝ) ^ 2))
    calc
      stoppedLazyOverflowCost laws m +
          (overflowCost m +
            ∑ band ∈ bands m,
              (candidateBudget48 m band.beta : ℝ≥0∞) *
                Gap.geometricReturnCost
                  (HLOZGapMeshEscape.meshPointEscapeChance m band.scale)
                  band.returns) =
        (stoppedLazyOverflowCost laws m + overflowCost m) +
          ∑ band ∈ bands m,
            (candidateBudget48 m band.beta : ℝ≥0∞) *
              Gap.geometricReturnCost
                (HLOZGapMeshEscape.meshPointEscapeChance m band.scale)
                band.returns := by ac_rfl
      _ ≤ q + q := add_le_add hotherM hreturnM
      _ = (2 : ℝ≥0∞) * q := (two_mul q).symm
      _ ≤ ENNReal.ofReal (Real.exp (-c * Real.log (m : ℝ) ^ 2)) :=
        habsorbM
  exact eventually_measure_gapEvent_le_exp_of_lazy_randomClockScreen
    c (fun m ↦ onTimeLowGapDeficitExceptionalEvent t m) cap laws bands
    hextract overflowCost hoverflow hnumeric

/-- All-tiling packaging of the preceding theorem in exactly the interface
consumed by the HLOZ upper assembly. -/
theorem hasGapDeficitReturnHarnack_of_lazy_randomClock_bounds
    {c : ℝ} (hc : 0 < c)
    (cap : ℕ → ℕ) (laws : StoppedLazyLawFamily cap)
    (bands : DominoTiling → ℕ → Finset RandomClockBand)
    (index : ℕ → RandomClockBand → ℕ)
    (templates : DominoTiling → Finset (GapScale × ℕ))
    (B : DominoTiling → ℕ)
    (hextract : ∀ t m,
      LazyGoodRandomClockExtraction
        (onTimeLowGapDeficitExceptionalEvent t m) m
        (levelCutoffTime upperTailDelta m) (cap m) (bands t m))
    (overflowCost : DominoTiling → ℕ → ℝ≥0∞)
    (hoverflow : ∀ t, ∀ᶠ m : ℕ in atTop,
      simpleRandomWalk
          (candidateOverflow (bands t m)
            (randomClockBandSites m (levelCutoffTime upperTailDelta m))
            (fun band ↦ candidateBudget48 m band.beta)) ≤
        overflowCost t m)
    (hother : ∀ t, ∀ᶠ m : ℕ in atTop,
      stoppedLazyOverflowCost laws m + overflowCost t m ≤
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
  exact eventually_measure_onTimeLowGapDeficitExceptionalEvent_le_exp
    hc t cap laws (bands t) index (templates t) (B t) (hextract t)
    (overflowCost t) (hoverflow t) (hother t) (hscale t)
    (hprojects t) (hcard t) (hbeta t) (hreturns t)

end

end Erdos1165.HLOZGapRandomClockClosure
