/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/
/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Formal Conjectures Authors
-/

import ErdosProblems.Erdos1165.HLOZStoppedLazyLawClosure
import ErdosProblems.Erdos1165.HLOZLowScaleCandidateOverflow
import ErdosProblems.Erdos1165.HLOZGapRandomClockClosure

/-!
# Product-data closure of the low-gap exceptional estimate

This module eliminates both path-probability premises from the low-gap
random-clock endgame.  Lazy overflow is bounded by exact all-six variable-time
coordinate product specifications.  Candidate overflow is bounded by the
closed stopped one-point theorem and literal per-band balance/random-total
product laws.  The random-clock return contribution is discharged by the
adjacent-beta numerical theorem.

The only quantitative premise left is an estimate on the sum of the explicit
per-band product coefficients.  It mentions no path event or random-walk
probability and is the intended endpoint of the pending all-six finite-product
calculation.
-/

open Filter MeasureTheory Set
open scoped BigOperators ENNReal

namespace Erdos1165.HLOZLowGapProductEndgame

open HLOZGapBetaArithmetic HLOZGapBetaNumerics HLOZGapEstimate
open HLOZGapRandomClockClosure HLOZGapRandomClockScreen HLOZPathEvents
open HLOZLazyOverflow HLOZLowScaleCandidateOverflow
open HLOZProposition48Candidates HLOZStoppedLazyLawClosure
open ExternalProposition44 ScreeningInstantiation

noncomputable section

/-- The upper-cutoff used by the random-clock extraction is definitionally
the cap used by the stopped one-point theorem. -/
theorem levelCutoffTime_upperTailDelta_eq_hlozCutoff44 (m : ℕ) :
    levelCutoffTime upperTailDelta m = hlozCutoff44 m := by
  simp [hlozCutoff44, hlozDelta44, upperTailDelta]

/-- Full low-gap closure for all six tilings.  There is no assumed lazy-event
or candidate-overflow probability bound. -/
theorem hasGapDeficitReturnHarnack_of_stoppedProductData
    {c : ℝ} (hc : 0 < c)
    (cap : ℕ → ℕ) (lazyData : StoppedLazyTilingProductFamily cap)
    (bands : DominoTiling → ℕ → Finset RandomClockBand)
    (index : ℕ → RandomClockBand → ℕ)
    (templates : DominoTiling → Finset (GapScale × ℕ))
    (B : DominoTiling → ℕ)
    (hextract : ∀ t m,
      LazyGoodRandomClockExtraction
        (onTimeLowGapDeficitExceptionalEvent t m) m
        (levelCutoffTime upperTailDelta m) (cap m) (bands t m))
    (screen : ∀ t m band,
      BandProductScreen m (levelCutoffTime upperTailDelta m) band)
    (hthreshold : ∀ t, ∀ᶠ m : ℕ in atTop,
      ∀ band ∈ bands t m, hlozOnePointLevel44 m ≤ band.externalThreshold)
    (hbetaLower : ∀ t m band, band ∈ bands t m →
      kappaOne ≤ band.beta)
    (hproductCost : ∀ t, ∀ᶠ m : ℕ in atTop,
      ∑ band ∈ bands t m, bandOverflowCoefficient (screen t m band) ≤
        ENNReal.ofReal
          (Real.exp (-(4 * c) * Real.log (m : ℝ) ^ 2)))
    (hscale : ∀ t p, p ∈ templates t → p.1 ∈ lowGapMesh)
    (hprojects : ∀ t m band, band ∈ bands t m →
      (band.scale, index m band) ∈ templates t)
    (hcard : ∀ t m, (bands t m).card ≤ B t)
    (hbetaUpper : ∀ t m band, band ∈ bands t m →
      band.beta ≤ deficitExponent48 (meshExponent band.scale)
        (index m band + 1))
    (hreturns : ∀ t m band, band ∈ bands t m →
      requiredReturns48 m
          (deficitExponent48 (meshExponent band.scale) (index m band)) ≤
        band.returns) :
    HLOZUpperEstimates.HasGapDeficitReturnHarnack c := by
  let laws := stoppedLazyLawFamilyOfTilingProductFamily lazyData
  let overflowCost : DominoTiling → ℕ → ℝ≥0∞ := fun t m ↦
    ∑ band ∈ bands t m, bandOverflowCoefficient (screen t m band)
  have hcutoff : ∀ᶠ m : ℕ in atTop,
      levelCutoffTime upperTailDelta m ≤ hlozCutoff44 m := by
    filter_upwards [] with m
    rw [levelCutoffTime_upperTailDelta_eq_hlozCutoff44]
  have hoverflow : ∀ t, ∀ᶠ m : ℕ in atTop,
      simpleRandomWalk
          (candidateOverflow (bands t m)
            (randomClockBandSites m (levelCutoffTime upperTailDelta m))
            (fun band ↦ candidateBudget48 m band.beta)) ≤
        overflowCost t m := by
    intro t
    exact eventually_simpleRandomWalk_randomClockCandidateOverflow_le_sum
      (fun m ↦ levelCutoffTime upperTailDelta m) (bands t) hcutoff
      (hthreshold t) (hbetaLower t) (screen t)
  have hlazy : ∀ᶠ m : ℕ in atTop,
      stoppedLazyOverflowCost laws m ≤
        ENNReal.ofReal
          (Real.exp (-(4 * c) * Real.log (m : ℝ) ^ 2)) := by
    exact hasStoppedLazyOverflowRate_of_tilingProductFamily lazyData (4 * c)
  have habsorb := eventually_nat_mul_exp_neg_two_log_sq_le_exp_neg
    2 (c := 2 * c) (by linarith)
  have hother : ∀ t, ∀ᶠ m : ℕ in atTop,
      stoppedLazyOverflowCost laws m + overflowCost t m ≤
        ENNReal.ofReal
          (Real.exp (-(2 * c) * Real.log (m : ℝ) ^ 2)) := by
    intro t
    filter_upwards [hlazy, hproductCost t, habsorb] with m hlazyM hproductM habsorbM
    let q : ℝ≥0∞ := ENNReal.ofReal
      (Real.exp (-(4 * c) * Real.log (m : ℝ) ^ 2))
    calc
      stoppedLazyOverflowCost laws m + overflowCost t m ≤ q + q :=
        add_le_add hlazyM hproductM
      _ = (2 : ℝ≥0∞) * q := (two_mul q).symm
      _ ≤ ENNReal.ofReal
          (Real.exp (-(2 * c) * Real.log (m : ℝ) ^ 2)) := by
        dsimp [q]
        convert habsorbM using 1 <;> ring
  exact hasGapDeficitReturnHarnack_of_lazy_randomClock_bounds hc cap laws
    bands index templates B hextract overflowCost hoverflow hother hscale
    hprojects hcard hbetaUpper hreturns

end

end Erdos1165.HLOZLowGapProductEndgame
