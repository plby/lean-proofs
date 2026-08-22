/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/
/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Formal Conjectures Authors
-/

import ErdosProblems.Erdos1165.HLOZLazyOverflowClosure

/-!
# The low-scale Proposition 4.8 candidate-overflow coefficient

This module assembles the canonical stopped one-point estimate with the
deterministic-cap domination of the genuine random-clock candidates.  The
one-point estimate is uniform in the stopped clock, its threshold and the
orientation.  Consequently it may be summed over a finite family of
level-dependent HLOZ bands without conditioning on a physical creation time.

The only data still exposed by the final coefficient are the literal
negative-binomial balance law and the random-total adjacent-shell product
law.  In particular, there is no stopped external-word disintegration
premise and no premise which is itself a candidate-overflow inequality.
-/

open Filter MeasureTheory Set
open scoped BigOperators ENNReal

namespace Erdos1165.HLOZLowScaleCandidateOverflow

open ExternalStoppedWeightedOnePoint ExternalWeightedOnePointCanonical
open ExternalThickCount ExternalProposition44
open HLOZDynamicStoppedOnePointClosure HLOZDynamicThresholdedScreening
open HLOZLazyOverflow HLOZLazyOverflowClosure
open HLOZGapRandomClockScreen HLOZGapEstimate HLOZPathEvents
open HLOZProposition48Candidates HLOZThresholdedShellScreening
open NearFavoriteThresholded ScreeningInstantiation
open LazyDecomposition

noncomputable section

/-- The canonical stopped one-point estimate at one level, uniformly over
both orientations and over every bounded stopped clock and threshold. -/
def CanonicalStoppedOnePointAt (m : ℕ) : Prop :=
  ∀ (o : Orientation) (tau : WalkPath → ℕ) (threshold : ℕ),
    hlozOnePointLevel44 m ≤ threshold →
    (∀ s, tau s ≤ hlozCutoff44 m) →
    (∀ x, MeasurableSet (stoppedOrientedLargeEvent o tau threshold x)) →
    ∀ x : Point,
      simpleRandomWalk
          (candidateEvent (stoppedCapVisitedSites o m)
            (stoppedOrientedLargeEvent o tau threshold) x) ≤
        hlozOnePointRate44 m * simpleRandomWalk
          (memberEvent (stoppedCapVisitedSites o m) x)

/-- The large-level condition needed for the elementary geometric candidate
budget is independent of the band exponent. -/
def CandidateBudgetArithmeticAt (m : ℕ) : Prop :=
  ∀ beta : ℝ, kappaOne ≤ beta →
    geometricCandidateBudget48 m beta ≤ candidateBudget48 m beta

theorem eventually_canonicalStoppedOnePointAt :
    ∀ᶠ m : ℕ in atTop, CanonicalStoppedOnePointAt m := by
  filter_upwards
      [eventually_simpleRandomWalk_hloz_stoppedLarge_weightedOneSite44
        (.even : Orientation),
       eventually_simpleRandomWalk_hloz_stoppedLarge_weightedOneSite44
        (.shifted : Orientation)] with m heven hshifted
  intro o tau threshold hthreshold htau hlarge x
  cases o with
  | even =>
      change simpleRandomWalk
          (candidateEvent
            (fun s ↦ orientedExternalVisitedSites .even s (hlozCutoff44 m))
            (stoppedOrientedLargeEvent .even tau threshold) x) ≤
        hlozOnePointRate44 m * simpleRandomWalk
          (memberEvent
            (fun s ↦ orientedExternalVisitedSites .even s (hlozCutoff44 m)) x)
      exact heven tau threshold hthreshold htau hlarge x
  | shifted =>
      change simpleRandomWalk
          (candidateEvent
            (fun s ↦ orientedExternalVisitedSites .shifted s (hlozCutoff44 m))
            (stoppedOrientedLargeEvent .shifted tau threshold) x) ≤
        hlozOnePointRate44 m * simpleRandomWalk
          (memberEvent
            (fun s ↦ orientedExternalVisitedSites .shifted s (hlozCutoff44 m)) x)
      exact hshifted tau threshold hthreshold htau hlarge x

theorem eventually_candidateBudgetArithmeticAt :
    ∀ᶠ m : ℕ in atTop, CandidateBudgetArithmeticAt m := by
  have hlogT : Tendsto (fun m : ℕ ↦ Real.log (m : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [eventually_ge_atTop 1,
      hlogT.eventually (eventually_ge_atTop 1)] with m hm hlog
  intro beta hbeta
  exact geometricCandidateBudget48_le_candidateBudget48 hm hbeta
    (by nlinarith [sq_nonneg (Real.log (m : ℝ))])

/-- Literal adjacent-shell data for one random-clock band.  Both fields are
finite product laws; neither is a path-level candidate-overflow estimate. -/
structure BandProductScreen (m cutoff : ℕ) (band : RandomClockBand) where
  balanced : ℕ → Set WalkPath
  balanceLaw : ∀ j,
    GeometricBalanceLaw (Site := Point) simpleRandomWalk (balanced j) m
  productLaw : RandomTotalProductLaw simpleRandomWalk balanced
    (dynamicShellOccupancy (stoppedCapVisitedSites band.orientation m)
      (stoppedOrientedLargeEvent band.orientation
        (pathTruncatedLevelTime m band.oldRank cutoff)
        band.externalThreshold)
      (randomClockDistinguishedSites m cutoff band)
      (randomClockTotalLocalTime m cutoff band)
      m (shellWidth48 m))
    (geometricShellThreshold (initialBudget48 m) shellGrowth48)
    shellGrowth48 (shellCount48 m band.beta)

/-- The completely explicit coefficient delivered by the stopped one-point,
balance and adjacent-shell product estimates for one band. -/
noncomputable def bandOverflowCoefficient
    {m cutoff : ℕ} {band : RandomClockBand}
    (screen : BandProductScreen m cutoff band) : ℝ≥0∞ :=
  ENNReal.ofReal
    (((hlozOnePointRate44 m *
          ((hlozCutoff44 m + 1 : ℕ) : ℝ≥0∞) /
          initialBudget48 m).toReal) +
      ∑ j ∈ Finset.range (shellCount48 m band.beta - 1),
        ((((screen.balanceLaw j).budget : ℝ≥0∞) *
            (ENNReal.ofReal (Real.exp (-17 * balanceRateScale m)) +
              ENNReal.ofReal
                (Real.exp (-17 * balanceRateScale m)))).toReal +
          ∑ total ∈ Finset.range (screen.productLaw.totalBound j + 1),
            screen.productLaw.fixedCost j total))

theorem simpleRandomWalk_randomClockDominatingBandOverflow_le
    {m cutoff : ℕ} {band : RandomClockBand}
    (hone : CanonicalStoppedOnePointAt m)
    (hbudget : CandidateBudgetArithmeticAt m)
    (hcutoff : cutoff ≤ hlozCutoff44 m)
    (hthreshold : hlozOnePointLevel44 m ≤ band.externalThreshold)
    (hbeta : kappaOne ≤ band.beta)
    (screen : BandProductScreen m cutoff band) :
    simpleRandomWalk (randomClockDominatingBandOverflow m cutoff band) ≤
      bandOverflowCoefficient screen := by
  have htau : ∀ s,
      pathTruncatedLevelTime m band.oldRank cutoff s ≤ hlozCutoff44 m :=
    fun s ↦ (pathTruncatedLevelTime_le m band.oldRank cutoff s).trans hcutoff
  have hlarge : ∀ x, MeasurableSet
      (stoppedOrientedLargeEvent band.orientation
        (pathTruncatedLevelTime m band.oldRank cutoff)
        band.externalThreshold x) := by
    intro x
    simpa only [← randomClockExternalLargeEvent_eq_stopped] using
      measurableSet_randomClockExternalLargeEvent m cutoff band x
  simpa only [randomClockDominatingBandOverflow,
      randomClockDominatingBandSites, dynamicStoppedCandidateOverflow48,
      bandOverflowCoefficient] using
    simpleRandomWalk_dynamicStoppedCandidateOverflow48_le_thresholded
      (Site := Point) (stoppedCapVisitedSites band.orientation m)
      (stoppedOrientedLargeEvent band.orientation
        (pathTruncatedLevelTime m band.oldRank cutoff)
        band.externalThreshold)
      (randomClockDistinguishedSites m cutoff band)
      (randomClockTotalLocalTime m cutoff band)
      m band.beta screen.balanced (hlozOnePointRate44 m)
      (((hlozCutoff44 m + 1 : ℕ) : ℝ≥0∞))
      (hlozOnePointRate44_ne_top m) ENNReal.coe_ne_top
      (hbudget band.beta hbeta)
      (fun x ↦ measurableSet_member_orientedExternalVisitedSites
        band.orientation (hlozCutoff44 m) x)
      hlarge (hone band.orientation
        (pathTruncatedLevelTime m band.oldRank cutoff)
        band.externalThreshold hthreshold htau hlarge)
      (by
        simpa only [HLOZDynamicStoppedOnePointClosure.stoppedCapVisitedSites] using
          lintegral_orientedExternalVisitedSites_card_le
            band.orientation (hlozCutoff44 m))
      screen.balanceLaw screen.productLaw

/-- The genuine random-clock overflow over a finite, level-dependent band
family is bounded by the sum of the explicit per-band coefficients. -/
theorem eventually_simpleRandomWalk_randomClockCandidateOverflow_le_sum
    (cutoff : ℕ → ℕ) (bands : ℕ → Finset RandomClockBand)
    (hcutoff : ∀ᶠ m : ℕ in atTop, cutoff m ≤ hlozCutoff44 m)
    (hthreshold : ∀ᶠ m : ℕ in atTop,
      ∀ band ∈ bands m, hlozOnePointLevel44 m ≤ band.externalThreshold)
    (hbeta : ∀ m band, band ∈ bands m → kappaOne ≤ band.beta)
    (screen : ∀ m band, BandProductScreen m (cutoff m) band) :
    ∀ᶠ m : ℕ in atTop,
      simpleRandomWalk
          (candidateOverflow (bands m) (randomClockBandSites m (cutoff m))
            (fun band ↦ candidateBudget48 m band.beta)) ≤
        ∑ band ∈ bands m, bandOverflowCoefficient (screen m band) := by
  filter_upwards [eventually_canonicalStoppedOnePointAt,
      eventually_candidateBudgetArithmeticAt, hcutoff, hthreshold] with
      m hone hbudget hcutoffM hthresholdM
  refine (simpleRandomWalk_randomClockCandidateOverflow_le_sum_dominating
    hcutoffM).trans ?_
  apply Finset.sum_le_sum
  intro band hband
  exact simpleRandomWalk_randomClockDominatingBandOverflow_le
    hone hbudget hcutoffM (hthresholdM band hband) (hbeta m band hband)
      (screen m band)

end

end Erdos1165.HLOZLowScaleCandidateOverflow
