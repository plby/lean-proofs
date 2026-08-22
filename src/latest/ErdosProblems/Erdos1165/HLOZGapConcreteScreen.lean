/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/
/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Formal Conjectures Authors
-/

import ErdosProblems.Erdos1165.HLOZGapCandidateMeasurability
import ErdosProblems.Erdos1165.HLOZGapPointScreeningBridge

/-!
# The concrete deterministic HLOZ gap screen

This module fixes every path object occurring in the Lemma 4.10 screen:
the candidates are the actual external-thick Proposition 4.8 candidates at
the old creation time, the distinguished set consists of the old favorite
domino bases, and the total-local-time profile is the actual local time at
that old prefix.  Slot measurability, beta-return gain, the no-old-return
certificate, and the point-before-return escape bound are all internal.

The remaining `CanonicalBandExtraction` is precisely the finite deterministic
beta-band/lazy-cap classification of a failed pair.
-/

open MeasureTheory ProbabilityTheory Set
open Filter
open scoped BigOperators ENNReal

namespace Erdos1165.HLOZGapConcreteScreen

open HLOZGapCandidateMeasurability HLOZGapCandidateRealization
open HLOZGapEstimate HLOZGapFixedPair HLOZGapMeshEscape
open HLOZGapPointScreeningBridge HLOZGapGuardedPointReturn
open HLOZPathEvents HLOZProposition48Candidates
open LazyDecomposition PreStoppingSpatialLaw

noncomputable section

/-- The finite data attached to one creation-pair/deficit band. -/
structure FixedPairBand where
  orientation : Orientation
  oldRank : ℕ
  newRank : ℕ
  nOld : ℕ
  nNew : ℕ
  nTerminal : ℕ
  returns : ℕ
  externalThreshold : ℕ
  lazyCap : ℕ
  beta : ℝ
  scale : GapScale
  oldRank_pos : 0 < oldRank
  newRank_pos : 0 < newRank
  rank_lt : oldRank < newRank
  oldTime_lt_newTime : nOld < nNew
  scale_proper : scale ∈ properGapMesh

/-- The actual stopped Proposition 4.8 candidates for one fixed band. -/
noncomputable def canonicalBandSites (m : ℕ) (s : WalkPath)
    (band : FixedPairBand) : Finset Point :=
  stoppedCandidateSites48 band.orientation band.nOld
    band.externalThreshold
    (fun s ↦ favoriteDominoBases band.orientation s band.nOld)
    (fun s x ↦ localTime s band.nOld x) m band.beta s

/-- Literal fixed-pair beta-return realization for a band. -/
def canonicalBandRealizes (m : ℕ) (s : WalkPath)
    (band : FixedPairBand) (x : Point) : Prop :=
  FixedPairReturnRealizes m band.oldRank band.newRank band.nOld band.nNew
    band.nTerminal band.returns band.scale s () x

/-- The exact additional path facts which place the failed new favorite in
the external-thick candidate set at the old prefix. -/
def CanonicalBandMembershipFacts (m : ℕ) (s : WalkPath)
    (band : FixedPairBand) (x : Point) : Prop :=
  0 < band.externalThreshold ∧
    SpatialInsertionFiber.OrientationCompatible band.orientation x ∧
    orientedBoundaryLocalTime band.orientation s x +
        orientedLazyLocalTime band.orientation s band.nOld x ≤ band.lazyCap ∧
    (∀ y ∈ thresholdSites s band.nOld m,
      dominoBase band.orientation y ≠ dominoBase band.orientation x) ∧
    0 < shellWidth48 m ∧
    (m - localTime s band.nOld x) / shellWidth48 m <
      shellCount48 m band.beta ∧
    band.externalThreshold + band.lazyCap +
        shellWidth48 m * shellCount48 m band.beta ≤ m + 1

/-- The sole deterministic extraction seam left after fixing all concrete
candidate and return objects. -/
def CanonicalBandExtraction (t : DominoTiling) (m : ℕ)
    (bands : Finset FixedPairBand) : Prop :=
  ∀ s, s ∈ onTimeGapDeficitExceptionalEvent t m →
    ∃ band ∈ bands, ∃ x,
      canonicalBandRealizes m s band x ∧
        CanonicalBandMembershipFacts m s band x

/-- The beta-band extraction gives the literal `PathGapWitness`; membership
in the candidate Finset is discharged by the oriented local-time split. -/
theorem pathGapWitness_of_canonicalBandExtraction
    {t : DominoTiling} {m : ℕ} {bands : Finset FixedPairBand}
    (hextract : CanonicalBandExtraction t m bands) :
    PathGapWitness (onTimeGapDeficitExceptionalEvent t m) bands
      (canonicalBandSites m)
      (fun band ↦ candidateBudget48 m band.beta)
      (canonicalBandRealizes m) := by
  intro s hs _hnotOverflow
  obtain ⟨band, hband, x, hrealizes, hfacts⟩ := hextract s hs
  refine ⟨band, hband, x, ?_, hrealizes⟩
  exact fixedPairReturnRealizes_mem_stoppedCandidateSites48
    band.oldRank_pos band.newRank_pos band.rank_lt hrealizes hfacts.1
    hfacts.2.1 hfacts.2.2.1 hfacts.2.2.2.1 hfacts.2.2.2.2.1
    hfacts.2.2.2.2.2.1 hfacts.2.2.2.2.2.2

/-- Every concrete band slot is a measurable event. -/
theorem measurableSet_canonicalBandSlotSuccess
    (m : ℕ) (band : FixedPairBand) (slot : ℕ) :
    MeasurableSet
      (slotSuccessEvent (canonicalBandSites m)
        (canonicalBandRealizes m) band slot) := by
  exact measurableSet_canonicalFixedPairReturn_slotSuccessEvent
    band.orientation band.nOld band.externalThreshold m band.beta
    band.oldRank band.newRank band.nOld band.nNew band.nTerminal
    band.returns band.scale slot

/-- Every concrete band slot carries the complete guarded sharp-return
certificate. -/
noncomputable def canonicalBandSlotWitness
    (m : ℕ) (band : FixedPairBand) (slot : ℕ) :
    GuardedStoppedCandidatePointReturnWitness
      (slotSuccessEvent (canonicalBandSites m)
        (canonicalBandRealizes m) band slot)
      (band.nNew + 1) band.returns
      (meshPointEscapeChance m band.scale) := by
  let h := guardedFixedPairReturnSlotWitness (canonicalBandSites m) band slot
    m band.oldRank band.newRank band.nOld band.nNew band.nTerminal
    band.returns band.scale band.scale_proper band.oldRank_pos
    band.newRank_pos band.rank_lt band.oldTime_lt_newTime
    (fun x ↦ by
      exact canonicalSlotCandidatePoint_observable band.orientation band.nOld
        band.externalThreshold m band.beta slot x)
  exact h

/-- Complete deterministic finite-union/geometric-return estimate for the
actual stopped Proposition 4.8 candidate family. -/
theorem measure_onTimeGapDeficitExceptionalEvent_le_canonicalScreen
    (t : DominoTiling) (m : ℕ) (bands : Finset FixedPairBand)
    (hextract : CanonicalBandExtraction t m bands) :
    simpleRandomWalk (onTimeGapDeficitExceptionalEvent t m) ≤
      simpleRandomWalk
        (candidateOverflow bands (canonicalBandSites m)
          (fun band ↦ candidateBudget48 m band.beta)) +
        ∑ band ∈ bands,
          (candidateBudget48 m band.beta : ℝ≥0∞) *
            Gap.geometricReturnCost
              (meshPointEscapeChance m band.scale) band.returns := by
  exact measure_onTimeGapDeficitExceptionalEvent_le_overflow_add_guardedPointReturns
    t m bands (canonicalBandSites m)
    (fun band ↦ candidateBudget48 m band.beta)
    (fun band ↦ band.nNew + 1) (fun band ↦ band.returns)
    (fun band ↦ meshPointEscapeChance m band.scale)
    (canonicalBandRealizes m)
    (pathGapWitness_of_canonicalBandExtraction hextract)
    (measurableSet_canonicalBandSlotSuccess m)
    (fun band _ ↦ (meshPointEscapeChance_pos m band.scale).le)
    (fun band _ ↦ meshPointEscapeChance_le_one m band.scale)
    (fun band _ slot _ ↦ canonicalBandSlotWitness m band slot)

/-- Concrete near-final `HasGapDeficitReturnHarnack` bridge.  All path,
measurability, stopping, local-time, and escape inputs are discharged.  Its
two quantitative premises are exactly the corrected thresholded
Proposition 4.8 overflow conclusion for each displayed band and the final
finite numerical sum. -/
theorem hasGapDeficitReturnHarnack_of_canonicalScreen
    (c : ℝ)
    (bands : DominoTiling → ℕ → Finset FixedPairBand)
    (failure : DominoTiling → ℕ → FixedPairBand → ℝ≥0∞)
    (hextract : ∀ t m, CanonicalBandExtraction t m (bands t m))
    (hprop48 : ∀ t, ∀ᶠ m : ℕ in atTop,
      ∀ band ∈ bands t m,
        simpleRandomWalk
          (stoppedCandidateOverflow48 band.orientation band.nOld
            band.externalThreshold
            (fun s ↦ favoriteDominoBases band.orientation s band.nOld)
            (fun s x ↦ localTime s band.nOld x) m band.beta) ≤
          failure t m band)
    (hnumeric : ∀ t, ∀ᶠ m : ℕ in atTop,
      (∑ band ∈ bands t m, failure t m band) +
          ∑ band ∈ bands t m,
            (candidateBudget48 m band.beta : ℝ≥0∞) *
              Gap.geometricReturnCost
                (meshPointEscapeChance m band.scale) band.returns ≤
        ENNReal.ofReal (Real.exp (-c * Real.log (m : ℝ) ^ 2))) :
    HLOZUpperEstimates.HasGapDeficitReturnHarnack c := by
  intro t
  filter_upwards [hprop48 t, hnumeric t] with m hpropM hnumericM
  have hscreen := measure_onTimeGapDeficitExceptionalEvent_le_canonicalScreen
    t m (bands t m) (hextract t m)
  have hoverflow :
      simpleRandomWalk
          (candidateOverflow (bands t m) (canonicalBandSites m)
            (fun band ↦ candidateBudget48 m band.beta)) ≤
        ∑ band ∈ bands t m, failure t m band := by
    change simpleRandomWalk
        (orientedStoppedCandidateOverflow48 (bands t m)
          FixedPairBand.orientation FixedPairBand.nOld
          FixedPairBand.externalThreshold
          (fun band s ↦
            favoriteDominoBases band.orientation s band.nOld)
          (fun band s x ↦ localTime s band.nOld x) m
          FixedPairBand.beta) ≤ _
    exact simpleRandomWalk_orientedStoppedCandidateOverflow48_le
      (bands t m) FixedPairBand.orientation FixedPairBand.nOld
      FixedPairBand.externalThreshold
      (fun band s ↦ favoriteDominoBases band.orientation s band.nOld)
      (fun band s x ↦ localTime s band.nOld x) m FixedPairBand.beta
      (failure t m) hpropM
  exact hscreen.trans ((add_le_add hoverflow le_rfl).trans hnumericM)

end

end Erdos1165.HLOZGapConcreteScreen
