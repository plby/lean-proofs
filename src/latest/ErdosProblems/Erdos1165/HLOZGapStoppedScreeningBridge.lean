/-
Copyright (c) 2026 The Erdos Problems Formalization Project.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Erdos Problems Formalization Project
-/

import ErdosProblems.Erdos1165.HLOZGapStoppedCandidate
import ErdosProblems.Erdos1165.HLOZProposition48Candidates
import ErdosProblems.Erdos1165.HLOZUpperEstimates

/-!
# Concrete stopped-candidate bridge for the HLOZ gap screen

This file aligns the canonical Proposition 4.4 candidate sets from
`HLOZGapEstimate` with the first-hit/local-time API of
`HLOZGapStoppedCandidate`.  Candidate enumeration, the two-orientation
overflow reduction, first-hit construction, revisit clocks, and strong
Markov iteration are all internal.

The remaining path-specific inputs are the literal `PathGapWitness`, slot
measurability, and a stopped-candidate local-time gain.  The only probability
transport left is the path-to-external-chain comparison used by Proposition
4.4.  The last premise is an explicit numerical domination of the displayed
failure-rate/geometric-cost expression, rather than a restatement of the
target event inequality.
-/

open Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace Erdos1165.HLOZGapStoppedScreeningBridge

open HLOZGapEstimate HLOZGapStoppedCandidate HLOZUpperEstimates
open HLOZProposition48Candidates
open LazyDecomposition

noncomputable section

/-- The stopped-local-time finite screen for the correctly clock-truncated
gap event.  Lateness is a separate exceptional family in the upper endgame. -/
theorem measure_onTimeLowGapDeficitExceptionalEvent_le_overflow_add_stoppedCandidates
    {Band Site : Type*} (t : DominoTiling) (m : ℕ) (bands : Finset Band)
    (sites : WalkPath → Band → Finset Site)
    (budget deadline returns : Band → ℕ)
    (realizes : WalkPath → Band → Site → Prop)
    (hpath : PathGapWitness
      (HLOZPathEvents.onTimeLowGapDeficitExceptionalEvent t m)
      bands sites budget realizes)
    (hmeas : ∀ band i,
      MeasurableSet (slotSuccessEvent sites realizes band i))
    (hdeadline : ∀ band ∈ bands, 2 ≤ deadline band)
    (hwitness : ∀ band ∈ bands, ∀ i ∈ Finset.range (budget band),
      StoppedCandidateReturnWitness
        (slotSuccessEvent sites realizes band i)
        (deadline band) (returns band)) :
    simpleRandomWalk
        (HLOZPathEvents.onTimeLowGapDeficitExceptionalEvent t m) ≤
      simpleRandomWalk (candidateOverflow bands sites budget) +
        ∑ band ∈ bands, (budget band : ℝ≥0∞) *
          Gap.geometricReturnCost
            (1 / (100 * Real.log (deadline band))) (returns band) := by
  let overflow := candidateOverflow bands sites budget
  let screened := HLOZPathEvents.onTimeLowGapDeficitExceptionalEvent t m \ overflow
  have hsplit : HLOZPathEvents.onTimeLowGapDeficitExceptionalEvent t m ⊆
      overflow ∪ screened := by
    intro s hs
    by_cases ho : s ∈ overflow
    · exact Or.inl ho
    · exact Or.inr ⟨hs, ho⟩
  calc
    simpleRandomWalk
        (HLOZPathEvents.onTimeLowGapDeficitExceptionalEvent t m) ≤
        simpleRandomWalk (overflow ∪ screened) := measure_mono hsplit
    _ ≤ simpleRandomWalk overflow + simpleRandomWalk screened :=
      measure_union_le _ _
    _ ≤ simpleRandomWalk overflow +
        ∑ band ∈ bands, (budget band : ℝ≥0∞) *
          Gap.geometricReturnCost
            (1 / (100 * Real.log (deadline band))) (returns band) := by
      gcongr
      exact Gap.measure_gapEvent_le_geometric_sum simpleRandomWalk screened bands
        (fun band ↦ Finset.range (budget band))
        (slotSuccessEvent sites realizes) budget
        (fun band ↦ 1 / (100 * Real.log (deadline band))) returns
        (by
          dsimp only [screened, overflow]
          exact gapEvent_diff_overflow_covered_by_slots
            (HLOZPathEvents.onTimeLowGapDeficitExceptionalEvent t m)
            bands sites budget realizes hpath)
        (range_candidateCountBound bands budget)
        (perCandidateGeometricReturnBound_of_stoppedCandidates
          bands sites budget deadline returns realizes hmeas hdeadline hwitness)

/-- Canonical oriented Proposition 4.4 candidates, equipped with literal
stopped local-time gains, imply the exact gap-return/Harnack input consumed
by the HLOZ upper endgame. -/
theorem hasGapDeficitReturnHarnack_of_orientedStoppedLocalTimeCandidates
    {Band : Type*} (c : ℝ)
    (bands : DominoTiling → ℕ → Finset Band)
    (orientation : Band → Orientation)
    (distinguished :
      DominoTiling → ℕ → Orientation → WalkPath → Finset Point)
    (realizes : DominoTiling → ℕ → WalkPath → Band → Point → Prop)
    (deadline returns : DominoTiling → ℕ → Band → ℕ)
    (hpath : ∀ t m,
      PathGapWitness (HLOZPathEvents.onTimeLowGapDeficitExceptionalEvent t m)
        (bands t m)
        (orientedCandidateSites44 orientation m (distinguished t m))
        (fun _ ↦ ExternalProposition44.hlozSiteBudget44 m)
        (realizes t m))
    (hmeasurable : ∀ t m band slot,
      MeasurableSet
        (slotSuccessEvent
          (orientedCandidateSites44 orientation m (distinguished t m))
          (realizes t m) band slot))
    (hdeadline : ∀ t m band, band ∈ bands t m →
      2 ≤ deadline t m band)
    (hlocalTime : ∀ t m band, band ∈ bands t m →
      ∀ slot ∈ Finset.range (ExternalProposition44.hlozSiteBudget44 m),
        StoppedCandidateLocalTimeWitness
          (slotSuccessEvent
            (orientedCandidateSites44 orientation m (distinguished t m))
            (realizes t m) band slot)
          (deadline t m band) (returns t m band))
    (htransportEven : ∀ᶠ m : ℕ in atTop,
      ExternalCountTransport44 .even m)
    (htransportShifted : ∀ᶠ m : ℕ in atTop,
      ExternalCountTransport44 .shifted m)
    (hnumeric : ∀ t, ∀ᶠ m : ℕ in atTop,
      ExternalProposition44.hlozFailureRate44 m +
          ExternalProposition44.hlozFailureRate44 m +
          ∑ band ∈ bands t m,
            (ExternalProposition44.hlozSiteBudget44 m : ℝ≥0∞) *
              Gap.geometricReturnCost
                (1 / (100 * Real.log (deadline t m band)))
                (returns t m band) ≤
        ENNReal.ofReal (Real.exp (-c * Real.log (m : ℝ) ^ 2))) :
    HasGapDeficitReturnHarnack c := by
  intro t
  have hoverflow :=
    eventually_orientedCandidateOverflow44_lt_two_failureRates
      (bands t) orientation (distinguished t) htransportEven htransportShifted
  filter_upwards [hoverflow, hnumeric t] with m hoverflowM hnumericM
  have hscreen :=
    measure_onTimeLowGapDeficitExceptionalEvent_le_overflow_add_stoppedCandidates
      t m (bands t m)
      (orientedCandidateSites44 orientation m (distinguished t m))
      (fun _ ↦ ExternalProposition44.hlozSiteBudget44 m)
      (deadline t m) (returns t m) (realizes t m) (hpath t m)
      (hmeasurable t m) (hdeadline t m)
      (fun band hband slot hslot ↦
        (hlocalTime t m band hband slot hslot).toReturnWitness)
  have hscreen' :
      simpleRandomWalk
          (HLOZPathEvents.onTimeLowGapDeficitExceptionalEvent t m) ≤
        simpleRandomWalk
            (orientedCandidateOverflow44 (bands t m) orientation m
              (distinguished t m)) +
          ∑ band ∈ bands t m,
            (ExternalProposition44.hlozSiteBudget44 m : ℝ≥0∞) *
              Gap.geometricReturnCost
                (1 / (100 * Real.log (deadline t m band)))
                (returns t m band) := by
    simpa only [orientedCandidateOverflow44] using hscreen
  exact hscreen'.trans <| (by
    calc
      simpleRandomWalk
            (orientedCandidateOverflow44 (bands t m) orientation m
              (distinguished t m)) +
          ∑ band ∈ bands t m,
            (ExternalProposition44.hlozSiteBudget44 m : ℝ≥0∞) *
              Gap.geometricReturnCost
                (1 / (100 * Real.log (deadline t m band)))
                (returns t m band) ≤
          ExternalProposition44.hlozFailureRate44 m +
              ExternalProposition44.hlozFailureRate44 m +
              ∑ band ∈ bands t m,
                (ExternalProposition44.hlozSiteBudget44 m : ℝ≥0∞) *
                  Gap.geometricReturnCost
                    (1 / (100 * Real.log (deadline t m band)))
                    (returns t m band) := by
            gcongr
      _ ≤ ENNReal.ofReal (Real.exp (-c * Real.log (m : ℝ) ^ 2)) :=
        hnumericM)

/-! ## The genuine Proposition 4.8 deficit-band bridge -/

/-- Concrete stopped-prefix Proposition 4.8 candidates imply the gap-return
input consumed by the upper endgame.  Unlike the preceding legacy adapter,
the slot budget depends on the deficit-band exponent and has logarithm

`O(m^(beta-kappaOne) + log log m)`.

The `hprop48` premise is the per-band output of
`simpleRandomWalk_real_stoppedCandidateOverflow48_le` (converted by
`simpleRandomWalk_stoppedCandidateOverflow48_le_of_real`), or of the literal
stopped-product adapter in `HLOZProposition48Product`.  Thus it is a genuine
candidate-count screen, not the target gap-transition inequality. -/
theorem hasGapDeficitReturnHarnack_of_orientedStoppedProposition48Candidates
    {Band : Type*} (c : ℝ)
    (bands : DominoTiling → ℕ → Finset Band)
    (orientation : Band → Orientation)
    (cutoff externalThreshold : DominoTiling → ℕ → Band → ℕ)
    (distinguished :
      DominoTiling → ℕ → Band → WalkPath → Finset Point)
    (totalLocalTime :
      DominoTiling → ℕ → Band → WalkPath → Point → ℕ)
    (beta : DominoTiling → ℕ → Band → ℝ)
    (realizes : DominoTiling → ℕ → WalkPath → Band → Point → Prop)
    (deadline returns : DominoTiling → ℕ → Band → ℕ)
    (failure : DominoTiling → ℕ → Band → ℝ≥0∞)
    (hpath : ∀ t m,
      PathGapWitness (HLOZPathEvents.onTimeLowGapDeficitExceptionalEvent t m)
        (bands t m)
        (orientedStoppedCandidateSites48 orientation (cutoff t m)
          (externalThreshold t m) (distinguished t m) (totalLocalTime t m)
          m (beta t m))
        (fun band ↦ candidateBudget48 m (beta t m band))
        (realizes t m))
    (hmeasurable : ∀ t m band slot,
      MeasurableSet
        (slotSuccessEvent
          (orientedStoppedCandidateSites48 orientation (cutoff t m)
            (externalThreshold t m) (distinguished t m) (totalLocalTime t m)
            m (beta t m))
          (realizes t m) band slot))
    (hdeadline : ∀ t m band, band ∈ bands t m →
      2 ≤ deadline t m band)
    (hlocalTime : ∀ t m band, band ∈ bands t m →
      ∀ slot ∈ Finset.range (candidateBudget48 m (beta t m band)),
        StoppedCandidateLocalTimeWitness
          (slotSuccessEvent
            (orientedStoppedCandidateSites48 orientation (cutoff t m)
              (externalThreshold t m) (distinguished t m)
              (totalLocalTime t m) m (beta t m))
            (realizes t m) band slot)
          (deadline t m band) (returns t m band))
    (hprop48 : ∀ t, ∀ᶠ m : ℕ in atTop,
      ∀ band ∈ bands t m,
        simpleRandomWalk
          (stoppedCandidateOverflow48 (orientation band) (cutoff t m band)
            (externalThreshold t m band) (distinguished t m band)
            (totalLocalTime t m band) m (beta t m band)) ≤
          failure t m band)
    (hnumeric : ∀ t, ∀ᶠ m : ℕ in atTop,
      (∑ band ∈ bands t m, failure t m band) +
          ∑ band ∈ bands t m,
            (candidateBudget48 m (beta t m band) : ℝ≥0∞) *
              Gap.geometricReturnCost
                (1 / (100 * Real.log (deadline t m band)))
                (returns t m band) ≤
        ENNReal.ofReal (Real.exp (-c * Real.log (m : ℝ) ^ 2))) :
    HasGapDeficitReturnHarnack c := by
  intro t
  filter_upwards [hprop48 t, hnumeric t] with m hprop48M hnumericM
  let sites : WalkPath → Band → Finset Point :=
    orientedStoppedCandidateSites48 orientation (cutoff t m)
      (externalThreshold t m) (distinguished t m) (totalLocalTime t m)
      m (beta t m)
  let budget : Band → ℕ := fun band ↦ candidateBudget48 m (beta t m band)
  have hoverflow :
      simpleRandomWalk (candidateOverflow (bands t m) sites budget) ≤
        ∑ band ∈ bands t m, failure t m band := by
    change simpleRandomWalk
        (orientedStoppedCandidateOverflow48 (bands t m) orientation
          (cutoff t m) (externalThreshold t m) (distinguished t m)
          (totalLocalTime t m) m (beta t m)) ≤ _
    exact simpleRandomWalk_orientedStoppedCandidateOverflow48_le
      (bands t m) orientation (cutoff t m) (externalThreshold t m)
      (distinguished t m) (totalLocalTime t m) m (beta t m)
      (failure t m) hprop48M
  have hscreen :=
    measure_onTimeLowGapDeficitExceptionalEvent_le_overflow_add_stoppedCandidates
      t m (bands t m) sites budget (deadline t m) (returns t m)
      (realizes t m) (by
        dsimp only [sites, budget]
        exact hpath t m)
      (by
        intro band slot
        dsimp only [sites]
        exact hmeasurable t m band slot)
      (hdeadline t m)
      (fun band hband slot hslot ↦ by
        dsimp only [sites, budget] at hslot ⊢
        exact (hlocalTime t m band hband slot hslot).toReturnWitness)
  exact hscreen.trans <| (add_le_add hoverflow le_rfl).trans hnumericM

end

end Erdos1165.HLOZGapStoppedScreeningBridge
