/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/
/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

import ErdosProblems.Erdos1165.HLOZGapGuardedPointReturn
import ErdosProblems.Erdos1165.HLOZProposition48Candidates
import ErdosProblems.Erdos1165.HLOZUpperEstimates

/-!
# Sharp stopped-candidate bridge for the HLOZ gap screen

This is the point-before-return analogue of `HLOZGapStoppedScreeningBridge`.
It uses the stopped-prefix deficit bands and the explicit candidate budget
from HLOZ Proposition 4.8, and replaces the coarse finite-horizon escape cost
by an arbitrary bandwise lower bound on `P_0(H_x < H_0^+)`.
-/

open Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace Erdos1165.HLOZGapPointScreeningBridge

open HLOZGapEstimate HLOZGapPointReturn HLOZUpperEstimates
open HLOZProposition48Candidates
open HLOZGapGuardedPointReturn
open LazyDecomposition PointBeforeReturn

noncomputable section

/-- The sharp finite-screen estimate for the correctly time-truncated gap
event.  The late fourth-creation clock is budgeted separately by Proposition
1.3 in `HLOZUpperEstimates`. -/
theorem measure_onTimeGapDeficitExceptionalEvent_le_overflow_add_pointReturns
    {Band Site : Type*} (t : DominoTiling) (m : ℕ) (bands : Finset Band)
    (sites : WalkPath → Band → Finset Site)
    (budget deadline returns : Band → ℕ) (escapeChance : Band → ℝ)
    (realizes : WalkPath → Band → Site → Prop)
    (hpath : PathGapWitness
      (HLOZPathEvents.onTimeGapDeficitExceptionalEvent t m)
      bands sites budget realizes)
    (hmeas : ∀ band i,
      MeasurableSet (slotSuccessEvent sites realizes band i))
    (hzero : ∀ band ∈ bands, 0 ≤ escapeChance band)
    (hone : ∀ band ∈ bands, escapeChance band ≤ 1)
    (hwitness : ∀ band ∈ bands, ∀ i ∈ Finset.range (budget band),
      StoppedCandidatePointReturnWitness
        (slotSuccessEvent sites realizes band i)
        (deadline band) (returns band))
    (hlower : ∀ (band : Band) (hband : band ∈ bands) (i : ℕ)
      (hi : i ∈ Finset.range (budget band)) (w : StepPath),
      let h := hwitness band hband i hi
      h.oldFavorite w ≠ h.target w →
        escapeChance band ≤ pointBeforeReturnProbability
          (h.oldFavorite w - h.target w)) :
    simpleRandomWalk
        (HLOZPathEvents.onTimeGapDeficitExceptionalEvent t m) ≤
      simpleRandomWalk (candidateOverflow bands sites budget) +
        ∑ band ∈ bands, (budget band : ℝ≥0∞) *
          Gap.geometricReturnCost (escapeChance band) (returns band) := by
  let overflow := candidateOverflow bands sites budget
  let screened := HLOZPathEvents.onTimeGapDeficitExceptionalEvent t m \ overflow
  have hsplit : HLOZPathEvents.onTimeGapDeficitExceptionalEvent t m ⊆
      overflow ∪ screened := by
    intro s hs
    by_cases ho : s ∈ overflow
    · exact Or.inl ho
    · exact Or.inr ⟨hs, ho⟩
  calc
    simpleRandomWalk
        (HLOZPathEvents.onTimeGapDeficitExceptionalEvent t m) ≤
        simpleRandomWalk (overflow ∪ screened) := measure_mono hsplit
    _ ≤ simpleRandomWalk overflow + simpleRandomWalk screened :=
      measure_union_le _ _
    _ ≤ simpleRandomWalk overflow +
        ∑ band ∈ bands, (budget band : ℝ≥0∞) *
          Gap.geometricReturnCost (escapeChance band) (returns band) := by
      gcongr
      exact Gap.measure_gapEvent_le_geometric_sum simpleRandomWalk screened bands
        (fun band ↦ Finset.range (budget band))
        (slotSuccessEvent sites realizes) budget escapeChance returns
        (by
          dsimp only [screened, overflow]
          exact gapEvent_diff_overflow_covered_by_slots
            (HLOZPathEvents.onTimeGapDeficitExceptionalEvent t m)
            bands sites budget realizes hpath)
        (range_candidateCountBound bands budget)
        (perCandidateGeometricReturnBound_of_stoppedCandidatePointReturns
          bands sites budget deadline returns escapeChance realizes hmeas
          hzero hone hwitness hlower)

/-- Guarded version of the on-time screen.  The stopped spatial guard is
retained through every return stage, so the sharp distance-dependent escape
bound is part of each witness rather than an all-path side condition. -/
theorem measure_onTimeGapDeficitExceptionalEvent_le_overflow_add_guardedPointReturns
    {Band Site : Type*} (t : DominoTiling) (m : ℕ) (bands : Finset Band)
    (sites : WalkPath → Band → Finset Site)
    (budget deadline returns : Band → ℕ) (escapeChance : Band → ℝ)
    (realizes : WalkPath → Band → Site → Prop)
    (hpath : PathGapWitness
      (HLOZPathEvents.onTimeGapDeficitExceptionalEvent t m)
      bands sites budget realizes)
    (hmeas : ∀ band i,
      MeasurableSet (slotSuccessEvent sites realizes band i))
    (hzero : ∀ band ∈ bands, 0 ≤ escapeChance band)
    (hone : ∀ band ∈ bands, escapeChance band ≤ 1)
    (hwitness : ∀ band ∈ bands, ∀ i ∈ Finset.range (budget band),
      GuardedStoppedCandidatePointReturnWitness
        (slotSuccessEvent sites realizes band i)
        (deadline band) (returns band) (escapeChance band)) :
    simpleRandomWalk
        (HLOZPathEvents.onTimeGapDeficitExceptionalEvent t m) ≤
      simpleRandomWalk (candidateOverflow bands sites budget) +
        ∑ band ∈ bands, (budget band : ℝ≥0∞) *
          Gap.geometricReturnCost (escapeChance band) (returns band) := by
  let overflow := candidateOverflow bands sites budget
  let screened := HLOZPathEvents.onTimeGapDeficitExceptionalEvent t m \ overflow
  have hsplit : HLOZPathEvents.onTimeGapDeficitExceptionalEvent t m ⊆
      overflow ∪ screened := by
    intro s hs
    by_cases ho : s ∈ overflow
    · exact Or.inl ho
    · exact Or.inr ⟨hs, ho⟩
  calc
    simpleRandomWalk
        (HLOZPathEvents.onTimeGapDeficitExceptionalEvent t m) ≤
        simpleRandomWalk (overflow ∪ screened) := measure_mono hsplit
    _ ≤ simpleRandomWalk overflow + simpleRandomWalk screened :=
      measure_union_le _ _
    _ ≤ simpleRandomWalk overflow +
        ∑ band ∈ bands, (budget band : ℝ≥0∞) *
          Gap.geometricReturnCost (escapeChance band) (returns band) := by
      gcongr
      exact Gap.measure_gapEvent_le_geometric_sum simpleRandomWalk screened bands
        (fun band ↦ Finset.range (budget band))
        (slotSuccessEvent sites realizes) budget escapeChance returns
        (by
          dsimp only [screened, overflow]
          exact gapEvent_diff_overflow_covered_by_slots
            (HLOZPathEvents.onTimeGapDeficitExceptionalEvent t m)
            bands sites budget realizes hpath)
        (range_candidateCountBound bands budget)
        (perCandidateGeometricReturnBound_of_guardedStoppedPointReturns
          bands sites budget deadline returns escapeChance realizes hmeas
          hzero hone hwitness)

/-! ## The genuine Proposition 4.8 beta-band screen -/

/-- The stopped candidate family associated with one finite family of
deficit exponents.  Keeping the old clock, external threshold, distinguished
sites, and stopped local time band-dependent lets the same definition cover
each of the three successive creation pairs and both domino orientations. -/
noncomputable def stoppedBandCandidateSites48 {Band : Type*} (m : ℕ)
    (orientation : Band → Orientation) (cutoff externalThreshold : Band → ℕ)
    (distinguished : Band → WalkPath → Finset Point)
    (totalLocalTime : Band → WalkPath → Point → ℕ)
    (beta : Band → ℝ) (s : WalkPath) (band : Band) : Finset Point :=
  stoppedCandidateSites48 (orientation band) (cutoff band)
    (externalThreshold band) (distinguished band) (totalLocalTime band)
    m (beta band) s

/-- Proposition 4.8's explicit slot budget, indexed by the same beta band. -/
noncomputable def stoppedBandCandidateBudget48 {Band : Type*} (m : ℕ)
    (beta : Band → ℝ) (band : Band) : ℕ :=
  candidateBudget48 m (beta band)

/-- Candidate overflow for a finite family of genuine Proposition 4.8 bands
is bounded by the sum of its single-band stopped-prefix overflows. -/
theorem measure_candidateOverflow_stoppedBandCandidateSites48_le_sum
    {Band : Type*} (μ : Measure WalkPath) (m : ℕ) (bands : Finset Band)
    (orientation : Band → Orientation) (cutoff externalThreshold : Band → ℕ)
    (distinguished : Band → WalkPath → Finset Point)
    (totalLocalTime : Band → WalkPath → Point → ℕ)
    (beta : Band → ℝ) :
    μ (candidateOverflow bands
        (stoppedBandCandidateSites48 m orientation cutoff externalThreshold
          distinguished totalLocalTime beta)
        (stoppedBandCandidateBudget48 m beta)) ≤
      ∑ band ∈ bands,
        μ (stoppedCandidateOverflow48 (orientation band) (cutoff band)
          (externalThreshold band) (distinguished band)
          (totalLocalTime band) m (beta band)) := by
  simpa only [candidateOverflow, stoppedBandCandidateSites48,
    stoppedBandCandidateBudget48, Screening.someCandidateBad,
    stoppedCandidateOverflow48, Set.mem_ofPred_eq] using
      (Screening.measure_someCandidateBad_le_sum μ bands fun band ↦
        stoppedCandidateOverflow48 (orientation band) (cutoff band)
          (externalThreshold band) (distinguished band)
          (totalLocalTime band) m (beta band))

/-- The complete finite-union bridge with the actual HLOZ Proposition 4.8
beta-band candidate set and budget.  `hoverflow` is precisely the path-level
conclusion furnished bandwise by
`simpleRandomWalk_real_stoppedCandidateOverflow48_le`; all candidate
enumeration and conversion from real-valued overflow bounds are internal. -/
theorem hasGapDeficitReturnHarnack_of_stoppedProposition48PointReturnCandidates
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
    (escapeChance overflowCost : DominoTiling → ℕ → Band → ℝ)
    (hpath : ∀ t m,
      PathGapWitness (HLOZPathEvents.onTimeGapDeficitExceptionalEvent t m)
        (bands t m)
        (stoppedBandCandidateSites48 m orientation (cutoff t m)
          (externalThreshold t m) (distinguished t m) (totalLocalTime t m)
          (beta t m))
        (stoppedBandCandidateBudget48 m (beta t m))
        (realizes t m))
    (hmeasurable : ∀ t m band slot,
      MeasurableSet
        (slotSuccessEvent
          (stoppedBandCandidateSites48 m orientation (cutoff t m)
            (externalThreshold t m) (distinguished t m) (totalLocalTime t m)
            (beta t m))
          (realizes t m) band slot))
    (hzero : ∀ t m band, band ∈ bands t m →
      0 ≤ escapeChance t m band)
    (hone : ∀ t m band, band ∈ bands t m →
      escapeChance t m band ≤ 1)
    (hwitness : ∀ t m band, band ∈ bands t m →
      ∀ slot ∈ Finset.range (candidateBudget48 m (beta t m band)),
        GuardedStoppedCandidatePointReturnWitness
          (slotSuccessEvent
            (stoppedBandCandidateSites48 m orientation (cutoff t m)
              (externalThreshold t m) (distinguished t m)
              (totalLocalTime t m) (beta t m))
            (realizes t m) band slot)
          (deadline t m band) (returns t m band)
          (escapeChance t m band))
    (hoverflow : ∀ t, ∀ᶠ m : ℕ in atTop,
      ∀ band ∈ bands t m,
        simpleRandomWalk.real
            (stoppedCandidateOverflow48 (orientation band)
              (cutoff t m band) (externalThreshold t m band)
              (distinguished t m band) (totalLocalTime t m band)
              m (beta t m band)) ≤
          overflowCost t m band)
    (hnumeric : ∀ t, ∀ᶠ m : ℕ in atTop,
      (∑ band ∈ bands t m, ENNReal.ofReal (overflowCost t m band)) +
          ∑ band ∈ bands t m,
            (candidateBudget48 m (beta t m band) : ℝ≥0∞) *
              Gap.geometricReturnCost
                (escapeChance t m band) (returns t m band) ≤
        ENNReal.ofReal (Real.exp (-c * Real.log (m : ℝ) ^ 2))) :
    HasGapDeficitReturnHarnack c := by
  intro t
  filter_upwards [hoverflow t, hnumeric t] with m hoverflowM hnumericM
  let sites := stoppedBandCandidateSites48 m orientation (cutoff t m)
    (externalThreshold t m) (distinguished t m) (totalLocalTime t m)
    (beta t m)
  let budget := stoppedBandCandidateBudget48 m (beta t m)
  have hscreen :=
    measure_onTimeGapDeficitExceptionalEvent_le_overflow_add_guardedPointReturns
      t m (bands t m) sites budget (deadline t m) (returns t m)
      (escapeChance t m) (realizes t m) (hpath t m)
      (hmeasurable t m) (hzero t m) (hone t m) (hwitness t m)
  have hoverflowUnion :
      simpleRandomWalk (candidateOverflow (bands t m) sites budget) ≤
        ∑ band ∈ bands t m, ENNReal.ofReal (overflowCost t m band) := by
    refine (measure_candidateOverflow_stoppedBandCandidateSites48_le_sum
      simpleRandomWalk m (bands t m) orientation (cutoff t m)
        (externalThreshold t m) (distinguished t m) (totalLocalTime t m)
        (beta t m)).trans ?_
    apply Finset.sum_le_sum
    intro band hband
    rw [← ofReal_measureReal (measure_ne_top simpleRandomWalk _)]
    exact ENNReal.ofReal_le_ofReal (hoverflowM band hband)
  exact hscreen.trans <| (by
    calc
      simpleRandomWalk (candidateOverflow (bands t m) sites budget) +
          ∑ band ∈ bands t m, (budget band : ℝ≥0∞) *
            Gap.geometricReturnCost
              (escapeChance t m band) (returns t m band) ≤
          (∑ band ∈ bands t m, ENNReal.ofReal (overflowCost t m band)) +
            ∑ band ∈ bands t m,
              (candidateBudget48 m (beta t m band) : ℝ≥0∞) *
                Gap.geometricReturnCost
                  (escapeChance t m band) (returns t m band) := by
        dsimp only [budget, stoppedBandCandidateBudget48]
        gcongr
      _ ≤ ENNReal.ofReal (Real.exp (-c * Real.log (m : ℝ) ^ 2)) :=
        hnumericM)

end

end Erdos1165.HLOZGapPointScreeningBridge
