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

import ErdosProblems.Erdos1165.HLOZGapPointReturn

/-!
# Spatially guarded point-before-return iteration

The sharp HLOZ escape probability depends on the stopped spatial gap between
the old favorite and the candidate.  The unguarded return ladder has an
irrelevant fallback target when the candidate is not hit before the deadline.
This module intersects every ladder stage with the stopped spatial guard and
with the genuine-first-hit event.  Consequently the stopped target equals the
candidate throughout the geometric iteration, so a beta-band distance bound
can be used without imposing any condition on paths outside the screened
event.
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace Erdos1165.HLOZGapGuardedPointReturn

open HLOZGapEstimate HLOZGapPointReturn HLOZGapStoppedCandidate
open PointBeforeReturn

noncomputable section

/-- A comparison with a deterministic time is observable at the stopping
time itself. -/
theorem isMeasurableAtStopping_lt_const
    {tau : StepPath → ℕ} (htau : IsFiniteStoppingTime tau) (deadline : ℕ) :
    IsMeasurableAtStopping tau {w | tau w < deadline} := by
  intro n
  by_cases hn : n < deadline
  · have heq : {w | tau w < deadline} ∩ {w | tau w = n} =
        {w | tau w = n} := by
      ext w
      simp only [Set.mem_inter_iff, Set.mem_ofPred_eq]
      constructor
      · exact fun h ↦ h.2
      · intro h
        exact ⟨h ▸ hn, h⟩
    rw [heq]
    exact htau.measurableSet_eq n
  · have heq : {w | tau w < deadline} ∩ {w | tau w = n} = ∅ := by
      ext w
      change (tau w < deadline ∧ tau w = n) ↔ False
      constructor
      · rintro ⟨hlt, heq⟩
        exact (hn (heq ▸ hlt)).elim
      · exact False.elim
    rw [heq]
    exact (incrementFiltration n).measurableSet_empty

/-- A stopped-candidate point-return witness together with the stopped
spatial guard on which its sharp escape lower bound is valid. -/
structure GuardedStoppedCandidatePointReturnWitness
    (event : Set WalkPath) (deadline returns : ℕ) (escapeChance : ℝ) where
  base : StoppedCandidatePointReturnWitness event deadline returns
  guard : Set StepPath
  guard_observable :
    IsMeasurableAtStopping base.candidateWitness.past guard
  event_guard : trajectory ⁻¹' event ⊆ guard
  guard_lower : ∀ w, w ∈ guard →
    base.oldFavorite w ≠ base.candidateWitness.candidate w →
      escapeChance ≤ pointBeforeReturnProbability
        (base.oldFavorite w - base.candidateWitness.candidate w)

/-- The guarded ladder stage.  Besides the old-favorite avoidance stage, it
retains the stopped spatial guard and records that the candidate was actually
hit before the deadline. -/
def guardedReturnLadderStage
    {event : Set WalkPath} {deadline returns : ℕ} {escapeChance : ℝ}
    (h : GuardedStoppedCandidatePointReturnWitness
      event deadline returns escapeChance) (r : ℕ) : Set StepPath :=
  (screenedReturnLadderStage h.base.candidateWitness.past h.base.start
      h.base.target deadline h.base.oldFavorite r ∩ h.guard) ∩
    {w | h.base.start w < deadline}

/-- On the screened event, the canonical candidate hit is genuine. -/
theorem GuardedStoppedCandidatePointReturnWitness.start_lt_deadline_of_event
    {event : Set WalkPath} {deadline returns : ℕ} {escapeChance : ℝ}
    (h : GuardedStoppedCandidatePointReturnWitness
      event deadline returns escapeChance)
    {w : StepPath} (hw : trajectory w ∈ event) :
    h.base.start w < deadline := by
  obtain ⟨times, _hmono, hafter, hbefore, hvisit⟩ :=
    h.base.candidateWitness.toReturnWitness.event_visits hw
  let first : Fin (returns + 1) := ⟨0, Nat.zero_lt_succ returns⟩
  apply (nextVisitBefore_lt_deadline_iff w).2
  exact ⟨times first, hbefore first, hafter first, hvisit first⟩

/-- Whenever the first-hit clock is genuine, its stopped target is the
original stopped candidate. -/
theorem GuardedStoppedCandidatePointReturnWitness.target_eq_candidate_of_start_lt
    {event : Set WalkPath} {deadline returns : ℕ} {escapeChance : ℝ}
    (h : GuardedStoppedCandidatePointReturnWitness
      event deadline returns escapeChance)
    {w : StepPath} (hw : h.base.start w < deadline) :
    h.base.target w = h.base.candidateWitness.candidate w :=
  trajectory_nextVisitBefore_eq_target_of_lt hw

/-- The guarded stopped candidate gives the full sharp geometric certificate.
The spatial guard is carried through all stages, so no global distance bound
is needed on paths outside the original slot event. -/
noncomputable def
    GuardedStoppedCandidatePointReturnWitness.toPointBeforeReturnCertificate
    {event : Set WalkPath} {deadline returns : ℕ} {escapeChance : ℝ}
    (h : GuardedStoppedCandidatePointReturnWitness
      event deadline returns escapeChance) :
    PointBeforeReturnCertificate event returns where
  stage := guardedReturnLadderStage h
  stop := returnLadder h.base.start h.base.target deadline
  relativePoint := fun _ w ↦ h.base.oldFavorite w - h.base.target w
  event_subset := by
    intro w hw
    exact ⟨⟨h.base.event_mem_screenedStage hw, h.event_guard hw⟩,
      h.start_lt_deadline_of_event hw⟩
  stop_isStopping := fun r _hr ↦
    returnLadder_isFiniteStoppingTime h.base.start_isStopping
      h.base.start_le_deadline h.base.target_observable r
  spatial_observable := by
    intro r _hr x
    have hstop : IsFiniteStoppingTime
        (returnLadder h.base.start h.base.target deadline r) :=
      returnLadder_isFiniteStoppingTime h.base.start_isStopping
        h.base.start_le_deadline h.base.target_observable r
    have hguardAtStart : IsMeasurableAtStopping h.base.start h.guard :=
      IsMeasurableAtStopping.mono_time h.guard_observable
        h.base.start_isStopping h.base.past_le_start
    have hguardAtReturn : IsMeasurableAtStopping
        (returnLadder h.base.start h.base.target deadline r) h.guard :=
      IsMeasurableAtStopping.mono_time hguardAtStart hstop
        (returnLadder_base_le h.base.start_le_deadline r)
    have hhitAtStart : IsMeasurableAtStopping h.base.start
        {w | h.base.start w < deadline} :=
      isMeasurableAtStopping_lt_const h.base.start_isStopping deadline
    have hhitAtReturn : IsMeasurableAtStopping
        (returnLadder h.base.start h.base.target deadline r)
        {w | h.base.start w < deadline} :=
      IsMeasurableAtStopping.mono_time hhitAtStart hstop
        (returnLadder_base_le h.base.start_le_deadline r)
    exact isMeasurableAtStopping_inter
      (isMeasurableAtStopping_inter
        (isMeasurableAtStopping_inter
          (screenedReturnLadderStage_observable h.base.start_isStopping
            h.base.start_le_deadline h.base.target_observable
            h.base.past_le_start h.base.oldFavorite_observable r)
          hguardAtReturn)
        hhitAtReturn)
      (returnLadder_relativePoint_fiber_observable
        h.base.start_isStopping h.base.start_le_deadline
        h.base.target_observable h.base.past_le_start
        h.base.oldFavorite_observable x)
  next_subset := by
    intro r _hr w hw
    rcases hw with ⟨⟨hstage, hguard⟩, hhit⟩
    have hnext :=
      screenedReturnLadderStage_succ_subset_pointBeforeReturn_compl
        h.base.start_le_deadline h.base.past_le_start h.base.start_at_target
        hstage
    exact ⟨⟨⟨hnext.1, hguard⟩, hhit⟩, hnext.2⟩

/-- Sharp geometric bound with a stopped spatial guard. -/
theorem measure_le_geometricReturnCost_of_guardedStoppedCandidatePointReturn
    {event : Set WalkPath} {deadline returns : ℕ} {escapeChance : ℝ}
    (hevent : MeasurableSet event)
    (hzero : 0 ≤ escapeChance) (hone : escapeChance ≤ 1)
    (h : GuardedStoppedCandidatePointReturnWitness
      event deadline returns escapeChance) :
    simpleRandomWalk event ≤ Gap.geometricReturnCost escapeChance returns := by
  apply measure_le_geometricReturnCost_of_pointBeforeReturnCertificate
    hevent hzero hone h.toPointBeforeReturnCertificate
  intro r _hr w hw
  have htarget := h.target_eq_candidate_of_start_lt hw.2
  change escapeChance ≤ pointBeforeReturnProbability
    (h.base.oldFavorite w - h.base.target w)
  rw [htarget]
  have hdistinct : h.base.oldFavorite w ≠
      h.base.candidateWitness.candidate w := by
    intro heq
    exact hw.1.1.1.2 (heq.trans htarget.symm)
  exact h.guard_lower w hw.1.2 hdistinct

section FiniteScreen

variable {Band Site : Type*}

/-- Guarded stopped candidates discharge the per-slot sharp geometric input
without a separate all-path escape hypothesis. -/
theorem perCandidateGeometricReturnBound_of_guardedStoppedPointReturns
    (bands : Finset Band) (sites : WalkPath → Band → Finset Site)
    (budget deadline returns : Band → ℕ) (escapeChance : Band → ℝ)
    (realizes : WalkPath → Band → Site → Prop)
    (hmeas : ∀ band i,
      MeasurableSet (slotSuccessEvent sites realizes band i))
    (hzero : ∀ band ∈ bands, 0 ≤ escapeChance band)
    (hone : ∀ band ∈ bands, escapeChance band ≤ 1)
    (hwitness : ∀ band ∈ bands, ∀ i ∈ Finset.range (budget band),
      GuardedStoppedCandidatePointReturnWitness
        (slotSuccessEvent sites realizes band i)
        (deadline band) (returns band) (escapeChance band)) :
    Gap.PerCandidateGeometricReturnBound simpleRandomWalk bands
      (fun band ↦ Finset.range (budget band))
      (slotSuccessEvent sites realizes) escapeChance returns := by
  intro band hband i hi
  exact measure_le_geometricReturnCost_of_guardedStoppedCandidatePointReturn
    (hmeas band i) (hzero band hband) (hone band hband)
    (hwitness band hband i hi)

end FiniteScreen

end

end Erdos1165.HLOZGapGuardedPointReturn
