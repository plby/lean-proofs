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

import ErdosProblems.Erdos1165.HLOZGapReturn

/-!
# First-hit stopped candidates for HLOZ Lemma 4.10

`HLOZGapReturn` constructs the successive-return ladder once its initial
clock is already at the random target.  This file removes that last formal
stopping-time obligation.  A candidate observable at a stopped past is hit
at the canonical capped first-visit clock; the position at that new clock is
automatically an observable stopped target.  An explicit increasing list of
candidate visits then dominates the canonical return ladder.

Consequently an application only has to prove the deterministic assertion
which is specific to HLOZ Lemma 4.10: on a slot-success event, the selected
candidate has the required number of visits after the stopped past and before
the deterministic deadline.
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace Erdos1165.HLOZGapStoppedCandidate

open HLOZGapEstimate HLOZGapReturn

noncomputable section

/-! ## The position at a finite stopping time -/

/-- The walk position observed at a finite stopping time. -/
def stoppedLocation (tau : StepPath → ℕ) (w : StepPath) : Point :=
  trajectory w (tau w)

/-- The position at a finite stopping time is observable at that stopping
time.  The proof is the stopped-atom decomposition, so it does not use any
optional-stopping or completion theorem. -/
theorem stoppedLocation_fiber_observable
    {tau : StepPath → ℕ} (htau : IsFiniteStoppingTime tau) (x : Point) :
    IsMeasurableAtStopping tau {w | stoppedLocation tau w = x} := by
  intro n
  have heq :
      {w | stoppedLocation tau w = x} ∩ {w | tau w = n} =
        {w | trajectory w n = x} ∩ {w | tau w = n} := by
    ext w
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, stoppedLocation]
    constructor
    · rintro ⟨hloc, htime⟩
      exact ⟨by simpa only [htime] using hloc, htime⟩
    · rintro ⟨hloc, htime⟩
      exact ⟨by simpa only [htime] using hloc, htime⟩
  rw [heq]
  exact (measurableSet_eq_fun
      (measurable_trajectory_at_incrementFiltration n) measurable_const).inter
    (htau.measurableSet_eq n)

/-! ## A deterministic schedule of strict candidate visits -/

/-- There are `visits` strictly increasing visits to `target`, strictly after
`past` and strictly before `deadline`.  This is the exact deterministic datum
which a local-time deficit supplies in the HLOZ application. -/
def HasStrictVisitSchedule (past : StepPath → ℕ)
    (target : StepPath → Point) (deadline visits : ℕ) (w : StepPath) : Prop :=
  ∃ times : Fin visits → ℕ,
    StrictMono times ∧
      (∀ i, past w < times i) ∧
      (∀ i, times i < deadline) ∧
      (∀ i, trajectory w (times i) = target w)

/-- The finite set of visits to `x` strictly after `past` and strictly before
`deadline`.  Its cardinality is the most convenient form of the deterministic
local-time input in applications. -/
def strictVisitTimes (s : WalkPath) (x : Point) (past deadline : ℕ) :
    Finset ℕ :=
  (Finset.Ioo past deadline).filter fun n ↦ s n = x

@[simp] theorem mem_strictVisitTimes_iff
    {s : WalkPath} {x : Point} {past deadline n : ℕ} :
    n ∈ strictVisitTimes s x past deadline ↔
      past < n ∧ n < deadline ∧ s n = x := by
  simp only [strictVisitTimes, Finset.mem_filter, Finset.mem_Ioo]
  tauto

/-- Sorting any sufficiently large finite set of strict visits produces the
explicit increasing schedule consumed by the canonical return ladder. -/
theorem hasStrictVisitSchedule_of_card_strictVisitTimes
    {past : StepPath → ℕ} {target : StepPath → Point}
    {deadline visits : ℕ} {w : StepPath}
    (hcard : visits ≤
      (strictVisitTimes (trajectory w) (target w) (past w) deadline).card) :
    HasStrictVisitSchedule past target deadline visits w := by
  let S := strictVisitTimes (trajectory w) (target w) (past w) deadline
  let times : Fin visits → ℕ := S.orderEmbOfCardLe hcard
  refine ⟨times, (S.orderEmbOfCardLe hcard).strictMono, ?_, ?_, ?_⟩
  · intro i
    exact (mem_strictVisitTimes_iff.mp
      (S.orderEmbOfCardLe_mem hcard i)).1
  · intro i
    exact (mem_strictVisitTimes_iff.mp
      (S.orderEmbOfCardLe_mem hcard i)).2.1
  · intro i
    exact (mem_strictVisitTimes_iff.mp
      (S.orderEmbOfCardLe_mem hcard i)).2.2

/-- The open-interval visit count is exactly the increase of local time from
`past` through time `deadline - 1`. -/
theorem card_strictVisitTimes_eq_localTime_sub
    (s : WalkPath) (x : Point) {past deadline : ℕ}
    (hpast : past < deadline) :
    (strictVisitTimes s x past deadline).card =
      localTime s (deadline - 1) x - localTime s past x := by
  let beforeDeadline :=
    (Finset.range deadline).filter fun n ↦ s n = x
  let throughPast :=
    (Finset.range (past + 1)).filter fun n ↦ s n = x
  have hsubset : throughPast ⊆ beforeDeadline := by
    intro n hn
    simp only [throughPast, beforeDeadline, Finset.mem_filter,
      Finset.mem_range] at hn ⊢
    exact ⟨by omega, hn.2⟩
  have hset : strictVisitTimes s x past deadline =
      beforeDeadline \ throughPast := by
    ext n
    simp only [mem_strictVisitTimes_iff, beforeDeadline, throughPast,
      Finset.mem_sdiff, Finset.mem_filter, Finset.mem_range]
    by_cases hn : s n = x
    · simp only [hn, and_true]
      omega
    · simp [hn]
  have hbefore : beforeDeadline.card = localTime s (deadline - 1) x := by
    rw [localTime_eq_card_filter_range]
    dsimp only [beforeDeadline]
    rw [Nat.sub_add_cancel (by omega : 1 ≤ deadline)]
  have hthrough : throughPast.card = localTime s past x := by
    exact (localTime_eq_card_filter_range s past x).symm
  rw [hset, Finset.card_sdiff_of_subset hsubset, hbefore, hthrough]

/-- A literal local-time gain yields the sorted strict-visit schedule. -/
theorem hasStrictVisitSchedule_of_localTime_gain
    {past : StepPath → ℕ} {target : StepPath → Point}
    {deadline visits : ℕ} {w : StepPath}
    (hpast : past w < deadline)
    (hgain : localTime (trajectory w) (past w) (target w) + visits ≤
      localTime (trajectory w) (deadline - 1) (target w)) :
    HasStrictVisitSchedule past target deadline visits w := by
  apply hasStrictVisitSchedule_of_card_strictVisitTimes
  rw [card_strictVisitTimes_eq_localTime_sub _ _ hpast]
  omega

/-! ## The deterministic content of an HLOZ gap failure -/

/-- If a new level-`m` creation occurs before the deadline and the preceding
creation pair satisfies `gapDeficitFailure`, then the new site gains more
than the displayed deficit cutoff after the old creation time.  This is the
literal pathwise estimate which feeds `StoppedCandidateLocalTimeWitness`. -/
theorem gapDeficitFailure_localTime_gain
    {s : WalkPath} {m k nOld nNew deadline : ℕ}
    (hk : 0 < k)
    (hnew : HLOZPathEvents.ThresholdCreation s m k nNew)
    (hfailure : HLOZPathEvents.gapDeficitFailure s m nOld nNew)
    (hnewDeadline : nNew < deadline) :
    localTime s nOld (s nNew) +
        (HLOZPathEvents.gapDeficitCutoff m
          (HLOZPathEvents.gapScaleOf m (s nOld) (s nNew)) + 1) ≤
      localTime s (deadline - 1) (s nNew) := by
  have hdeficit :
      localTime s nOld (s nNew) +
          HLOZPathEvents.gapDeficitCutoff m
            (HLOZPathEvents.gapScaleOf m (s nOld) (s nNew)) < m := by
    exact hfailure.2
  have hthreshold : m ≤ localTime s nNew (s nNew) := by
    exact (mem_thresholdSites s nNew m (s nNew)).mp
      (HLOZPathEvents.position_mem_thresholdSites_of_creation hk hnew) |>.2
  have htime : nNew ≤ deadline - 1 := by omega
  have hmono : localTime s nNew (s nNew) ≤
      localTime s (deadline - 1) (s nNew) :=
    localTime_mono_time s (s nNew) htime
  omega

/-- Cardinality form of the same pathwise deficit consequence. -/
theorem gapDeficitFailure_strictVisitTimes
    {s : WalkPath} {m k nOld nNew deadline : ℕ}
    (hk : 0 < k)
    (hnew : HLOZPathEvents.ThresholdCreation s m k nNew)
    (hfailure : HLOZPathEvents.gapDeficitFailure s m nOld nNew)
    (hnewDeadline : nNew < deadline) :
    HLOZPathEvents.gapDeficitCutoff m
          (HLOZPathEvents.gapScaleOf m (s nOld) (s nNew)) + 1 ≤
      (strictVisitTimes s (s nNew) nOld deadline).card := by
  have holdNew : nOld < nNew := by
    by_contra hnot
    have hmono : localTime s nNew (s nNew) ≤ localTime s nOld (s nNew) :=
      localTime_mono_time s (s nNew) (Nat.le_of_not_gt hnot)
    have hthreshold : m ≤ localTime s nNew (s nNew) :=
      (mem_thresholdSites s nNew m (s nNew)).mp
        (HLOZPathEvents.position_mem_thresholdSites_of_creation hk hnew) |>.2
    have hdeficit := hfailure.2
    omega
  rw [card_strictVisitTimes_eq_localTime_sub _ _
    (holdNew.trans hnewDeadline)]
  have hgain := gapDeficitFailure_localTime_gain hk hnew hfailure hnewDeadline
  omega

/-- A visit at a strictly later time strictly increases the local time of its
site. -/
theorem localTime_lt_of_later_visit
    {s : WalkPath} {x : Point} {a b : ℕ}
    (hab : a < b) (hb : s b = x) :
    localTime s a x < localTime s b x := by
  obtain ⟨q, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : b ≠ 0)
  have haq : a ≤ q := Nat.lt_succ_iff.mp hab
  have hmono : localTime s a x ≤ localTime s q x :=
    localTime_mono_time s x haq
  rw [localTime_succ, if_pos hb]
  omega

/-- Once an old creation site has local time at least `m`, absence of every
level-`m+1` site at a later terminal time means that the old site is never
visited again in between.  This is the other deterministic ingredient needed
by the sharp point-before-return kernel. -/
theorem no_oldCreation_visit_of_no_next_level
    {s : WalkPath} {m k nOld terminal : ℕ}
    (hk : 0 < k)
    (hold : HLOZPathEvents.ThresholdCreation s m k nOld)
    (hnext : thresholdCount s terminal (m + 1) = 0) :
    ∀ q, nOld < q → q ≤ terminal → s q ≠ s nOld := by
  have holdLevel : m ≤ localTime s nOld (s nOld) :=
    (mem_thresholdSites s nOld m (s nOld)).mp
      (HLOZPathEvents.position_mem_thresholdSites_of_creation hk hold) |>.2
  have hbelow : localTime s terminal (s nOld) < m + 1 :=
    (thresholdCount_eq_zero_iff_forall_lt s terminal (m + 1) (by omega)).mp hnext _
  intro q hOldQ hqTerminal hq
  have hstrict := localTime_lt_of_later_visit hOldQ hq
  have hmono : localTime s q (s nOld) ≤ localTime s terminal (s nOld) :=
    localTime_mono_time s (s nOld) hqTerminal
  omega

/-- If the capped next-visit clock is strictly before its deadline, it really
is located at the requested target. -/
theorem trajectory_nextVisitBefore_eq_target_of_lt
    {past : StepPath → ℕ} {target : StepPath → Point} {deadline : ℕ}
    {w : StepPath}
    (hlt : nextVisitBefore past target deadline w < deadline) :
    trajectory w (nextVisitBefore past target deadline w) = target w := by
  classical
  have hex := (nextVisitBefore_lt_deadline_iff w).mp hlt
  unfold nextVisitBefore
  rw [dif_pos hex]
  exact (Nat.find_spec hex).2.2

/-- Every entry of a strict visit schedule lies after the preceding canonical
return-ladder clock. -/
theorem returnLadder_le_visitTime
    {past : StepPath → ℕ} {candidate : StepPath → Point}
    {deadline visits : ℕ} {w : StepPath}
    (times : Fin visits → ℕ) (hmono : StrictMono times)
    (hafter : ∀ i, past w < times i)
    (hbefore : ∀ i, times i < deadline)
    (hvisit : ∀ i, trajectory w (times i) = candidate w)
    (i : Fin visits) :
    returnLadder
        (nextVisitBefore past candidate deadline)
        (stoppedLocation (nextVisitBefore past candidate deadline))
        deadline i w ≤ times i := by
  let start := nextVisitBefore past candidate deadline
  let target := stoppedLocation start
  have hstartLt : start w < deadline := by
    apply (nextVisitBefore_lt_deadline_iff w).2
    exact ⟨times i, hbefore i, hafter i, hvisit i⟩
  have htarget : target w = candidate w := by
    dsimp only [target, stoppedLocation]
    exact trajectory_nextVisitBefore_eq_target_of_lt hstartLt
  have hle : ∀ n : ℕ, ∀ hn : n < visits,
      returnLadder start target deadline n w ≤ times ⟨n, hn⟩ := by
    intro n
    induction n with
    | zero =>
        intro hn
        rw [returnLadder_zero]
        dsimp only [start]
        apply (nextVisitBefore_le_iff (hbefore ⟨0, hn⟩) w).2
        exact ⟨times ⟨0, hn⟩, le_rfl, hafter ⟨0, hn⟩, hvisit ⟨0, hn⟩⟩
    | succ n ih =>
        intro hn
        have hnprev : n < visits := lt_trans (Nat.lt_succ_self n) hn
        have hprev := ih hnprev
        have hstrict : times ⟨n, hnprev⟩ < times ⟨n + 1, hn⟩ := by
          apply hmono
          exact Fin.mk_lt_mk.mpr (Nat.lt_succ_self n)
        rw [returnLadder_succ]
        apply (nextVisitBefore_le_iff (hbefore ⟨n + 1, hn⟩) w).2
        refine ⟨times ⟨n + 1, hn⟩, le_rfl, hprev.trans_lt hstrict, ?_⟩
        exact (hvisit ⟨n + 1, hn⟩).trans htarget.symm
  exact hle i i.isLt

/-- A schedule containing the first candidate hit and `returns` subsequent
visits forces the `returns`-th canonical return ladder clock to occur before
the deadline. -/
theorem returnLadderStage_of_strictVisitSchedule
    {past : StepPath → ℕ} {candidate : StepPath → Point}
    {deadline returns : ℕ} {w : StepPath}
    (h : HasStrictVisitSchedule past candidate deadline (returns + 1) w) :
    w ∈ returnLadderStage
      (nextVisitBefore past candidate deadline)
      (stoppedLocation (nextVisitBefore past candidate deadline))
      deadline returns := by
  cases returns with
  | zero => simp [returnLadderStage]
  | succ r =>
      rcases h with ⟨times, hmono, hafter, hbefore, hvisit⟩
      have hle := returnLadder_le_visitTime times hmono hafter hbefore hvisit
        ⟨r + 1, by omega⟩
      change returnLadder
          (nextVisitBefore past candidate deadline)
          (stoppedLocation (nextVisitBefore past candidate deadline))
          deadline (r + 1) w < deadline
      simpa using hle.trans_lt (hbefore ⟨r + 1, by omega⟩)

/-! ## The concrete first-hit witness -/

/-- A stopped-past candidate together with the pathwise strict-visit
consequence of one slot event.  Unlike `StoppedTargetReturnWitness`, this
structure does not ask the application to construct a new stopping time,
prove its target observable, or prove that the clock is at the target. -/
structure StoppedCandidateReturnWitness
    (event : Set WalkPath) (deadline returns : ℕ) where
  past : StepPath → ℕ
  candidate : StepPath → Point
  past_isStopping : IsFiniteStoppingTime past
  past_le_deadline : ∀ w, past w ≤ deadline
  candidate_observable : ∀ x,
    IsMeasurableAtStopping past {w | candidate w = x}
  event_visits : trajectory ⁻¹' event ⊆
    {w | HasStrictVisitSchedule past candidate deadline (returns + 1) w}

/-- Cardinality form of the stopped-candidate witness.  This is generally the
direct output of the local-time deficit calculation: the successful slot has
at least `returns + 1` visits in the open time interval. -/
structure StoppedCandidateCountWitness
    (event : Set WalkPath) (deadline returns : ℕ) where
  past : StepPath → ℕ
  candidate : StepPath → Point
  past_isStopping : IsFiniteStoppingTime past
  past_le_deadline : ∀ w, past w ≤ deadline
  candidate_observable : ∀ x,
    IsMeasurableAtStopping past {w | candidate w = x}
  event_count : ∀ w, trajectory w ∈ event →
    returns + 1 ≤
      (strictVisitTimes (trajectory w) (candidate w) (past w) deadline).card

/-- Local-time form of the stopped candidate input.  This is the direct
shape obtained when the new site exceeds its stopped-past local time by the
band's required deficit before the common cutoff. -/
structure StoppedCandidateLocalTimeWitness
    (event : Set WalkPath) (deadline returns : ℕ) where
  past : StepPath → ℕ
  candidate : StepPath → Point
  past_isStopping : IsFiniteStoppingTime past
  past_lt_deadline : ∀ w, past w < deadline
  candidate_observable : ∀ x,
    IsMeasurableAtStopping past {w | candidate w = x}
  event_gain : ∀ w, trajectory w ∈ event →
    localTime (trajectory w) (past w) (candidate w) + (returns + 1) ≤
      localTime (trajectory w) (deadline - 1) (candidate w)

/-- Convert the literal finite visit count to the sorted strict-visit
schedule. -/
def StoppedCandidateCountWitness.toReturnWitness
    {event : Set WalkPath} {deadline returns : ℕ}
    (h : StoppedCandidateCountWitness event deadline returns) :
    StoppedCandidateReturnWitness event deadline returns where
  past := h.past
  candidate := h.candidate
  past_isStopping := h.past_isStopping
  past_le_deadline := h.past_le_deadline
  candidate_observable := h.candidate_observable
  event_visits := fun w hw ↦
    hasStrictVisitSchedule_of_card_strictVisitTimes (h.event_count w hw)

/-- Convert the local-time deficit directly to the stopped return witness. -/
def StoppedCandidateLocalTimeWitness.toReturnWitness
    {event : Set WalkPath} {deadline returns : ℕ}
    (h : StoppedCandidateLocalTimeWitness event deadline returns) :
    StoppedCandidateReturnWitness event deadline returns where
  past := h.past
  candidate := h.candidate
  past_isStopping := h.past_isStopping
  past_le_deadline := fun w ↦ (h.past_lt_deadline w).le
  candidate_observable := h.candidate_observable
  event_visits := fun w hw ↦
    hasStrictVisitSchedule_of_localTime_gain (h.past_lt_deadline w)
      (h.event_gain w hw)

/-- Canonical first hit followed by canonical strict revisits supplies the
complete stopped-target witness used by `HLOZGapReturn`. -/
noncomputable def StoppedCandidateReturnWitness.toStoppedTarget
    {event : Set WalkPath} {deadline returns : ℕ}
    (h : StoppedCandidateReturnWitness event deadline returns) :
    StoppedTargetReturnWitness event deadline returns where
  start := nextVisitBefore h.past h.candidate deadline
  target := stoppedLocation (nextVisitBefore h.past h.candidate deadline)
  start_isStopping :=
    isFiniteStoppingTime_nextVisitBefore h.candidate_observable
  start_le_deadline := nextVisitBefore_le_deadline _ _ _
  target_observable := fun x ↦ stoppedLocation_fiber_observable
    (isFiniteStoppingTime_nextVisitBefore h.candidate_observable) x
  start_at_target := fun _ ↦ rfl
  event_subset := fun _ hw ↦
    returnLadderStage_of_strictVisitSchedule (h.event_visits hw)

/-- Strong Markov plus two-point avoidance, with all first-hit and revisit
clocks generated from the stopped-past candidate data. -/
theorem measure_le_geometricReturnCost_of_stoppedCandidate
    {event : Set WalkPath} {deadline returns : ℕ}
    (hevent : MeasurableSet event) (hdeadline : 2 ≤ deadline)
    (h : StoppedCandidateReturnWitness event deadline returns) :
    simpleRandomWalk event ≤
      Gap.geometricReturnCost
        (1 / (100 * Real.log deadline)) returns :=
  measure_le_geometricReturnCost_of_stoppedTarget hevent hdeadline
    h.toStoppedTarget

/-- Cardinality-input version of the stopped-candidate geometric estimate. -/
theorem measure_le_geometricReturnCost_of_stoppedCandidateCount
    {event : Set WalkPath} {deadline returns : ℕ}
    (hevent : MeasurableSet event) (hdeadline : 2 ≤ deadline)
    (h : StoppedCandidateCountWitness event deadline returns) :
    simpleRandomWalk event ≤
      Gap.geometricReturnCost
        (1 / (100 * Real.log deadline)) returns :=
  measure_le_geometricReturnCost_of_stoppedCandidate hevent hdeadline
    h.toReturnWitness

/-- Local-time-input version of the stopped-candidate geometric estimate. -/
theorem measure_le_geometricReturnCost_of_stoppedCandidateLocalTime
    {event : Set WalkPath} {deadline returns : ℕ}
    (hevent : MeasurableSet event) (hdeadline : 2 ≤ deadline)
    (h : StoppedCandidateLocalTimeWitness event deadline returns) :
    simpleRandomWalk event ≤
      Gap.geometricReturnCost
        (1 / (100 * Real.log deadline)) returns :=
  measure_le_geometricReturnCost_of_stoppedCandidate hevent hdeadline
    h.toReturnWitness

section FiniteScreen

variable {Band Site : Type*}

/-- One stopped-past candidate and its strict-visit consequence per finite
slot discharge the per-candidate geometric premise. -/
theorem perCandidateGeometricReturnBound_of_stoppedCandidates
    (bands : Finset Band) (sites : WalkPath → Band → Finset Site)
    (budget deadline returns : Band → ℕ)
    (realizes : WalkPath → Band → Site → Prop)
    (hmeas : ∀ band i,
      MeasurableSet (slotSuccessEvent sites realizes band i))
    (hdeadline : ∀ band ∈ bands, 2 ≤ deadline band)
    (hwitness : ∀ band ∈ bands, ∀ i ∈ Finset.range (budget band),
      StoppedCandidateReturnWitness
        (slotSuccessEvent sites realizes band i)
        (deadline band) (returns band)) :
    Gap.PerCandidateGeometricReturnBound simpleRandomWalk bands
      (fun band ↦ Finset.range (budget band))
      (slotSuccessEvent sites realizes)
      (fun band ↦ 1 / (100 * Real.log (deadline band))) returns := by
  intro band hband i hi
  exact measure_le_geometricReturnCost_of_stoppedCandidate
    (hmeas band i) (hdeadline band hband) (hwitness band hband i hi)

/-- The finite path-gap engine with both candidate-return clock construction
and strong-Markov iteration discharged.  The hypotheses which remain are the
literal path-to-candidate cover/count witness and the deterministic fact that
a realized slot has enough strict visits. -/
theorem measure_gapDeficitExceptionalEvent_le_overflow_add_stoppedCandidates
    (t : DominoTiling) (m : ℕ) (bands : Finset Band)
    (sites : WalkPath → Band → Finset Site)
    (budget deadline returns : Band → ℕ)
    (realizes : WalkPath → Band → Site → Prop)
    (hpath : PathGapWitness (HLOZPathEvents.gapDeficitExceptionalEvent t m)
      bands sites budget realizes)
    (hmeas : ∀ band i,
      MeasurableSet (slotSuccessEvent sites realizes band i))
    (hdeadline : ∀ band ∈ bands, 2 ≤ deadline band)
    (hwitness : ∀ band ∈ bands, ∀ i ∈ Finset.range (budget band),
      StoppedCandidateReturnWitness
        (slotSuccessEvent sites realizes band i)
        (deadline band) (returns band)) :
    simpleRandomWalk (HLOZPathEvents.gapDeficitExceptionalEvent t m) ≤
      simpleRandomWalk (candidateOverflow bands sites budget) +
        ∑ band ∈ bands, (budget band : ℝ≥0∞) *
          Gap.geometricReturnCost
            (1 / (100 * Real.log (deadline band))) (returns band) := by
  exact measure_gapDeficitExceptionalEvent_le_overflow_add_stoppedGeometric
    t m bands sites budget deadline returns realizes hpath hmeas hdeadline
    (fun band hband i hi ↦ (hwitness band hband i hi).toStoppedTarget)

end FiniteScreen

end

end Erdos1165.HLOZGapStoppedCandidate
