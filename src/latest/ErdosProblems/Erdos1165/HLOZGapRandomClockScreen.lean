/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/
/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Formal Conjectures Authors
-/

import ErdosProblems.Erdos1165.HLOZGapCandidateMeasurability
import ErdosProblems.Erdos1165.HLOZGapPointScreeningBridge

/-!
# Random-clock HLOZ gap screening

The old and new level-`m` creation times are genuine capped stopping times,
not deterministic entries of the beta-band index.  Thus the final union
bound ranges only over the finite geometric/beta data.

The existing fixed-deadline point-return witness asks for avoidance of the
old favorite all the way to that deadline.  This is stronger than the HLOZ
path event: the latter gives avoidance only through the fourth creation,
while all required candidate returns occur no later than the selected new
creation.  We therefore use an explicit stopped-past visit schedule whose
last visit is bounded by the random terminal clock.  This is exactly what
the full-tail strong Markov iteration needs and makes no assertion about the
irrelevant portion between the fourth creation and the deterministic cap.
-/

open Filter MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal

namespace Erdos1165.HLOZGapRandomClockScreen

open HLOZGapCandidateMeasurability HLOZGapEstimate HLOZGapFixedPair
open HLOZGapGuardedPointReturn HLOZGapMeshEscape HLOZGapPointReturn
open HLOZGapPointScreeningBridge HLOZGapStoppedCandidate HLOZPathEvents
open HLOZProposition48Candidates LazyDecomposition PointBeforeReturn
open PreStoppingSpatialLaw StoppedInsertion

noncomputable section

/-! ## The capped clock on walk paths -/

/-- Walk-path version of `StoppedInsertion.truncatedLevelTime`. -/
noncomputable def pathTruncatedLevelTime
    (m k cutoff : ℕ) (s : WalkPath) : ℕ := by
  classical
  exact if h : ReachesThreshold s m k then min (Nat.find h) cutoff else cutoff

@[simp] theorem pathTruncatedLevelTime_trajectory
    (m k cutoff : ℕ) (omega : StepPath) :
    pathTruncatedLevelTime m k cutoff (trajectory omega) =
      truncatedLevelTime m k cutoff omega := by
  rfl

theorem pathTruncatedLevelTime_le
    (m k cutoff : ℕ) (s : WalkPath) :
    pathTruncatedLevelTime m k cutoff s ≤ cutoff := by
  classical
  unfold pathTruncatedLevelTime
  split_ifs
  · exact min_le_right _ _
  · exact le_rfl

private theorem find_threshold_le_iff
    (s : WalkPath) (m k n : ℕ) (h : ReachesThreshold s m k) :
    Nat.find h ≤ n ↔ k ≤ thresholdCount s n m := by
  constructor
  · intro hle
    exact (Nat.find_spec h).trans (thresholdCount_mono_time s m hle)
  · exact Nat.find_min' h

theorem pathTruncatedLevelTime_le_iff
    (m k cutoff n : ℕ) (s : WalkPath) :
    pathTruncatedLevelTime m k cutoff s ≤ n ↔
      cutoff ≤ n ∨ k ≤ thresholdCount s n m := by
  classical
  by_cases hcut : cutoff ≤ n
  · constructor
    · exact fun _ ↦ Or.inl hcut
    · exact fun _ ↦ (pathTruncatedLevelTime_le m k cutoff s).trans hcut
  · have hncut : n < cutoff := Nat.lt_of_not_ge hcut
    unfold pathTruncatedLevelTime
    split_ifs with hreach
    · rw [min_le_iff, find_threshold_le_iff s m k n hreach]
      simp only [hcut, or_false, false_or]
    · have hnot : ¬k ≤ thresholdCount s n m := by
        intro hn
        exact hreach ⟨n, hn⟩
      simp [Nat.not_le.mpr hncut, hnot]

theorem measurableSet_pathTruncatedLevelTime_le
    (m k cutoff n : ℕ) :
    MeasurableSet {s : WalkPath |
      pathTruncatedLevelTime m k cutoff s ≤ n} := by
  have heq : {s : WalkPath | pathTruncatedLevelTime m k cutoff s ≤ n} =
      if cutoff ≤ n then Set.univ
      else {s : WalkPath | k ≤ thresholdCount s n m} := by
    ext s
    simp only [Set.mem_ofPred_eq]
    rw [pathTruncatedLevelTime_le_iff]
    by_cases h : cutoff ≤ n <;> simp [h]
  rw [heq]
  split_ifs
  · exact MeasurableSet.univ
  · exact (measurable_thresholdCount n m)
      (Set.to_countable {q : ℕ | k ≤ q}).measurableSet

theorem measurableSet_pathTruncatedLevelTime_eq
    (m k cutoff n : ℕ) :
    MeasurableSet {s : WalkPath |
      pathTruncatedLevelTime m k cutoff s = n} := by
  cases n with
  | zero =>
      have heq : {s : WalkPath | pathTruncatedLevelTime m k cutoff s = 0} =
          {s : WalkPath | pathTruncatedLevelTime m k cutoff s ≤ 0} := by
        ext s
        simp only [Set.mem_ofPred_eq]
        omega
      rw [heq]
      exact measurableSet_pathTruncatedLevelTime_le m k cutoff 0
  | succ n =>
      have heq :
          {s : WalkPath | pathTruncatedLevelTime m k cutoff s = n + 1} =
            {s : WalkPath | pathTruncatedLevelTime m k cutoff s ≤ n + 1} \
              {s : WalkPath | pathTruncatedLevelTime m k cutoff s ≤ n} := by
        ext s
        simp only [Set.mem_ofPred_eq, Set.mem_sdiff]
        omega
      rw [heq]
      exact (measurableSet_pathTruncatedLevelTime_le m k cutoff (n + 1)).diff
        (measurableSet_pathTruncatedLevelTime_le m k cutoff n)

/-! ## Band-only stopped candidates -/

/-- A beta/geometric band contains no creation times. -/
structure RandomClockBand where
  orientation : Orientation
  /-- Endpoint (`false`) or midpoint (`true`) phase of a statefully deleted
  two-step external path.  Canonical horizontal screens may ignore this tag;
  the all-six tiling screen uses it to select the correct external chain. -/
  vertexPhase : Bool
  oldRank : ℕ
  newRank : ℕ
  returns : ℕ
  externalThreshold : ℕ
  lazyCap : ℕ
  beta : ℝ
  scale : GapScale
  oldRank_pos : 0 < oldRank
  newRank_pos : 0 < newRank
  rank_lt : oldRank < newRank
  newRank_le_four : newRank ≤ 4
  scale_proper : scale ∈ properGapMesh

/-- The actual Proposition 4.8 candidate set evaluated at the random old
creation clock. -/
noncomputable def randomClockBandSites
    (m cutoff : ℕ) (s : WalkPath) (band : RandomClockBand) : Finset Point :=
  let nOld := pathTruncatedLevelTime m band.oldRank cutoff s
  stoppedCandidateSites48 band.orientation nOld band.externalThreshold
    (fun u ↦ favoriteDominoBases band.orientation u nOld)
    (fun u x ↦ localTime u nOld x) m band.beta s

/-- The point occupying a fixed slot of the random-prefix candidate set. -/
def randomClockSlotCandidatePoint
    (m cutoff : ℕ) (band : RandomClockBand) (slot : ℕ)
    (omega : StepPath) : Point :=
  (finsetSlot (randomClockBandSites m cutoff (trajectory omega) band) slot).getD 0

lemma randomClockSlotCandidatePoint_eq_of_slot
    {m cutoff : ℕ} {band : RandomClockBand} {slot : ℕ}
    {omega : StepPath} {x : Point}
    (hslot : finsetSlot
      (randomClockBandSites m cutoff (trajectory omega) band) slot = some x) :
    randomClockSlotCandidatePoint m cutoff band slot omega = x := by
  simp [randomClockSlotCandidatePoint, hslot]

/-- The random candidate slot is observable at the genuine old threshold
clock. -/
theorem randomClockSlotCandidatePoint_observable
    (m cutoff : ℕ) (band : RandomClockBand) (slot : ℕ) (x : Point) :
    IsMeasurableAtStopping
      (truncatedLevelTime m band.oldRank cutoff)
      {omega | randomClockSlotCandidatePoint m cutoff band slot omega = x} := by
  intro n
  let deterministicPoint : StepPath → Point := fun omega ↦
    (finsetSlot
      (stoppedCandidateSites48 band.orientation n band.externalThreshold
        (fun s ↦ favoriteDominoBases band.orientation s n)
        (fun s y ↦ localTime s n y) m band.beta (trajectory omega)) slot).getD 0
  have hdetObs : IsMeasurableAtStopping (fun _ : StepPath ↦ n)
      {omega | deterministicPoint omega = x} := by
    simpa only [deterministicPoint, HLOZGapFixedPair.slotCandidatePoint] using
      (canonicalSlotCandidatePoint_observable band.orientation n
        band.externalThreshold m band.beta slot x)
  have hdetMeas : MeasurableSet[incrementFiltration n]
      {omega | deterministicPoint omega = x} := by
    convert hdetObs n using 1
    ext omega
    simp
  have heq :
      {omega | randomClockSlotCandidatePoint m cutoff band slot omega = x} ∩
          {omega | truncatedLevelTime m band.oldRank cutoff omega = n} =
        {omega | deterministicPoint omega = x} ∩
          {omega | truncatedLevelTime m band.oldRank cutoff omega = n} := by
    ext omega
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨hpoint, hclock⟩
      refine ⟨?_, hclock⟩
      simpa only [randomClockSlotCandidatePoint, randomClockBandSites,
        pathTruncatedLevelTime_trajectory, hclock, deterministicPoint] using hpoint
    · rintro ⟨hpoint, hclock⟩
      refine ⟨?_, hclock⟩
      simpa only [randomClockSlotCandidatePoint, randomClockBandSites,
        pathTruncatedLevelTime_trajectory, hclock, deterministicPoint] using hpoint
  rw [heq]
  exact hdetMeas.inter
    ((isFiniteStoppingTime_truncatedLevelTime m band.oldRank cutoff).measurableSet_eq n)

/-- Random-clock realization of a failed pair.  The terminal clock is the
actual fourth level-`m` creation clock. -/
def RandomClockPairRealizes
    (m cutoff : ℕ) (s : WalkPath) (band : RandomClockBand) (x : Point) : Prop :=
  FixedPairReturnRealizes m band.oldRank band.newRank
    (pathTruncatedLevelTime m band.oldRank cutoff s)
    (pathTruncatedLevelTime m band.newRank cutoff s)
    (pathTruncatedLevelTime m 4 cutoff s)
    band.returns band.scale s () x

/-- A fixed candidate slot of the random-prefix family is a measurable
walk-path event.  The proof partitions by the value of the bounded old
clock, but this partition is used only for measurability and never in the
probability union bound. -/
theorem measurableSet_randomClockBandSlot_eq
    (m cutoff : ℕ) (band : RandomClockBand) (slot : ℕ) (x : Point) :
    MeasurableSet {s : WalkPath |
      finsetSlot (randomClockBandSites m cutoff s band) slot = some x} := by
  have heq :
      {s : WalkPath |
          finsetSlot (randomClockBandSites m cutoff s band) slot = some x} =
        ⋃ n : ℕ,
          {s | pathTruncatedLevelTime m band.oldRank cutoff s = n} ∩
            {s | finsetSlot
              (stoppedCandidateSites48 band.orientation n
                band.externalThreshold
                (fun u ↦ favoriteDominoBases band.orientation u n)
                (fun u y ↦ localTime u n y) m band.beta s) slot = some x} := by
    ext s
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_inter_iff]
    constructor
    · intro hs
      refine ⟨pathTruncatedLevelTime m band.oldRank cutoff s, rfl, ?_⟩
      simpa only [randomClockBandSites] using hs
    · rintro ⟨n, hn, hs⟩
      simpa only [randomClockBandSites, hn] using hs
  rw [heq]
  apply MeasurableSet.iUnion
  intro n
  have hsites := measurable_canonicalStoppedCandidateSites48 band.orientation n
    band.externalThreshold m band.beta
  exact (measurableSet_pathTruncatedLevelTime_eq m band.oldRank cutoff n).inter
    (hsites (Set.to_countable {S : Finset Point |
      finsetSlot S slot = some x}).measurableSet)

/-- Random-clock failed-pair realization is measurable without retaining
the clock values in the band index. -/
theorem measurableSet_randomClockPairRealizes
    (m cutoff : ℕ) (band : RandomClockBand) (x : Point) :
    MeasurableSet {s : WalkPath | RandomClockPairRealizes m cutoff s band x} := by
  have heq : {s : WalkPath | RandomClockPairRealizes m cutoff s band x} =
      ⋃ nOld : ℕ, ⋃ nNew : ℕ, ⋃ nTerminal : ℕ,
        (({s | pathTruncatedLevelTime m band.oldRank cutoff s = nOld} ∩
          {s | pathTruncatedLevelTime m band.newRank cutoff s = nNew}) ∩
          {s | pathTruncatedLevelTime m 4 cutoff s = nTerminal}) ∩
          {s | FixedPairReturnRealizes m band.oldRank band.newRank
            nOld nNew nTerminal band.returns band.scale s () x} := by
    ext s
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_inter_iff]
    change RandomClockPairRealizes m cutoff s band x ↔
      ∃ nOld nNew nTerminal,
        ((pathTruncatedLevelTime m band.oldRank cutoff s = nOld ∧
          pathTruncatedLevelTime m band.newRank cutoff s = nNew) ∧
          pathTruncatedLevelTime m 4 cutoff s = nTerminal) ∧
          FixedPairReturnRealizes m band.oldRank band.newRank nOld nNew
            nTerminal band.returns band.scale s () x
    constructor
    · intro hs
      exact ⟨pathTruncatedLevelTime m band.oldRank cutoff s,
        pathTruncatedLevelTime m band.newRank cutoff s,
        pathTruncatedLevelTime m 4 cutoff s, ⟨⟨rfl, rfl⟩, rfl⟩, hs⟩
    · rintro ⟨nOld, nNew, nTerminal, ⟨⟨hOld, hNew⟩, hTerminal⟩, hs⟩
      simpa only [RandomClockPairRealizes, hOld, hNew, hTerminal] using hs
  rw [heq]
  exact MeasurableSet.iUnion fun nOld ↦ MeasurableSet.iUnion fun nNew ↦
    MeasurableSet.iUnion fun nTerminal ↦
      (((measurableSet_pathTruncatedLevelTime_eq m band.oldRank cutoff nOld).inter
        (measurableSet_pathTruncatedLevelTime_eq m band.newRank cutoff nNew)).inter
        (measurableSet_pathTruncatedLevelTime_eq m 4 cutoff nTerminal)).inter
        (measurableSet_fixedPairReturnRealizes m band.oldRank band.newRank
          nOld nNew nTerminal band.returns band.scale x)

/-- Every random-clock slot-success event is measurable. -/
theorem measurableSet_randomClockBandSlotSuccess
    (m cutoff : ℕ) (band : RandomClockBand) (slot : ℕ) :
    MeasurableSet
      (slotSuccessEvent (randomClockBandSites m cutoff)
        (RandomClockPairRealizes m cutoff) band slot) := by
  have heq :
      slotSuccessEvent (randomClockBandSites m cutoff)
          (RandomClockPairRealizes m cutoff) band slot =
        ⋃ x : Point,
          {s | finsetSlot (randomClockBandSites m cutoff s band) slot = some x} ∩
            {s | RandomClockPairRealizes m cutoff s band x} := by
    ext s
    simp only [slotSuccessEvent, Set.mem_ofPred_eq, Set.mem_iUnion,
      Set.mem_inter_iff]
  rw [heq]
  exact MeasurableSet.iUnion fun x ↦
    (measurableSet_randomClockBandSlot_eq m cutoff band slot x).inter
      (measurableSet_randomClockPairRealizes m cutoff band x)

/-! ## A sound random-terminal return certificate -/

/-- A stopped candidate with an explicit ordered visit schedule.  Avoidance
of the old favorite is required only through the last scheduled visit, which
is the exact pathwise information supplied by successive threshold clocks. -/
structure GuardedStoppedCandidateScheduleWitness
    (event : Set WalkPath) (deadline returns : ℕ) (escapeChance : ℝ) where
  past : StepPath → ℕ
  candidate : StepPath → Point
  oldFavorite : StepPath → Point
  past_isStopping : IsFiniteStoppingTime past
  past_lt_deadline : ∀ omega, past omega < deadline
  candidate_observable : ∀ x,
    IsMeasurableAtStopping past {omega | candidate omega = x}
  oldFavorite_observable : ∀ x,
    IsMeasurableAtStopping past {omega | oldFavorite omega = x}
  guard : Set StepPath
  guard_observable : IsMeasurableAtStopping past guard
  event_guard : trajectory ⁻¹' event ⊆ guard
  event_distinct : ∀ omega, trajectory omega ∈ event →
    oldFavorite omega ≠ candidate omega
  event_schedule : ∀ omega, trajectory omega ∈ event →
    ∃ times : Fin (returns + 1) → ℕ,
      StrictMono times ∧
        (∀ i, past omega < times i) ∧
        (∀ i, times i < deadline) ∧
        (∀ i, trajectory omega (times i) = candidate omega) ∧
        ∀ q, past omega < q →
          q ≤ times ⟨returns, Nat.lt_succ_self returns⟩ →
          trajectory omega q ≠ oldFavorite omega
  guard_lower : ∀ omega, omega ∈ guard →
    oldFavorite omega ≠ candidate omega →
      escapeChance ≤ pointBeforeReturnProbability
        (oldFavorite omega - candidate omega)

namespace GuardedStoppedCandidateScheduleWitness

variable {event : Set WalkPath} {deadline returns : ℕ} {escapeChance : ℝ}

/-- First candidate hit after the stopped past, capped only for construction
of an honest natural-valued stopping time. -/
noncomputable def start
    (h : GuardedStoppedCandidateScheduleWitness
      event deadline returns escapeChance) : StepPath → ℕ :=
  nextVisitBefore h.past h.candidate deadline

/-- Position at the first candidate-hit clock. -/
def target
    (h : GuardedStoppedCandidateScheduleWitness
      event deadline returns escapeChance) : StepPath → Point :=
  stoppedLocation h.start

theorem start_isStopping
    (h : GuardedStoppedCandidateScheduleWitness
      event deadline returns escapeChance) :
    IsFiniteStoppingTime h.start :=
  isFiniteStoppingTime_nextVisitBefore h.candidate_observable

theorem past_le_start
    (h : GuardedStoppedCandidateScheduleWitness
      event deadline returns escapeChance) :
    ∀ omega, h.past omega ≤ h.start omega :=
  self_le_nextVisitBefore fun omega ↦ (h.past_lt_deadline omega).le

theorem start_le_deadline
    (h : GuardedStoppedCandidateScheduleWitness
      event deadline returns escapeChance) :
    ∀ omega, h.start omega ≤ deadline :=
  nextVisitBefore_le_deadline _ _ _

theorem target_observable
    (h : GuardedStoppedCandidateScheduleWitness
      event deadline returns escapeChance) (x : Point) :
    IsMeasurableAtStopping h.start {omega | h.target omega = x} :=
  stoppedLocation_fiber_observable h.start_isStopping x

theorem start_at_target
    (h : GuardedStoppedCandidateScheduleWitness
      event deadline returns escapeChance) (omega : StepPath) :
    trajectory omega (h.start omega) = h.target omega := rfl

theorem target_eq_candidate_of_start_lt
    (h : GuardedStoppedCandidateScheduleWitness
      event deadline returns escapeChance)
    {omega : StepPath} (hlt : h.start omega < deadline) :
    h.target omega = h.candidate omega :=
  trajectory_nextVisitBefore_eq_target_of_lt hlt

/-- The sound guarded ladder stage for the explicit-schedule witness. -/
def stage
    (h : GuardedStoppedCandidateScheduleWitness
      event deadline returns escapeChance) (r : ℕ) : Set StepPath :=
  (screenedReturnLadderStage h.past h.start h.target deadline
      h.oldFavorite r ∩ h.guard) ∩
    {omega | h.start omega < deadline}

theorem event_mem_stage
    (h : GuardedStoppedCandidateScheduleWitness
      event deadline returns escapeChance)
    {omega : StepPath} (homega : trajectory omega ∈ event) :
    omega ∈ h.stage returns := by
  obtain ⟨times, hmono, hafter, hbefore, hvisit, havoid⟩ :=
    h.event_schedule omega homega
  have hschedule : HasStrictVisitSchedule h.past h.candidate deadline
      (returns + 1) omega :=
    ⟨times, hmono, hafter, hbefore, hvisit⟩
  have hreturn : omega ∈ returnLadderStage h.start h.target deadline returns :=
    returnLadderStage_of_strictVisitSchedule hschedule
  have hstartLt : h.start omega < deadline := by
    apply (nextVisitBefore_lt_deadline_iff omega).2
    exact ⟨times ⟨0, Nat.zero_lt_succ returns⟩,
      hbefore _, hafter _, hvisit _⟩
  have htarget : h.target omega = h.candidate omega :=
    h.target_eq_candidate_of_start_lt hstartLt
  have hclockLe :
      returnLadder h.start h.target deadline returns omega ≤
        times ⟨returns, Nat.lt_succ_self returns⟩ := by
    exact returnLadder_le_visitTime times hmono hafter hbefore hvisit
      ⟨returns, Nat.lt_succ_self returns⟩
  refine ⟨⟨⟨⟨hreturn, ?_⟩, ?_⟩, h.event_guard homega⟩, hstartLt⟩
  · intro heq
    exact h.event_distinct omega homega (heq.trans htarget)
  · intro q hpast hq
    exact havoid q hpast (hq.trans hclockLe)

/-- The explicit schedule produces the same full-tail certificate as the
fixed-deadline guarded witness, without extending old-site avoidance beyond
the random terminal clock. -/
noncomputable def toPointBeforeReturnCertificate
    (h : GuardedStoppedCandidateScheduleWitness
      event deadline returns escapeChance) :
    PointBeforeReturnCertificate event returns where
  stage := h.stage
  stop := returnLadder h.start h.target deadline
  relativePoint := fun _ omega ↦ h.oldFavorite omega - h.target omega
  event_subset := fun _ homega ↦ h.event_mem_stage homega
  stop_isStopping := fun r _hr ↦
    returnLadder_isFiniteStoppingTime h.start_isStopping h.start_le_deadline
      h.target_observable r
  spatial_observable := by
    intro r _hr x
    have hstop : IsFiniteStoppingTime
        (returnLadder h.start h.target deadline r) :=
      returnLadder_isFiniteStoppingTime h.start_isStopping h.start_le_deadline
        h.target_observable r
    have hguardStart : IsMeasurableAtStopping h.start h.guard :=
      IsMeasurableAtStopping.mono_time h.guard_observable h.start_isStopping
        h.past_le_start
    have hguardReturn : IsMeasurableAtStopping
        (returnLadder h.start h.target deadline r) h.guard :=
      IsMeasurableAtStopping.mono_time hguardStart hstop
        (returnLadder_base_le h.start_le_deadline r)
    have hhitStart : IsMeasurableAtStopping h.start
        {omega | h.start omega < deadline} :=
      isMeasurableAtStopping_lt_const h.start_isStopping deadline
    have hhitReturn : IsMeasurableAtStopping
        (returnLadder h.start h.target deadline r)
        {omega | h.start omega < deadline} :=
      IsMeasurableAtStopping.mono_time hhitStart hstop
        (returnLadder_base_le h.start_le_deadline r)
    exact isMeasurableAtStopping_inter
      (isMeasurableAtStopping_inter
        (isMeasurableAtStopping_inter
          (screenedReturnLadderStage_observable h.start_isStopping
            h.start_le_deadline h.target_observable h.past_le_start
            h.oldFavorite_observable r)
          hguardReturn)
        hhitReturn)
      (returnLadder_relativePoint_fiber_observable h.start_isStopping
        h.start_le_deadline h.target_observable h.past_le_start
        h.oldFavorite_observable x)
  next_subset := by
    intro r _hr omega homega
    rcases homega with ⟨⟨hstage, hguard⟩, hhit⟩
    have hnext :=
      screenedReturnLadderStage_succ_subset_pointBeforeReturn_compl
        h.start_le_deadline h.past_le_start h.start_at_target hstage
    exact ⟨⟨⟨hnext.1, hguard⟩, hhit⟩, hnext.2⟩

end GuardedStoppedCandidateScheduleWitness

/-- Sharp geometric cost for a schedule ending by the random terminal
clock. -/
theorem measure_le_geometricReturnCost_of_guardedStoppedCandidateSchedule
    {event : Set WalkPath} {deadline returns : ℕ} {escapeChance : ℝ}
    (hevent : MeasurableSet event)
    (hzero : 0 ≤ escapeChance) (hone : escapeChance ≤ 1)
    (h : GuardedStoppedCandidateScheduleWitness
      event deadline returns escapeChance) :
    simpleRandomWalk event ≤ Gap.geometricReturnCost escapeChance returns := by
  apply measure_le_geometricReturnCost_of_pointBeforeReturnCertificate
    hevent hzero hone h.toPointBeforeReturnCertificate
  intro r _hr omega homega
  have htarget := h.target_eq_candidate_of_start_lt homega.2
  change escapeChance ≤ pointBeforeReturnProbability
    (h.oldFavorite omega - h.target omega)
  rw [htarget]
  have hdistinct : h.oldFavorite omega ≠ h.candidate omega := by
    intro heq
    exact homega.1.1.1.2 (heq.trans htarget.symm)
  exact h.guard_lower omega homega.1.2 hdistinct

/-! ## Instantiation by the genuine threshold clocks -/

/-- Spatial mesh cell determined by the stopped old position and the random
candidate slot. -/
def randomClockBandSpatialGuard
    (m cutoff : ℕ) (band : RandomClockBand) (slot : ℕ) : Set StepPath :=
  {omega | gapScaleOf m
      (trajectory omega
        (truncatedLevelTime m band.oldRank cutoff omega))
      (randomClockSlotCandidatePoint m cutoff band slot omega) = band.scale}

theorem randomClockBandSpatialGuard_observable
    (m cutoff : ℕ) (band : RandomClockBand) (slot : ℕ) :
    IsMeasurableAtStopping
      (truncatedLevelTime m band.oldRank cutoff)
      (randomClockBandSpatialGuard m cutoff band slot) := by
  have hold : ∀ x, IsMeasurableAtStopping
      (truncatedLevelTime m band.oldRank cutoff)
      {omega | trajectory omega
        (truncatedLevelTime m band.oldRank cutoff omega) = x} := by
    intro x
    simpa only [stoppedLocation] using
      (stoppedLocation_fiber_observable
        (isFiniteStoppingTime_truncatedLevelTime m band.oldRank cutoff) x)
  have hcandidate := randomClockSlotCandidatePoint_observable
    m cutoff band slot
  simpa only [randomClockBandSpatialGuard] using
    (isMeasurableAtStopping_binary_fiber hold hcandidate
      (fun old candidate ↦ gapScaleOf m old candidate) band.scale)

/-- A random-clock slot carries the sound full-tail schedule witness.  Its
deterministic cap is used only to make the clocks finite; every screened
return occurs by the random new-creation time. -/
noncomputable def randomClockBandSlotScheduleWitness
    (m cutoff : ℕ) (band : RandomClockBand) (slot : ℕ) :
    GuardedStoppedCandidateScheduleWitness
      (slotSuccessEvent (randomClockBandSites m cutoff)
        (RandomClockPairRealizes m cutoff) band slot)
      (cutoff + 1) band.returns
      (meshPointEscapeChance m band.scale) where
  past := truncatedLevelTime m band.oldRank cutoff
  candidate := randomClockSlotCandidatePoint m cutoff band slot
  oldFavorite := fun omega ↦ trajectory omega
    (truncatedLevelTime m band.oldRank cutoff omega)
  past_isStopping :=
    isFiniteStoppingTime_truncatedLevelTime m band.oldRank cutoff
  past_lt_deadline := fun omega ↦
    Nat.lt_succ_of_le (truncatedLevelTime_le m band.oldRank cutoff omega)
  candidate_observable := randomClockSlotCandidatePoint_observable
    m cutoff band slot
  oldFavorite_observable := by
    intro x
    simpa only [stoppedLocation] using
      (stoppedLocation_fiber_observable
        (isFiniteStoppingTime_truncatedLevelTime m band.oldRank cutoff) x)
  guard := randomClockBandSpatialGuard m cutoff band slot
  guard_observable := randomClockBandSpatialGuard_observable
    m cutoff band slot
  event_guard := by
    intro omega homega
    obtain ⟨x, hslot, hrealizes⟩ := homega
    have hcandidate :
        randomClockSlotCandidatePoint m cutoff band slot omega = x :=
      randomClockSlotCandidatePoint_eq_of_slot hslot
    change gapScaleOf m
      (trajectory omega
        (truncatedLevelTime m band.oldRank cutoff omega))
      (randomClockSlotCandidatePoint m cutoff band slot omega) = band.scale
    rw [hcandidate]
    have hx : x = trajectory omega
        (truncatedLevelTime m band.newRank cutoff omega) := by
      simpa only [RandomClockPairRealizes,
        pathTruncatedLevelTime_trajectory] using hrealizes.1.2.2.2.2.2.2
    rw [hx]
    simpa only [RandomClockPairRealizes,
      pathTruncatedLevelTime_trajectory] using hrealizes.1.2.2.2.2.1
  event_distinct := by
    intro omega homega
    obtain ⟨x, hslot, hrealizes⟩ := homega
    have hcandidate :
        randomClockSlotCandidatePoint m cutoff band slot omega = x :=
      randomClockSlotCandidatePoint_eq_of_slot hslot
    change trajectory omega
      (truncatedLevelTime m band.oldRank cutoff omega) ≠
        randomClockSlotCandidatePoint m cutoff band slot omega
    rw [hcandidate]
    have hx : x = trajectory omega
        (truncatedLevelTime m band.newRank cutoff omega) := by
      simpa only [RandomClockPairRealizes,
        pathTruncatedLevelTime_trajectory] using hrealizes.1.2.2.2.2.2.2
    rw [hx]
    exact creation_locations_ne band.oldRank_pos band.newRank_pos band.rank_lt
      (by simpa only [RandomClockPairRealizes,
        pathTruncatedLevelTime_trajectory] using hrealizes.1.1)
      (by simpa only [RandomClockPairRealizes,
        pathTruncatedLevelTime_trajectory] using hrealizes.1.2.1)
  event_schedule := by
    intro omega homega
    obtain ⟨x, hslot, hrealizes⟩ := homega
    let nOld := truncatedLevelTime m band.oldRank cutoff omega
    let nNew := truncatedLevelTime m band.newRank cutoff omega
    let nTerminal := truncatedLevelTime m 4 cutoff omega
    have hold : ThresholdCreation (trajectory omega) m band.oldRank nOld := by
      simpa only [RandomClockPairRealizes, pathTruncatedLevelTime_trajectory,
        nOld, nNew, nTerminal] using hrealizes.1.1
    have hnew : ThresholdCreation (trajectory omega) m band.newRank nNew := by
      simpa only [RandomClockPairRealizes, pathTruncatedLevelTime_trajectory,
        nOld, nNew, nTerminal] using hrealizes.1.2.1
    have hnext : thresholdCount (trajectory omega) nTerminal (m + 1) = 0 := by
      simpa only [RandomClockPairRealizes, pathTruncatedLevelTime_trajectory,
        nOld, nNew, nTerminal] using hrealizes.1.2.2.1
    have hnewTerminal : nNew ≤ nTerminal := by
      simpa only [RandomClockPairRealizes, pathTruncatedLevelTime_trajectory,
        nOld, nNew, nTerminal] using hrealizes.1.2.2.2.1
    have hcandidate :
        randomClockSlotCandidatePoint m cutoff band slot omega = x :=
      randomClockSlotCandidatePoint_eq_of_slot hslot
    have hx : x = trajectory omega nNew := by
      simpa only [RandomClockPairRealizes, pathTruncatedLevelTime_trajectory,
        nOld, nNew, nTerminal] using hrealizes.1.2.2.2.2.2.2
    have hreturn : localTime (trajectory omega) nOld x +
        (band.returns + 1) ≤ m := by
      simpa only [RandomClockPairRealizes, pathTruncatedLevelTime_trajectory,
        nOld, nNew, nTerminal] using hrealizes.2
    have hthreshold : m ≤ localTime (trajectory omega) nNew x := by
      rw [hx]
      exact (mem_thresholdSites (trajectory omega) nNew m
        (trajectory omega nNew)).mp
          (position_mem_thresholdSites_of_creation band.newRank_pos hnew) |>.2
    have holdNew : nOld < nNew :=
      creation_time_lt band.oldRank_pos band.newRank_pos band.rank_lt hold hnew
    have hgain : localTime (trajectory omega) nOld
        (randomClockSlotCandidatePoint m cutoff band slot omega) +
          (band.returns + 1) ≤
        localTime (trajectory omega) nNew
          (randomClockSlotCandidatePoint m cutoff band slot omega) := by
      rw [hcandidate]
      exact hreturn.trans hthreshold
    have hschedule : HasStrictVisitSchedule
        (truncatedLevelTime m band.oldRank cutoff)
        (randomClockSlotCandidatePoint m cutoff band slot)
        (nNew + 1) (band.returns + 1) omega := by
      apply hasStrictVisitSchedule_of_localTime_gain
        (past := truncatedLevelTime m band.oldRank cutoff)
        (target := randomClockSlotCandidatePoint m cutoff band slot)
      · simpa only [nOld] using Nat.lt_succ_of_lt holdNew
      · simpa only [Nat.add_sub_cancel] using hgain
    obtain ⟨times, hmono, hafter, hbeforeNew, hvisit⟩ := hschedule
    refine ⟨times, hmono, hafter, ?_, hvisit, ?_⟩
    · intro i
      exact (hbeforeNew i).trans_le
        (Nat.succ_le_succ (truncatedLevelTime_le m band.newRank cutoff omega))
    · intro q hpast hq
      have hlastNew :
          times ⟨band.returns, Nat.lt_succ_self band.returns⟩ ≤ nNew :=
        Nat.lt_succ_iff.mp (hbeforeNew _)
      have havoid := no_oldCreation_visit_of_no_next_level
        band.oldRank_pos hold hnext
      exact havoid q (by simpa only [nOld] using hpast)
        ((hq.trans hlastNew).trans hnewTerminal)
  guard_lower := by
    intro omega hguard hdistinct
    exact meshPointEscapeChance_le_pointBeforeReturnProbability
      band.scale_proper hguard hdistinct

/-- Per-slot sharp bound at genuine random creation clocks. -/
theorem measure_randomClockBandSlotSuccess_le_geometric
    (m cutoff : ℕ) (band : RandomClockBand) (slot : ℕ) :
    simpleRandomWalk
        (slotSuccessEvent (randomClockBandSites m cutoff)
          (RandomClockPairRealizes m cutoff) band slot) ≤
      Gap.geometricReturnCost
        (meshPointEscapeChance m band.scale) band.returns := by
  exact measure_le_geometricReturnCost_of_guardedStoppedCandidateSchedule
    (measurableSet_randomClockBandSlotSuccess m cutoff band slot)
    (meshPointEscapeChance_pos m band.scale).le
    (meshPointEscapeChance_le_one m band.scale)
    (randomClockBandSlotScheduleWitness m cutoff band slot)

/-! ## Finite band-only screen -/

/-- Sound deterministic extraction interface.  Lazy-good classification is
used to prove this predicate; candidate overflow is already excluded in the
`PathGapWitness` premise.  Crucially, the finite index contains no clock
values. -/
def RandomClockBandExtraction
    (t : DominoTiling) (m cutoff : ℕ) (bands : Finset RandomClockBand) : Prop :=
  PathGapWitness (onTimeGapDeficitExceptionalEvent t m) bands
    (randomClockBandSites m cutoff)
    (fun band ↦ candidateBudget48 m band.beta)
    (RandomClockPairRealizes m cutoff)

/-- The complete random-clock gap screen.  The only union is over the
finite beta/geometric bands and their Proposition 4.8 candidate slots; no
factor depending on the number of possible old/new creation times occurs. -/
theorem measure_onTimeGapDeficitExceptionalEvent_le_randomClockScreen
    (t : DominoTiling) (m cutoff : ℕ) (bands : Finset RandomClockBand)
    (hextract : RandomClockBandExtraction t m cutoff bands) :
    simpleRandomWalk (onTimeGapDeficitExceptionalEvent t m) ≤
      simpleRandomWalk
        (candidateOverflow bands (randomClockBandSites m cutoff)
          (fun band ↦ candidateBudget48 m band.beta)) +
        ∑ band ∈ bands,
          (candidateBudget48 m band.beta : ℝ≥0∞) *
            Gap.geometricReturnCost
              (meshPointEscapeChance m band.scale) band.returns := by
  let sites := randomClockBandSites m cutoff
  let budget : RandomClockBand → ℕ := fun band ↦
    candidateBudget48 m band.beta
  let realizes := RandomClockPairRealizes m cutoff
  let overflow := candidateOverflow bands sites budget
  let screened := onTimeGapDeficitExceptionalEvent t m \ overflow
  have hsplit : onTimeGapDeficitExceptionalEvent t m ⊆
      overflow ∪ screened := by
    intro s hs
    by_cases hoverflow : s ∈ overflow
    · exact Or.inl hoverflow
    · exact Or.inr ⟨hs, hoverflow⟩
  calc
    simpleRandomWalk (onTimeGapDeficitExceptionalEvent t m) ≤
        simpleRandomWalk (overflow ∪ screened) := measure_mono hsplit
    _ ≤ simpleRandomWalk overflow + simpleRandomWalk screened :=
      measure_union_le _ _
    _ ≤ simpleRandomWalk overflow +
        ∑ band ∈ bands, (budget band : ℝ≥0∞) *
          Gap.geometricReturnCost
            (meshPointEscapeChance m band.scale) band.returns := by
      gcongr
      exact Gap.measure_gapEvent_le_geometric_sum simpleRandomWalk screened bands
        (fun band ↦ Finset.range (budget band))
        (slotSuccessEvent sites realizes) budget
        (fun band ↦ meshPointEscapeChance m band.scale)
        RandomClockBand.returns
        (by
          dsimp only [screened, overflow]
          exact gapEvent_diff_overflow_covered_by_slots
            (onTimeGapDeficitExceptionalEvent t m) bands sites budget realizes
            hextract)
        (range_candidateCountBound bands budget)
        (by
          intro band _hband slot _hslot
          exact measure_randomClockBandSlotSuccess_le_geometric
            m cutoff band slot)

/-- Eventual Harnack wrapper with an abstract candidate-overflow estimate.
This is the quantitative seam supplied by Proposition 4.8/lazy-good
screening; its numerical sum contains no time-atom multiplicity. -/
theorem hasGapDeficitReturnHarnack_of_randomClockScreen
    (c : ℝ)
    (bands : DominoTiling → ℕ → Finset RandomClockBand)
    (hextract : ∀ t m,
      RandomClockBandExtraction t m (levelCutoffTime upperTailDelta m)
        (bands t m))
    (overflowCost : DominoTiling → ℕ → ℝ≥0∞)
    (hoverflow : ∀ t, ∀ᶠ m : ℕ in atTop,
      simpleRandomWalk
          (candidateOverflow (bands t m)
            (randomClockBandSites m (levelCutoffTime upperTailDelta m))
            (fun band ↦ candidateBudget48 m band.beta)) ≤
        overflowCost t m)
    (hnumeric : ∀ t, ∀ᶠ m : ℕ in atTop,
      overflowCost t m +
          ∑ band ∈ bands t m,
            (candidateBudget48 m band.beta : ℝ≥0∞) *
              Gap.geometricReturnCost
                (meshPointEscapeChance m band.scale) band.returns ≤
        ENNReal.ofReal (Real.exp (-c * Real.log (m : ℝ) ^ 2))) :
    HLOZUpperEstimates.HasGapDeficitReturnHarnack c := by
  intro t
  filter_upwards [hoverflow t, hnumeric t] with m hoverflowM hnumericM
  refine (measure_onTimeGapDeficitExceptionalEvent_le_randomClockScreen
    t m (levelCutoffTime upperTailDelta m) (bands t m) (hextract t m)).trans ?_
  calc
    simpleRandomWalk
          (candidateOverflow (bands t m)
            (randomClockBandSites m (levelCutoffTime upperTailDelta m))
            (fun band ↦ candidateBudget48 m band.beta)) +
        ∑ band ∈ bands t m,
          (candidateBudget48 m band.beta : ℝ≥0∞) *
            Gap.geometricReturnCost
              (meshPointEscapeChance m band.scale) band.returns ≤
        overflowCost t m +
          ∑ band ∈ bands t m,
            (candidateBudget48 m band.beta : ℝ≥0∞) *
              Gap.geometricReturnCost
                (meshPointEscapeChance m band.scale) band.returns := by
      gcongr
    _ ≤ ENNReal.ofReal (Real.exp (-c * Real.log (m : ℝ) ^ 2)) := hnumericM

end

end Erdos1165.HLOZGapRandomClockScreen
