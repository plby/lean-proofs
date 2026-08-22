/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
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

import ErdosProblems.Erdos1165.TerminalVisitSpliceInvariance

/-!
# Invariance of excursion clocks under first-hit splices

The compressed terminal skeleton deletes finitely many inner-to-outer path
words.  Replacing such a word changes all later absolute times, so ordinary
finite-prefix congruence does not apply.  What the alternating excursion
clock actually uses is much smaller: each retained piece makes its prescribed
first hit of the inner boundary, and each inserted word makes its prescribed
first hit of the outer boundary.  The duration and the interior of a word are
irrelevant.

`FirstHitExcursionSchedule` records precisely this clock-visible data.
`EndpointMatchedExcursionSplice` pairs two schedules and additionally records
that corresponding word endpoints agree, which is the form produced by an
endpoint-preserving terminal-skeleton splice.  The main results show that the
completed-excursion count, the terminal count, and the whole excursion profile
are invariant.  No equality of horizons or removed-word lengths is assumed.
-/

open Set

namespace Erdos1165.TerminalClockSplice

open ThickPoint TerminalExcursionPathwise
open TerminalSkeletonWords TerminalSequentialVisitLaw
open MarkedBridgeFactorization TerminalVisitSpliceInvariance

noncomputable section

/-! ## First-hit certificates -/

/-- `stop` is the first visit to `A` in the interval from `start` through
`horizon`.  This formulation is independent of the implementation of the
finite first-hit clock and is convenient for finite path words. -/
def IsFirstHitSegment (s : WalkPath) (A : Set Point)
    (start stop horizon : ℕ) : Prop :=
  start ≤ stop ∧ stop ≤ horizon ∧ s stop ∈ A ∧
    ∀ q, start ≤ q → q < stop → s q ∉ A

/-- There is no visit to `A` from `start` through `horizon`. -/
def AvoidsThrough (s : WalkPath) (A : Set Point)
    (start horizon : ℕ) : Prop :=
  ∀ q, start ≤ q → q ≤ horizon → s q ∉ A

theorem firstHitThrough_eq_of_isFirstHitSegment
    (s : WalkPath) (A : Set Point) [DecidablePred (· ∈ A)]
    {start stop horizon : ℕ}
    (h : IsFirstHitSegment s A start stop horizon) :
    firstHitThrough s A start horizon = stop := by
  have hstop : stop ∈ hitTimesThrough s A start horizon := by
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_Icc.mpr ⟨h.1, h.2.1⟩, h.2.2.1⟩
  have hnonempty : (hitTimesThrough s A start horizon).Nonempty := ⟨stop, hstop⟩
  have hfirst := firstHitThrough_mem_of_nonempty s A start horizon hnonempty
  have hfirstInterval := Finset.mem_Icc.mp (Finset.mem_filter.mp hfirst).1
  have hfirstMem : s (firstHitThrough s A start horizon) ∈ A :=
    (Finset.mem_filter.mp hfirst).2
  apply le_antisymm
  · have hmin := Finset.min'_le (hitTimesThrough s A start horizon) stop hstop
    simpa only [firstHitThrough, dif_pos hnonempty] using hmin
  · by_contra hnot
    have hlt : firstHitThrough s A start horizon < stop := Nat.lt_of_not_ge hnot
    exact h.2.2.2 _ hfirstInterval.1 hlt hfirstMem

theorem firstHitThrough_eq_sentinel_of_avoidsThrough
    (s : WalkPath) (A : Set Point) [DecidablePred (· ∈ A)]
    {start horizon : ℕ} (h : AvoidsThrough s A start horizon) :
    firstHitThrough s A start horizon = horizon + 1 := by
  apply firstHitThrough_eq_sentinel_of_empty
  rintro ⟨q, hq⟩
  have hq' := Finset.mem_filter.mp hq
  have hqInterval := Finset.mem_Icc.mp hq'.1
  exact h q hqInterval.1 hqInterval.2 hq'.2

/-- A completed implementation-level first hit gives the corresponding
word-level first-hit certificate. -/
theorem isFirstHitSegment_firstHitThrough_of_le
    (s : WalkPath) (A : Set Point) [DecidablePred (· ∈ A)]
    (start horizon : ℕ)
    (hcomplete : firstHitThrough s A start horizon ≤ horizon) :
    IsFirstHitSegment s A start
      (firstHitThrough s A start horizon) horizon := by
  have hnonempty :=
    (firstHitThrough_le_horizon_iff s A start horizon).mp hcomplete
  have hmem := firstHitThrough_mem_of_nonempty s A start horizon hnonempty
  have hinterval := Finset.mem_Icc.mp (Finset.mem_filter.mp hmem).1
  refine ⟨hinterval.1, hcomplete, (Finset.mem_filter.mp hmem).2, ?_⟩
  intro q hstartq hq hqA
  have hqhorizon : q ≤ horizon := hq.le.trans hcomplete
  have hqmem : q ∈ hitTimesThrough s A start horizon :=
    Finset.mem_filter.mpr
      ⟨Finset.mem_Icc.mpr ⟨hstartq, hqhorizon⟩, hqA⟩
  have hmin := Finset.min'_le (hitTimesThrough s A start horizon) q hqmem
  have hhit : firstHitThrough s A start horizon =
      (hitTimesThrough s A start horizon).min' hnonempty := by
    simp only [firstHitThrough, dif_pos hnonempty]
  exact (Nat.not_le_of_gt hq) (by simpa only [hhit] using hmin)

/-- Conversely, a sentinel-valued first-hit clock means that the path avoids
the target set throughout the searched interval. -/
theorem avoidsThrough_of_firstHitThrough_eq_sentinel
    (s : WalkPath) (A : Set Point) [DecidablePred (· ∈ A)]
    {start horizon : ℕ}
    (hfirst : firstHitThrough s A start horizon = horizon + 1) :
    AvoidsThrough s A start horizon := by
  intro q hstartq hqhorizon hqA
  have hnonempty : (hitTimesThrough s A start horizon).Nonempty := by
    refine ⟨q, Finset.mem_filter.mpr ?_⟩
    exact ⟨Finset.mem_Icc.mpr ⟨hstartq, hqhorizon⟩, hqA⟩
  have hle := (firstHitThrough_le_horizon_iff s A start horizon).2 hnonempty
  rw [hfirst] at hle
  omega

/-! ## Moving finite first-hit words into a global path -/

/-- An absolute first-hit certificate on the shifted increment path becomes
an `IsFirstHitSegment` certificate on the global trajectory. -/
theorem isFirstHitSegment_of_shifted_absoluteBoundaryFirstAt
    (omega : StepPath) (boundary : Set Point)
    {wordStart wordStop duration horizon : ℕ} {startPoint : Point}
    (hposition : trajectory omega wordStart = startPoint)
    (hstop : wordStart + duration = wordStop)
    (hhorizon : wordStop ≤ horizon)
    (hfirst : AbsoluteBoundaryFirstAt boundary startPoint
      (shiftSteps wordStart omega) duration) :
    IsFirstHitSegment (trajectory omega) boundary wordStart wordStop horizon := by
  have hstartStop : wordStart ≤ wordStop := by omega
  refine ⟨hstartStop, hhorizon, ?_, ?_⟩
  · rw [← hstop, ← trajectoryFrom_shiftSteps_eq, hposition]
    exact hfirst.1
  · intro q hstartq hqstop hqBoundary
    let r := q - wordStart
    have hadd : wordStart + r = q := Nat.add_sub_of_le hstartq
    have hr : r < duration := by omega
    apply hfirst.2 r hr
    rw [← hposition, trajectoryFrom_shiftSteps_eq, hadd]
    exact hqBoundary

/-- Transport a first-hit segment across two equal path blocks.  Absolute
times and ambient horizons may change, but the block duration and every
position relative to its left endpoint agree. -/
theorem IsFirstHitSegment.transport_equalBlock
    {left right : WalkPath} {A : Set Point}
    {leftStart leftStop leftHorizon rightStart rightStop rightHorizon
      duration : ℕ}
    (h : IsFirstHitSegment left A leftStart leftStop leftHorizon)
    (hleftStop : leftStart + duration = leftStop)
    (hrightStop : rightStart + duration = rightStop)
    (hrightHorizon : rightStop ≤ rightHorizon)
    (hpath : ∀ q ≤ duration,
      left (leftStart + q) = right (rightStart + q)) :
    IsFirstHitSegment right A rightStart rightStop rightHorizon := by
  have hrightStartStop : rightStart ≤ rightStop := by omega
  refine ⟨hrightStartStop, hrightHorizon, ?_, ?_⟩
  · have hend := hpath duration le_rfl
    rw [hleftStop, hrightStop] at hend
    exact hend ▸ h.2.2.1
  · intro q hrightStartQ hqRightStop hqA
    let r := q - rightStart
    have hrAdd : rightStart + r = q := Nat.add_sub_of_le hrightStartQ
    have hrDuration : r < duration := by omega
    have hleftStartR : leftStart ≤ leftStart + r := Nat.le_add_right _ _
    have hleftRStop : leftStart + r < leftStop := by omega
    apply h.2.2.2 (leftStart + r) hleftStartR hleftRStop
    rw [hpath r hrDuration.le, hrAdd]
    exact hqA

/-- A canonical admissible replacement list is a literal first-hit segment
at its exact offsets inside the reconstructed alternating concatenation. -/
theorem isFirstHitSegment_replacementWord_of_admissible
    {m : ℕ} (pieces : Fin (m + 1) → List Direction)
    (words : TerminalSegmentWords m) (boundary : Set Point)
    (target : Point) (starts endpoints : Fin m → Point)
    (visits : Fin m → ℕ) (horizon : ℕ) (j : Fin m)
    (hposition : trajectory (reconstructedTerminalStepPath pieces words)
        (replacementWordStart m pieces words j) = starts j)
    (hadmissible : AdmissibleReplacementWord boundary target
      (starts j) (endpoints j) (visits j) (words j))
    (hhorizon : replacementWordStop pieces words j ≤ horizon) :
    IsFirstHitSegment
      (trajectory (reconstructedTerminalStepPath pieces words)) boundary
      (replacementWordStart m pieces words j)
      (replacementWordStop pieces words j) horizon := by
  let omega := reconstructedTerminalStepPath pieces words
  let start := replacementWordStart m pieces words j
  have hmem : shiftSteps start omega ∈
      stoppedWordCylinder (stoppedWordOfList (words j)) := by
    exact shift_reconstructed_mem_stoppedWordCylinder pieces words j
  have hfirst : AbsoluteBoundaryFirstAt boundary (starts j)
      (shiftSteps start omega) (words j).length :=
    absoluteBoundaryFirstAt_of_mem_stoppedWordCylinder hmem hadmissible.1
  apply isFirstHitSegment_of_shifted_absoluteBoundaryFirstAt omega boundary
    (wordStart := start) (wordStop := replacementWordStop pieces words j)
    (duration := (words j).length) hposition
  · dsimp [start]
    rfl
  · exact hhorizon
  · exact hfirst

/-- Unmarked canonical boundary words are admissible after marking them by
their literal target-visit count. -/
theorem admissibleReplacementWord_of_boundaryExitWordCode
    (boundary : Set Point) (target start endpoint : Point)
  (bridge : BoundaryExitWordCode boundary start endpoint) :
    AdmissibleReplacementWord boundary target start endpoint
      (replacementWordVisitCount start target (List.ofFn bridge.1.2))
      (List.ofFn bridge.1.2) := by
  simpa [AdmissibleReplacementWord, replacementWordVisitCount,
    extendStoppedWord_stoppedWordOfList_ofFn] using bridge.2

lemma excursionStart_succ_eq_firstHitThrough_finish_global
    (s : WalkPath) (outer inner : Set Point)
    [DecidablePred (· ∈ outer)] [DecidablePred (· ∈ inner)]
    (horizon j : ℕ) :
    excursionStart s outer inner horizon (j + 1) =
      firstHitThrough s outer
        (excursionFinish s outer inner horizon j) horizon := by
  rw [excursionFinish_eq_iterate_succ]
  rfl

/-- Concrete terminal-clock identification for an alternating concatenation.
The retained pieces supply the inward first-hit clauses; admissibility of the
inserted words supplies every outward first-hit clause automatically. -/
theorem terminalClocks_reconstructed_eq_replacementOffsets
    {m : ℕ} (hm : 0 < m)
    (pieces : Fin (m + 1) → List Direction)
    (words : TerminalSegmentWords m)
    (outer inner : Set Point) (target : Point)
    (starts endpoints : Fin m → Point) (visits : Fin m → ℕ)
    (horizon initialOuterTime : ℕ)
    [DecidablePred (· ∈ outer)] [DecidablePred (· ∈ inner)]
    (hhorizon : (alternatingConcat m pieces words).length ≤ horizon)
    (hfirstOuter : IsFirstHitSegment
      (trajectory (reconstructedTerminalStepPath pieces words)) outer
      0 initialOuterTime horizon)
    (hfirstInnerZero : IsFirstHitSegment
      (trajectory (reconstructedTerminalStepPath pieces words)) inner
      initialOuterTime
      (replacementWordStart m pieces words ⟨0, hm⟩) horizon)
    (hfirstInnerSucc : ∀ (j : Fin m) (hj : (j : ℕ) + 1 < m),
      IsFirstHitSegment
        (trajectory (reconstructedTerminalStepPath pieces words)) inner
        (replacementWordStop pieces words j)
        (replacementWordStart m pieces words ⟨(j : ℕ) + 1, hj⟩)
        horizon)
    (hposition : ∀ j,
      trajectory (reconstructedTerminalStepPath pieces words)
        (replacementWordStart m pieces words j) = starts j)
    (hadmissible : ∀ j,
      AdmissibleReplacementWord outer target
        (starts j) (endpoints j) (visits j) (words j)) :
    ∀ j : Fin m,
      excursionFinish
          (trajectory (reconstructedTerminalStepPath pieces words))
          outer inner horizon j = replacementWordStart m pieces words j ∧
      excursionStart
          (trajectory (reconstructedTerminalStepPath pieces words))
          outer inner horizon ((j : ℕ) + 1) =
        replacementWordStop pieces words j := by
  let s := trajectory (reconstructedTerminalStepPath pieces words)
  have houterWord (j : Fin m) :
      IsFirstHitSegment s outer
        (replacementWordStart m pieces words j)
        (replacementWordStop pieces words j) horizon := by
    apply isFirstHitSegment_replacementWord_of_admissible pieces words outer
      target starts endpoints visits horizon j (hposition j) (hadmissible j)
    exact (replacementWordStop_le_alternatingConcat_length pieces words j).trans
      hhorizon
  have hclock : ∀ (k : ℕ) (hk : k < m),
      excursionFinish s outer inner horizon k =
          replacementWordStart m pieces words ⟨k, hk⟩ ∧
      excursionStart s outer inner horizon (k + 1) =
          replacementWordStop pieces words ⟨k, hk⟩ := by
    intro k
    induction k with
    | zero =>
        intro hk
        have hstartZero : excursionStart s outer inner horizon 0 =
            initialOuterTime := by
          simpa [excursionStart, s] using
            firstHitThrough_eq_of_isFirstHitSegment s outer hfirstOuter
        have hfinishZero : excursionFinish s outer inner horizon 0 =
            replacementWordStart m pieces words ⟨0, hk⟩ := by
          unfold excursionFinish
          rw [hstartZero]
          exact firstHitThrough_eq_of_isFirstHitSegment s inner
            (by simpa only [Subsingleton.elim hk hm] using hfirstInnerZero)
        refine ⟨hfinishZero, ?_⟩
        rw [excursionStart_succ_eq_firstHitThrough_finish_global,
          hfinishZero]
        exact firstHitThrough_eq_of_isFirstHitSegment s outer
          (houterWord ⟨0, hk⟩)
    | succ k ih =>
        intro hk
        have hkprev : k < m := by omega
        have hprev := ih hkprev
        let prev : Fin m := ⟨k, hkprev⟩
        let current : Fin m := ⟨k + 1, hk⟩
        have hfinish : excursionFinish s outer inner horizon (k + 1) =
            replacementWordStart m pieces words current := by
          unfold excursionFinish
          rw [hprev.2]
          exact firstHitThrough_eq_of_isFirstHitSegment s inner
            (by simpa [prev, current] using hfirstInnerSucc prev hk)
        refine ⟨hfinish, ?_⟩
        rw [excursionStart_succ_eq_firstHitThrough_finish_global,
          hfinish]
        exact firstHitThrough_eq_of_isFirstHitSegment s outer
          (houterWord current)
  intro j
  simpa only [Fin.eta] using hclock (j : ℕ) j.isLt

/-! ## Alternating schedules and their exact count -/

/-- A complete alternating first-hit description of exactly `count`
outer-to-inner excursions.  `outerTime (j+1)` is the endpoint of the
arbitrary inner-to-outer word following `innerTime j`.  Its only clock-visible
property is `firstOuterSucc`: the word first reaches `outer` at that endpoint.

The final `noFinalInner` clause says that after the last outer endpoint there
is no further completed inward excursion before the horizon. -/
structure FirstHitExcursionSchedule (s : WalkPath)
    (outer inner : Set Point) (horizon count : ℕ) where
  count_le : count ≤ horizon + 1
  outerTime : ℕ → ℕ
  innerTime : ℕ → ℕ
  firstOuterZero : IsFirstHitSegment s outer 0 (outerTime 0) horizon
  firstInner : ∀ j, j < count →
    IsFirstHitSegment s inner (outerTime j) (innerTime j) horizon
  firstOuterSucc : ∀ j, j < count →
    IsFirstHitSegment s outer (innerTime j) (outerTime (j + 1)) horizon
  noFinalInner : AvoidsThrough s inner (outerTime count) horizon

/-- Clock data for the first `wordCount` inner-to-outer replacement words of
an alternating concatenation.  `wordStart j` and `wordStop j` are allowed to
be arbitrary offsets; the four first-hit fields are exactly what is obtained
from the retained complementary pieces and canonical boundary-hit words. -/
structure InitialFirstHitWordSchedule (s : WalkPath)
    (outer inner : Set Point) (horizon wordCount : ℕ) where
  wordStart : ℕ → ℕ
  wordStop : ℕ → ℕ
  initialOuterTime : ℕ
  firstOuterZero :
    IsFirstHitSegment s outer 0 initialOuterTime horizon
  firstInnerZero : 0 < wordCount →
    IsFirstHitSegment s inner initialOuterTime (wordStart 0) horizon
  firstInnerSucc : ∀ j, j + 1 < wordCount →
    IsFirstHitSegment s inner (wordStop j) (wordStart (j + 1)) horizon
  firstOuterWord : ∀ j, j < wordCount →
    IsFirstHitSegment s outer (wordStart j) (wordStop j) horizon

namespace FirstHitExcursionSchedule

variable {s : WalkPath} {outer inner : Set Point} {horizon count : ℕ}
  [DecidablePred (· ∈ outer)] [DecidablePred (· ∈ inner)]

lemma excursionStart_succ_eq_firstHitThrough_finish
    (s : WalkPath) (outer inner : Set Point)
    [DecidablePred (· ∈ outer)] [DecidablePred (· ∈ inner)]
    (horizon j : ℕ) :
    excursionStart s outer inner horizon (j + 1) =
      firstHitThrough s outer
        (excursionFinish s outer inner horizon j) horizon := by
  rw [excursionFinish_eq_iterate_succ]
  rfl

/-- Build a splice schedule directly from the actual truncated excursion
clocks.  This is the bridge from clock calculations on an assembled packet to
the abstract duration-invariance theorem. -/
def ofExactClocks
    (s : WalkPath) (outer inner : Set Point)
    [DecidablePred (· ∈ outer)] [DecidablePred (· ∈ inner)]
    (horizon count : ℕ)
    (hcount : count ≤ horizon + 1)
    (houterZero : excursionStart s outer inner horizon 0 ≤ horizon)
    (hinner : ∀ j, j < count →
      excursionFinish s outer inner horizon j ≤ horizon)
    (houterSucc : ∀ j, j < count →
      excursionStart s outer inner horizon (j + 1) ≤ horizon)
    (hnext : excursionFinish s outer inner horizon count = horizon + 1) :
    FirstHitExcursionSchedule s outer inner horizon count where
  count_le := hcount
  outerTime := fun j ↦ excursionStart s outer inner horizon j
  innerTime := fun j ↦ excursionFinish s outer inner horizon j
  firstOuterZero := by
    simpa [excursionStart] using
      isFirstHitSegment_firstHitThrough_of_le s outer
        ((excursionStep s outer inner horizon)^[0] 0) horizon houterZero
  firstInner := by
    intro j hj
    unfold excursionFinish
    exact isFirstHitSegment_firstHitThrough_of_le s inner _ horizon
      (hinner j hj)
  firstOuterSucc := by
    intro j hj
    let hit := firstHitThrough s outer
      (excursionFinish s outer inner horizon j) horizon
    have heq : excursionStart s outer inner horizon (j + 1) = hit :=
      excursionStart_succ_eq_firstHitThrough_finish s outer inner horizon j
    have hbound : hit ≤ horizon := by
      rw [← heq]
      exact houterSucc j hj
    have hseg : IsFirstHitSegment s outer
        (excursionFinish s outer inner horizon j) hit horizon :=
      isFirstHitSegment_firstHitThrough_of_le s outer _ horizon hbound
    exact heq.symm ▸ hseg
  noFinalInner := by
    unfold excursionFinish at hnext
    exact avoidsThrough_of_firstHitThrough_eq_sentinel s inner hnext

theorem excursionStart_eq_outerTime
    (schedule : FirstHitExcursionSchedule s outer inner horizon count) :
    ∀ {j : ℕ}, j ≤ count →
      excursionStart s outer inner horizon j = schedule.outerTime j := by
  intro j hj
  induction j with
  | zero =>
      simpa [excursionStart] using
        firstHitThrough_eq_of_isFirstHitSegment s outer schedule.firstOuterZero
  | succ j ih =>
      have hjlt : j < count := by omega
      have hstart : excursionStart s outer inner horizon j =
          schedule.outerTime j := ih (by omega)
      have hfinish : excursionFinish s outer inner horizon j =
          schedule.innerTime j := by
        unfold excursionFinish
        rw [hstart]
        exact firstHitThrough_eq_of_isFirstHitSegment s inner
          (schedule.firstInner j hjlt)
      rw [excursionStart_succ_eq_firstHitThrough_finish, hfinish]
      exact firstHitThrough_eq_of_isFirstHitSegment s outer
        (schedule.firstOuterSucc j hjlt)

theorem excursionFinish_eq_innerTime
    (schedule : FirstHitExcursionSchedule s outer inner horizon count)
    {j : ℕ} (hj : j < count) :
    excursionFinish s outer inner horizon j = schedule.innerTime j := by
  unfold excursionFinish
  rw [schedule.excursionStart_eq_outerTime hj.le]
  exact firstHitThrough_eq_of_isFirstHitSegment s inner
    (schedule.firstInner j hj)

theorem excursionFinish_eq_sentinel
    (schedule : FirstHitExcursionSchedule s outer inner horizon count) :
    excursionFinish s outer inner horizon count = horizon + 1 := by
  unfold excursionFinish
  rw [schedule.excursionStart_eq_outerTime le_rfl]
  exact firstHitThrough_eq_sentinel_of_avoidsThrough s inner
    schedule.noFinalInner

/-- The alternating first-hit schedule determines the completed-excursion
count exactly, irrespective of the lengths and interiors of its
inner-to-outer pieces. -/
theorem completedExcursionCount_eq
    (schedule : FirstHitExcursionSchedule s outer inner horizon count) :
    completedExcursionCount s outer inner horizon = count := by
  unfold completedExcursionCount
  rw [show count = (Finset.range count).card by simp]
  apply congrArg Finset.card
  ext j
  simp only [Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ⟨jhorizon, hfinish⟩
    by_contra hjnot
    have hcountj : count ≤ j := Nat.le_of_not_gt hjnot
    have hmono := excursionFinish_mono s outer inner horizon hcountj
    have hmono' : excursionFinish s outer inner horizon count ≤
        excursionFinish s outer inner horizon j := hmono
    rw [schedule.excursionFinish_eq_sentinel] at hmono'
    omega
  · intro hjcount
    have hjhorizon : j < horizon + 1 :=
      hjcount.trans_le schedule.count_le
    refine ⟨hjhorizon, ?_⟩
    rw [schedule.excursionFinish_eq_innerTime hjcount]
    exact (schedule.firstInner j hjcount).2.1

end FirstHitExcursionSchedule

namespace InitialFirstHitWordSchedule

variable {s : WalkPath} {outer inner : Set Point} {horizon wordCount : ℕ}
  [DecidablePred (· ∈ outer)] [DecidablePred (· ∈ inner)]

/-- Every replacement word is selected by the literal alternating excursion
clocks.  This is the exact clock-identification result needed by the visit
mark calculation: the inward completion is the word start, and the following
outer hit is the word stop. -/
theorem excursionFinish_eq_wordStart_and_start_succ_eq_wordStop
    (schedule : InitialFirstHitWordSchedule s outer inner horizon wordCount) :
    ∀ j, j < wordCount →
      excursionFinish s outer inner horizon j = schedule.wordStart j ∧
      excursionStart s outer inner horizon (j + 1) = schedule.wordStop j := by
  intro j hj
  induction j with
  | zero =>
      have hstartZero : excursionStart s outer inner horizon 0 =
          schedule.initialOuterTime := by
        simpa [excursionStart] using
          firstHitThrough_eq_of_isFirstHitSegment s outer
            schedule.firstOuterZero
      have hfinishZero : excursionFinish s outer inner horizon 0 =
          schedule.wordStart 0 := by
        unfold excursionFinish
        rw [hstartZero]
        exact firstHitThrough_eq_of_isFirstHitSegment s inner
          (schedule.firstInnerZero hj)
      refine ⟨hfinishZero, ?_⟩
      rw [FirstHitExcursionSchedule.excursionStart_succ_eq_firstHitThrough_finish,
        hfinishZero]
      exact firstHitThrough_eq_of_isFirstHitSegment s outer
        (schedule.firstOuterWord 0 hj)
  | succ j ih =>
      have hjprev : j < wordCount := by omega
      have hprev := ih hjprev
      have hfinish : excursionFinish s outer inner horizon (j + 1) =
          schedule.wordStart (j + 1) := by
        unfold excursionFinish
        rw [hprev.2]
        exact firstHitThrough_eq_of_isFirstHitSegment s inner
          (schedule.firstInnerSucc j hj)
      refine ⟨hfinish, ?_⟩
      rw [FirstHitExcursionSchedule.excursionStart_succ_eq_firstHitThrough_finish,
        hfinish]
      exact firstHitThrough_eq_of_isFirstHitSegment s outer
        (schedule.firstOuterWord (j + 1) hj)

theorem excursionFinish_eq_wordStart
    (schedule : InitialFirstHitWordSchedule s outer inner horizon wordCount)
    {j : ℕ} (hj : j < wordCount) :
    excursionFinish s outer inner horizon j = schedule.wordStart j :=
  (schedule.excursionFinish_eq_wordStart_and_start_succ_eq_wordStop j hj).1

theorem excursionStart_succ_eq_wordStop
    (schedule : InitialFirstHitWordSchedule s outer inner horizon wordCount)
    {j : ℕ} (hj : j < wordCount) :
    excursionStart s outer inner horizon (j + 1) = schedule.wordStop j :=
  (schedule.excursionFinish_eq_wordStart_and_start_succ_eq_wordStop j hj).2

end InitialFirstHitWordSchedule

/-! ## Endpoint-preserving splices -/

/-- Two alternating schedules obtained from one another by replacing the
finitely many inner-to-outer words, with corresponding inner and outer
endpoints unchanged.  The two horizons and all word lengths may differ. -/
structure EndpointMatchedExcursionSplice
    (left right : WalkPath) (outer inner : Set Point)
    (leftHorizon rightHorizon count : ℕ) where
  leftSchedule :
    FirstHitExcursionSchedule left outer inner leftHorizon count
  rightSchedule :
    FirstHitExcursionSchedule right outer inner rightHorizon count
  outerEndpoint_eq : ∀ j, j ≤ count →
    left (leftSchedule.outerTime j) = right (rightSchedule.outerTime j)
  innerEndpoint_eq : ∀ j, j < count →
    left (leftSchedule.innerTime j) = right (rightSchedule.innerTime j)

/-- Completed-excursion count is invariant under an endpoint-preserving
finite replacement of arbitrary first-hit inner-to-outer words. -/
theorem completedExcursionCount_eq_of_endpointMatchedSplice
    {left right : WalkPath} {outer inner : Set Point}
    [DecidablePred (· ∈ outer)] [DecidablePred (· ∈ inner)]
    {leftHorizon rightHorizon count : ℕ}
    (splice : EndpointMatchedExcursionSplice left right outer inner
      leftHorizon rightHorizon count) :
    completedExcursionCount left outer inner leftHorizon =
      completedExcursionCount right outer inner rightHorizon := by
  rw [splice.leftSchedule.completedExcursionCount_eq,
    splice.rightSchedule.completedExcursionCount_eq]

/-- A low-level, horizon-changing congruence principle.  It is often easier
for a concrete splice proof to match the finite sets of completed clock
indices directly than to package full schedules. -/
theorem completedExcursionCount_eq_of_completedIndices_iff
    {left right : WalkPath} {outer inner : Set Point}
    [DecidablePred (· ∈ outer)] [DecidablePred (· ∈ inner)]
    {leftHorizon rightHorizon : ℕ}
    (hcompleted : ∀ j : ℕ,
      (j < leftHorizon + 1 ∧
        excursionFinish left outer inner leftHorizon j ≤ leftHorizon) ↔
      (j < rightHorizon + 1 ∧
        excursionFinish right outer inner rightHorizon j ≤ rightHorizon)) :
    completedExcursionCount left outer inner leftHorizon =
      completedExcursionCount right outer inner rightHorizon := by
  unfold completedExcursionCount
  apply congrArg Finset.card
  ext j
  simpa only [Finset.mem_filter, Finset.mem_range] using hcompleted j

/-! ## Excursion-profile corollaries -/

/-- Classical-instance-free wrapper for the finite finish clock at one HLOZ
profile coordinate. -/
noncomputable def profileExcursionFinish
    (s : WalkPath) (n horizon : ℕ) (x : Point)
    (k : Fin (n + 2)) (j : ℕ) : ℕ := by
  classical
  exact excursionFinish s
    (discBoundary x (scaleRadius n ((k : ℕ) - 1)))
    (discBoundary x (scaleRadius n (k : ℕ))) horizon j

/-- If corresponding annular clocks have endpoint-matched first-hit splice
descriptions at every nonzero level, the entire HLOZ excursion profile is
unchanged. -/
theorem excursionProfile_eq_of_endpointMatchedSplices
    {left right : WalkPath} {n leftHorizon rightHorizon : ℕ} {x : Point}
    (count : Fin (n + 2) → ℕ)
    (splices : ∀ k : Fin (n + 2), (k : ℕ) ≠ 0 →
      EndpointMatchedExcursionSplice left right
        (discBoundary x (scaleRadius n ((k : ℕ) - 1)))
        (discBoundary x (scaleRadius n (k : ℕ)))
        leftHorizon rightHorizon (count k)) :
    excursionProfile left n leftHorizon x =
      excursionProfile right n rightHorizon x := by
  classical
  funext k
  unfold excursionProfile
  split_ifs with hk
  · rfl
  · exact completedExcursionCount_eq_of_endpointMatchedSplice
      (splices k hk)

/-- Whole-profile version of
`completedExcursionCount_eq_of_completedIndices_iff`.  It is the concrete
adapter for a splice proof that establishes clock-index equivalence one
annular level at a time. -/
theorem excursionProfile_eq_of_completedIndices_iff
    {left right : WalkPath} {n leftHorizon rightHorizon : ℕ} {x : Point}
    (hcompleted : ∀ (k : Fin (n + 2)), (k : ℕ) ≠ 0 → ∀ j : ℕ,
      (j < leftHorizon + 1 ∧
        profileExcursionFinish left n leftHorizon x k j ≤ leftHorizon) ↔
      (j < rightHorizon + 1 ∧
        profileExcursionFinish right n rightHorizon x k j ≤ rightHorizon)) :
    excursionProfile left n leftHorizon x =
      excursionProfile right n rightHorizon x := by
  classical
  funext k
  unfold excursionProfile
  split_ifs with hk
  · rfl
  · apply completedExcursionCount_eq_of_completedIndices_iff
    intro j
    simpa only [profileExcursionFinish] using hcompleted k hk j

/-- Successful-point status depends on a path/horizon only through its
excursion profile (the candidate-box condition is path independent). -/
theorem successfulPoint_iff_of_excursionProfile_eq
    {left right : WalkPath} {n leftHorizon rightHorizon : ℕ}
    {profileDelta : ℝ} {x : Point}
    (hprofile : excursionProfile left n leftHorizon x =
      excursionProfile right n rightHorizon x) :
    SuccessfulPoint left n leftHorizon profileDelta x ↔
      SuccessfulPoint right n rightHorizon profileDelta x := by
  unfold SuccessfulPoint
  rw [hprofile]

/-- Terminal specialization of the splice-invariance theorem. -/
theorem terminalCompletedExcursionCount_eq_of_endpointMatchedSplice
    {left right : WalkPath} {n leftHorizon rightHorizon : ℕ} {x : Point}
    {count : ℕ}
    (splice : EndpointMatchedExcursionSplice left right
      (terminalOuterBoundary n x) (terminalInnerBoundary n x)
      leftHorizon rightHorizon count) :
    terminalCompletedExcursionCount left n leftHorizon x =
      terminalCompletedExcursionCount right n rightHorizon x := by
  classical
  exact completedExcursionCount_eq_of_endpointMatchedSplice splice

/-- The terminal coordinate of the HLOZ profile is invariant under the same
endpoint-preserving first-hit splice. -/
theorem excursionProfile_terminal_eq_of_endpointMatchedSplice
    {left right : WalkPath} {n leftHorizon rightHorizon : ℕ} {x : Point}
    {count : ℕ}
    (splice : EndpointMatchedExcursionSplice left right
      (terminalOuterBoundary n x) (terminalInnerBoundary n x)
      leftHorizon rightHorizon count) :
    excursionProfile left n leftHorizon x ⟨n + 1, by omega⟩ =
      excursionProfile right n rightHorizon x ⟨n + 1, by omega⟩ := by
  rw [excursionProfile_terminal_eq_completedExcursionCount,
    excursionProfile_terminal_eq_completedExcursionCount]
  exact terminalCompletedExcursionCount_eq_of_endpointMatchedSplice splice

end

end Erdos1165.TerminalClockSplice
