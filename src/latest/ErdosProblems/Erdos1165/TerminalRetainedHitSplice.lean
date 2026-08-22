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

import ErdosProblems.Erdos1165.TerminalClockSplice
import ErdosProblems.Erdos1165.TerminalGlobalExitSplice
import ErdosProblems.Erdos1165.TerminalRetainedPieceOffsets

/-!
# First hits carried by the retained terminal-skeleton pieces

Replacing the deleted inner-to-outer words does not change any of the
outer-to-inner pieces left in a compressed terminal skeleton.  Absolute
times after a replacement word do change, however.  This file packages the
small affine reindexing argument which transports first-hit certificates
from the original path to the reconstructed path.

`RetainedPieceTrajectoryTranslation` is the word-level input: the first
retained piece agrees with the original prefix, and each later retained
piece agrees with the corresponding original interval after translating its
left endpoint to the end of the preceding replacement word.  No assumption
is made on replacement-word lengths or interiors.
-/

open Set

namespace Erdos1165.TerminalRetainedHitSplice

open TerminalExcursionPathwise TerminalSkeletonWords
open TerminalVisitSpliceInvariance TerminalClockSplice
open TerminalRetainedPieceOffsets TerminalGlobalExitSplice
open MarkedBridgeFactorization TerminalSequentialVisitLaw
open ThickPoint

noncomputable section

/-! ## Exact retained pieces of a timed skeleton -/

@[simp] theorem complementaryPieces_zero_of_pos
    {m : ℕ} (hm : 0 < m) (omega : StepPath) (base horizon : ℕ)
    (entrance exit : Fin m → ℕ) :
    complementaryPieces m omega base horizon entrance exit (0 : Fin (m + 1)) =
      incrementSlice omega base (entrance ⟨0, hm⟩) := by
  cases m with
  | zero => omega
  | succ m => exact complementaryPieces_zero omega base horizon entrance exit

/-- The retained piece after deleted coordinate `j` is literally the
original increment interval from `exit j` to the next entrance. -/
theorem complementaryPieces_succ : ∀ {m : ℕ} (omega : StepPath)
    (base horizon : ℕ) (entrance exit : Fin m → ℕ)
    (j : Fin m) (hj : (j : ℕ) + 1 < m),
    complementaryPieces m omega base horizon entrance exit j.succ =
      incrementSlice omega (exit j) (entrance ⟨(j : ℕ) + 1, hj⟩) := by
  intro m
  induction m with
  | zero =>
      intro omega base horizon entrance exit j
      exact Fin.elim0 j
  | succ m ih =>
      cases m with
      | zero =>
          intro omega base horizon entrance exit j hj
          omega
      | succ n =>
          intro omega base horizon entrance exit j hj
          let jj : Fin (n + 1) := ⟨(j : ℕ), by omega⟩
          have hcast : jj.castSucc = j := Fin.ext rfl
          have hsucc : jj.succ = ⟨(j : ℕ) + 1, hj⟩ := Fin.ext rfl
          simpa only [hcast, hsucc] using
            complementaryPieces_between n omega base horizon entrance exit jj

/-- Following an original increment slice through its full finite extension
recovers the original trajectory at every time in the slice. -/
theorem trajectoryFrom_extendStoppedWord_incrementSlice
    (omega : StepPath) {start stop q : ℕ}
    (hstart : start ≤ stop) (hq : q ≤ stop - start) :
    PlanarPotential.trajectoryFrom (trajectory omega start)
        (extendStoppedWord
          (stoppedWordOfList (incrementSlice omega start stop))) q =
      trajectory omega (start + q) := by
  rw [← wordPosition_ofFn_stepPrefix _ _ hq]
  have hlength : stop - start =
      (stoppedWordOfList (incrementSlice omega start stop)).1 := by
    simp [stoppedWordOfList]
  rw [hlength]
  rw [stepPrefix_extendStoppedWord]
  simpa [stoppedWordOfList] using
    wordPosition_incrementSlice omega hstart hq

/-! ## Affine transport of one first hit -/

/-- Transport a first-hit certificate across an order-preserving translation
of a finite time interval.  This is the only arithmetic fact needed for all
retained pieces. -/
theorem isFirstHitSegment_of_intervalTranslation
    {s s' : WalkPath} {A : Set Point}
    {start stop horizon start' stop' horizon' : ℕ}
    (hfirst : IsFirstHitSegment s A start stop horizon)
    (hstop' : stop' = start' + (stop - start))
    (hstopHorizon : stop' ≤ horizon')
    (htrajectory : ∀ q, start ≤ q → q ≤ stop →
      s' (start' + (q - start)) = s q) :
    IsFirstHitSegment s' A start' stop' horizon' := by
  have hstartStop : start ≤ stop := hfirst.1
  have hstart'Stop' : start' ≤ stop' := by omega
  refine ⟨hstart'Stop', hstopHorizon, ?_, ?_⟩
  · rw [hstop', htrajectory stop hstartStop le_rfl]
    simpa using hfirst.2.2.1
  · intro q hstart'q hqstop' hqA
    let q' := start + (q - start')
    have hstartq' : start ≤ q' := by omega
    have hq'stop : q' < stop := by
      dsimp [q']
      omega
    apply hfirst.2.2.2 q' hstartq' hq'stop
    have hindex : start' + (q' - start) = q := by
      dsimp [q']
      omega
    rw [← htrajectory q' hstartq' hq'stop.le, hindex]
    exact hqA

/-! ## Translation data for complementary pieces -/

/-- Exact trajectory translation furnished by the retained pieces of a timed
terminal skeleton.  The initial piece starts at absolute time zero.  The
piece following deleted coordinate `j` starts immediately after replacement
word `j` and represents the original interval from `t.exit j` through the
next entrance.

The explicit endpoint equations are kept alongside the pointwise equations
because they let downstream clock proofs avoid unfolding the recursive
definition of `replacementWordStart`. -/
structure RetainedPieceTrajectoryTranslation
    {m : ℕ} (omega : StepPath) (t : TimedTerminalSkeleton m)
    (words : TerminalSegmentWords m) where
  initialStop : ∀ hm : 0 < m,
    replacementWordStart m
        (complementaryPieces m omega 0 t.horizon t.entrance t.exit)
        words ⟨0, hm⟩ = t.entrance ⟨0, hm⟩
  initialTrajectory : ∀ (hm : 0 < m) q, q ≤ t.entrance ⟨0, hm⟩ →
    trajectory (reconstructedTerminalStepPath
        (complementaryPieces m omega 0 t.horizon t.entrance t.exit) words) q =
      trajectory omega q
  gapStop : ∀ (j : Fin m) (hj : (j : ℕ) + 1 < m),
    replacementWordStart m
        (complementaryPieces m omega 0 t.horizon t.entrance t.exit)
        words ⟨(j : ℕ) + 1, hj⟩ =
      replacementWordStop
          (complementaryPieces m omega 0 t.horizon t.entrance t.exit)
          words j +
        (t.entrance ⟨(j : ℕ) + 1, hj⟩ - t.exit j)
  gapTrajectory : ∀ (j : Fin m) (hj : (j : ℕ) + 1 < m) q,
    t.exit j ≤ q → q ≤ t.entrance ⟨(j : ℕ) + 1, hj⟩ →
      trajectory (reconstructedTerminalStepPath
          (complementaryPieces m omega 0 t.horizon t.entrance t.exit) words)
          (replacementWordStop
              (complementaryPieces m omega 0 t.horizon t.entrance t.exit)
              words j + (q - t.exit j)) =
        trajectory omega q

/-- The pointwise translation data are forced by the literal complementary
pieces once the endpoint of each replacement word is aligned with the
recorded original exit point.  Thus the only geometric input not contained
in the finite-word construction is the endpoint matching itself. -/
theorem retainedPieceTrajectoryTranslation_of_endpointAlignment
    {m : ℕ} (hm : 0 < m) (omega : StepPath)
    (t : TimedTerminalSkeleton m) (words : TerminalSegmentWords m)
    (hendpoint : ∀ j : Fin m,
      trajectory (reconstructedTerminalStepPath
          (complementaryPieces m omega 0 t.horizon t.entrance t.exit) words)
          (replacementWordStop
            (complementaryPieces m omega 0 t.horizon t.entrance t.exit)
            words j) = trajectory omega (t.exit j)) :
    RetainedPieceTrajectoryTranslation omega t words := by
  let pieces := complementaryPieces m omega 0 t.horizon t.entrance t.exit
  let newOmega := reconstructedTerminalStepPath pieces words
  refine
    { initialStop := ?_
      initialTrajectory := ?_
      gapStop := ?_
      gapTrajectory := ?_ }
  · intro hm'
    cases m with
    | zero => omega
    | succ k =>
        simp [replacementWordStart, complementaryPieces,
          incrementSlice_length]
  · intro hm' q hq
    have hpiece : pieces (0 : Fin (m + 1)) =
        incrementSlice omega 0 (t.entrance ⟨0, hm'⟩) := by
      simpa [pieces] using complementaryPieces_zero_of_pos hm' omega 0
        t.horizon t.entrance t.exit
    have hqPiece : q ≤ (pieces (0 : Fin (m + 1))).length := by
      rw [hpiece, incrementSlice_length]
      simpa using hq
    have hwalk := trajectory_reconstructed_along_retainedPiece
      pieces words (0 : Fin (m + 1)) hqPiece
    rw [retainedPieceStart_zero] at hwalk
    rw [hpiece] at hwalk
    calc
      trajectory newOmega q =
          PlanarPotential.trajectoryFrom (trajectory newOmega 0)
            (extendStoppedWord
              (stoppedWordOfList
                (incrementSlice omega 0 (t.entrance ⟨0, hm'⟩)))) q := by
          simpa [newOmega] using hwalk
      _ = PlanarPotential.trajectoryFrom (trajectory omega 0)
            (extendStoppedWord
              (stoppedWordOfList
                (incrementSlice omega 0 (t.entrance ⟨0, hm'⟩)))) q := by simp
      _ = trajectory omega (0 + q) :=
        trajectoryFrom_extendStoppedWord_incrementSlice omega
          (Nat.zero_le _) (by simpa using hq)
      _ = trajectory omega q := by simp
  · intro j hj
    let next : Fin m := ⟨(j : ℕ) + 1, hj⟩
    have hindex : next.castSucc = j.succ := by
      apply Fin.ext
      rfl
    calc
      replacementWordStart m pieces words next =
          retainedPieceStop pieces words next.castSucc :=
        (retainedPieceStop_castSucc_eq_replacementWordStart
          pieces words next).symm
      _ = retainedPieceStop pieces words j.succ := by rw [hindex]
      _ = retainedPieceStart m pieces words j.succ +
          (pieces j.succ).length := rfl
      _ = replacementWordStop pieces words j +
          (pieces j.succ).length := by
        rw [retainedPieceStart_succ_eq_replacementWordStop]
      _ = replacementWordStop pieces words j +
          (t.entrance next - t.exit j) := by
        rw [show pieces j.succ =
            incrementSlice omega (t.exit j) (t.entrance next) by
          simpa [pieces, next] using complementaryPieces_succ omega 0
            t.horizon t.entrance t.exit j hj]
        simp only [incrementSlice_length]
  · intro j hj q hqexit hqentrance
    let next : Fin m := ⟨(j : ℕ) + 1, hj⟩
    let r := q - t.exit j
    have hpiece : pieces j.succ =
        incrementSlice omega (t.exit j) (t.entrance next) := by
      simpa [pieces, next] using complementaryPieces_succ omega 0
        t.horizon t.entrance t.exit j hj
    have hr : r ≤ (pieces j.succ).length := by
      rw [hpiece, incrementSlice_length]
      dsimp [r]
      exact Nat.sub_le_sub_right hqentrance (t.exit j)
    have hr' : r ≤ t.entrance next - t.exit j := by
      rw [← incrementSlice_length omega (t.exit j) (t.entrance next), ← hpiece]
      exact hr
    have hwalk := trajectory_reconstructed_along_retainedPiece
      pieces words j.succ hr
    have hstart : retainedPieceStart m pieces words j.succ =
        replacementWordStop pieces words j :=
      retainedPieceStart_succ_eq_replacementWordStop pieces words j
    rw [hstart, hpiece] at hwalk
    calc
      trajectory newOmega
          (replacementWordStop pieces words j + (q - t.exit j)) =
          PlanarPotential.trajectoryFrom
            (trajectory newOmega (replacementWordStop pieces words j))
            (extendStoppedWord (stoppedWordOfList
              (incrementSlice omega (t.exit j) (t.entrance next)))) r := by
        simpa [newOmega, r] using hwalk
      _ = PlanarPotential.trajectoryFrom (trajectory omega (t.exit j))
            (extendStoppedWord (stoppedWordOfList
              (incrementSlice omega (t.exit j) (t.entrance next)))) r := by
        rw [show trajectory newOmega (replacementWordStop pieces words j) =
            trajectory omega (t.exit j) by
          simpa [newOmega, pieces] using hendpoint j]
      _ = trajectory omega (t.exit j + r) :=
        trajectoryFrom_extendStoppedWord_incrementSlice omega
          (by exact hqexit.trans hqentrance) hr'
      _ = trajectory omega q := by
        congr 1
        dsimp [r]
        omega

/-! ## The three retained first-hit inputs to the clock theorem -/

/-- The clock-visible first-hit data contributed by the retained pieces.
The first two fields concern the initial retained prefix and the last field
concerns every retained gap between consecutive replacement words. -/
structure RetainedFirstHitInputs
    {m : ℕ} (omega : StepPath) (t : TimedTerminalSkeleton m)
    (words : TerminalSegmentWords m) (outer inner : Set Point) where
  initialOuterTime : ℕ
  firstOuter : IsFirstHitSegment
    (trajectory (reconstructedTerminalStepPath
      (complementaryPieces m omega 0 t.horizon t.entrance t.exit) words))
    outer 0 initialOuterTime
    (alternatingConcat m
      (complementaryPieces m omega 0 t.horizon t.entrance t.exit) words).length
  firstInnerZero : ∀ hm : 0 < m, IsFirstHitSegment
    (trajectory (reconstructedTerminalStepPath
      (complementaryPieces m omega 0 t.horizon t.entrance t.exit) words))
    inner initialOuterTime
    (replacementWordStart m
      (complementaryPieces m omega 0 t.horizon t.entrance t.exit)
      words ⟨0, hm⟩)
    (alternatingConcat m
      (complementaryPieces m omega 0 t.horizon t.entrance t.exit) words).length
  firstInnerSucc : ∀ (j : Fin m) (hj : (j : ℕ) + 1 < m),
    IsFirstHitSegment
      (trajectory (reconstructedTerminalStepPath
        (complementaryPieces m omega 0 t.horizon t.entrance t.exit) words))
      inner
      (replacementWordStop
        (complementaryPieces m omega 0 t.horizon t.entrance t.exit) words j)
      (replacementWordStart m
        (complementaryPieces m omega 0 t.horizon t.entrance t.exit)
        words ⟨(j : ℕ) + 1, hj⟩)
      (alternatingConcat m
        (complementaryPieces m omega 0 t.horizon t.entrance t.exit) words).length

/-- Transport the original retained-piece first hits to arbitrary replacement
words.  Together with admissibility of the replacement words, the returned
fields are exactly the three hypotheses of
`terminalClocks_reconstructed_eq_replacementOffsets`.

The original first-hit certificates may have the old stopped horizon
`t.horizon`; only their restriction through the relevant entrance time is
used. -/
noncomputable def retainedFirstHitInputsOfTranslation
    {m : ℕ} (hm : 0 < m) (omega : StepPath)
    (t : TimedTerminalSkeleton m) (words : TerminalSegmentWords m)
    (outer inner : Set Point) (initialOuterTime : ℕ)
    (hfirstOuter : IsFirstHitSegment (trajectory omega) outer
      0 initialOuterTime t.horizon)
    (hfirstInnerZero : IsFirstHitSegment (trajectory omega) inner
      initialOuterTime (t.entrance ⟨0, hm⟩) t.horizon)
    (hfirstInnerSucc : ∀ (j : Fin m) (hj : (j : ℕ) + 1 < m),
      IsFirstHitSegment (trajectory omega) inner (t.exit j)
        (t.entrance ⟨(j : ℕ) + 1, hj⟩) t.horizon)
    (htranslation : RetainedPieceTrajectoryTranslation omega t words) :
    RetainedFirstHitInputs omega t words outer inner := by
  let pieces := complementaryPieces m omega 0 t.horizon t.entrance t.exit
  let newPath := trajectory (reconstructedTerminalStepPath pieces words)
  let newHorizon := (alternatingConcat m pieces words).length
  have hentranceLe : t.entrance ⟨0, hm⟩ ≤ newHorizon := by
    rw [← htranslation.initialStop hm]
    exact replacementWordStart_le_alternatingConcat_length m pieces words ⟨0, hm⟩
  have houterStop : initialOuterTime ≤ newHorizon :=
    hfirstInnerZero.1.trans hentranceLe
  refine
    { initialOuterTime := initialOuterTime
      firstOuter := ?_
      firstInnerZero := ?_
      firstInnerSucc := ?_ }
  · apply isFirstHitSegment_of_intervalTranslation hfirstOuter (by simp) houterStop
    intro q _hq0 hqstop
    simpa [pieces, newPath] using
      htranslation.initialTrajectory hm q
        (hqstop.trans hfirstInnerZero.1)
  · intro hm'
    have hmEq : (⟨0, hm'⟩ : Fin m) = ⟨0, hm⟩ := Fin.ext (by simp)
    rw [hmEq]
    have hinitialLe : initialOuterTime ≤ t.entrance ⟨0, hm⟩ :=
      hfirstInnerZero.1
    have hinitialStop : replacementWordStart m pieces words ⟨0, hm⟩ =
        t.entrance ⟨0, hm⟩ := by
      simpa [pieces] using htranslation.initialStop hm
    have hstop : replacementWordStart m pieces words ⟨0, hm⟩ =
        initialOuterTime + (t.entrance ⟨0, hm⟩ - initialOuterTime) := by
      rw [hinitialStop]
      omega
    have hnewStopLe : replacementWordStart m pieces words ⟨0, hm⟩ ≤
        (alternatingConcat m pieces words).length := by
      simpa [hinitialStop] using hentranceLe
    apply isFirstHitSegment_of_intervalTranslation hfirstInnerZero
      hstop (by simpa [pieces] using hnewStopLe)
    intro q hqstart hqentrance
    rw [Nat.add_sub_of_le hqstart]
    simpa [pieces, newPath] using
      htranslation.initialTrajectory hm q hqentrance
  · intro j hj
    let next : Fin m := ⟨(j : ℕ) + 1, hj⟩
    have hnextLe : replacementWordStart m pieces words next ≤ newHorizon :=
      replacementWordStart_le_alternatingConcat_length m pieces words next
    apply isFirstHitSegment_of_intervalTranslation
      (hfirstInnerSucc j hj) (htranslation.gapStop j hj) hnextLe
    intro q hqexit hqentrance
    simpa [pieces, newPath, next] using
      htranslation.gapTrajectory j hj q hqexit hqentrance

/-- Concrete call-site wrapper: endpoint matching alone turns the literal
complementary pieces into the required translation, after which the original
first-hit certificates transport to the reconstructed clock inputs. -/
noncomputable def retainedFirstHitInputsOfEndpointAlignment
    {m : ℕ} (hm : 0 < m) (omega : StepPath)
    (t : TimedTerminalSkeleton m) (words : TerminalSegmentWords m)
    (outer inner : Set Point) (initialOuterTime : ℕ)
    (hfirstOuter : IsFirstHitSegment (trajectory omega) outer
      0 initialOuterTime t.horizon)
    (hfirstInnerZero : IsFirstHitSegment (trajectory omega) inner
      initialOuterTime (t.entrance ⟨0, hm⟩) t.horizon)
    (hfirstInnerSucc : ∀ (j : Fin m) (hj : (j : ℕ) + 1 < m),
      IsFirstHitSegment (trajectory omega) inner (t.exit j)
        (t.entrance ⟨(j : ℕ) + 1, hj⟩) t.horizon)
    (hendpoint : ∀ j : Fin m,
      trajectory (reconstructedTerminalStepPath
          (complementaryPieces m omega 0 t.horizon t.entrance t.exit) words)
          (replacementWordStop
            (complementaryPieces m omega 0 t.horizon t.entrance t.exit)
            words j) = trajectory omega (t.exit j)) :
    RetainedFirstHitInputs omega t words outer inner :=
  retainedFirstHitInputsOfTranslation hm omega t words outer inner
    initialOuterTime hfirstOuter hfirstInnerZero hfirstInnerSucc
    (retainedPieceTrajectoryTranslation_of_endpointAlignment
      hm omega t words hendpoint)

/-! ## Literal extracted-skeleton specialization -/

/-- For a timed skeleton extracted from a stopped successful path, all source
first-hit certificates are the defining terminal excursion clocks.  Hence
endpoint matching of the replacement words is the sole remaining input for
the retained half of splice invariance. -/
noncomputable def retainedFirstHitInputsOfExtractedTimedSkeleton
    {scale horizon : ℕ} {profileDelta : ℝ} {x : Point}
    {omega : StepPath}
    (hscale : 1 ≤ scale)
    (hexit : IsOuterExitTime (trajectory omega) scale horizon)
    (hx : SuccessfulPoint (trajectory omega) scale horizon profileDelta x)
    (hm : 0 < AppendixLocalTime.requiredTerminalCount scale profileDelta)
    (words : TerminalSegmentWords
      (AppendixLocalTime.requiredTerminalCount scale profileDelta))
    (hendpoint : ∀ j : Fin
        (AppendixLocalTime.requiredTerminalCount scale profileDelta),
      trajectory (reconstructedTerminalStepPath
          (complementaryPieces
            (AppendixLocalTime.requiredTerminalCount scale profileDelta)
            omega 0 horizon
            (extractTimedTerminalSkeleton scale horizon profileDelta x omega).entrance
            (extractTimedTerminalSkeleton scale horizon profileDelta x omega).exit)
          words)
          (replacementWordStop
            (complementaryPieces
              (AppendixLocalTime.requiredTerminalCount scale profileDelta)
              omega 0 horizon
              (extractTimedTerminalSkeleton scale horizon profileDelta x omega).entrance
              (extractTimedTerminalSkeleton scale horizon profileDelta x omega).exit)
            words j) =
        trajectory omega
          ((extractTimedTerminalSkeleton scale horizon profileDelta x omega).exit j)) :
    RetainedFirstHitInputs omega
      (extractTimedTerminalSkeleton scale horizon profileDelta x omega) words
      (terminalOuterBoundary scale x) (terminalInnerBoundary scale x) := by
  classical
  let m := AppendixLocalTime.requiredTerminalCount scale profileDelta
  let t := extractTimedTerminalSkeleton scale horizon profileDelta x omega
  let s := trajectory omega
  let outer := terminalOuterBoundary scale x
  let inner := terminalInnerBoundary scale x
  let initialOuterTime := excursionStart s outer inner horizon 0
  have ht : t.WellFormed := by
    exact extractTimedTerminalSkeleton_wellFormed_of_stopped_success
      hscale hexit hx
  have hentranceZeroLe : t.entrance ⟨0, hm⟩ ≤ horizon :=
    (ht.1 ⟨0, hm⟩).1.trans (ht.1 ⟨0, hm⟩).2
  have hinitialLe : initialOuterTime ≤ horizon := by
    have hle : initialOuterTime ≤ t.entrance ⟨0, hm⟩ := by
      have hclock := excursionStart_le_finish s outer inner horizon 0
      simpa only [initialOuterTime, t, extractTimedTerminalSkeleton,
        extractedEntrance] using hclock
    exact hle.trans hentranceZeroLe
  have hfirstOuter : IsFirstHitSegment s outer
      0 initialOuterTime horizon := by
    have hcomplete : firstHitThrough s outer 0 horizon ≤ horizon := by
      simpa [initialOuterTime, excursionStart] using hinitialLe
    simpa [initialOuterTime, excursionStart] using
      isFirstHitSegment_firstHitThrough_of_le s outer 0 horizon hcomplete
  have hfirstInnerZero : IsFirstHitSegment s inner initialOuterTime
      (t.entrance ⟨0, hm⟩) horizon := by
    have hclock : t.entrance ⟨0, hm⟩ =
        firstHitThrough s inner initialOuterTime horizon := by
      simp only [t, extractTimedTerminalSkeleton, extractedEntrance,
        excursionFinish, initialOuterTime, s, outer, inner]
    have hcomplete : firstHitThrough s inner initialOuterTime horizon ≤
        horizon := by
      rw [← hclock]
      exact hentranceZeroLe
    have h := isFirstHitSegment_firstHitThrough_of_le s inner
      initialOuterTime horizon hcomplete
    rw [← hclock] at h
    exact h
  have hfirstInnerSucc : ∀ (j : Fin m) (hj : (j : ℕ) + 1 < m),
      IsFirstHitSegment s inner (t.exit j)
        (t.entrance ⟨(j : ℕ) + 1, hj⟩) horizon := by
    intro j hj
    let next : Fin m := ⟨(j : ℕ) + 1, hj⟩
    have hnextLe : t.entrance next ≤ horizon :=
      (ht.1 next).1.trans (ht.1 next).2
    have hstartClock : t.exit j =
        excursionStart s outer inner horizon ((j : ℕ) + 1) := by
      simp only [t, extractTimedTerminalSkeleton, extractedExit,
        terminalSegmentExitTime, s, outer, inner]
    have hstopClock : t.entrance next =
        firstHitThrough s inner (t.exit j) horizon := by
      rw [hstartClock]
      simp only [t, extractTimedTerminalSkeleton, extractedEntrance,
        excursionFinish, next, s, outer, inner]
    have hcomplete : firstHitThrough s inner (t.exit j) horizon ≤ horizon := by
      rw [← hstopClock]
      exact hnextLe
    have h := isFirstHitSegment_firstHitThrough_of_le s inner
      (t.exit j) horizon hcomplete
    rw [← hstopClock] at h
    exact h
  exact retainedFirstHitInputsOfEndpointAlignment hm omega t words outer inner
    initialOuterTime hfirstOuter hfirstInnerZero hfirstInnerSucc
    (by simpa [m, t, extractTimedTerminalSkeleton] using hendpoint)

end

end Erdos1165.TerminalRetainedHitSplice
