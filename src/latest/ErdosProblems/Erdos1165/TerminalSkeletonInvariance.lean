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

import ErdosProblems.Erdos1165.MarkedBridgeFactorization
import ErdosProblems.Erdos1165.TerminalGlobalExitSplice
import ErdosProblems.Erdos1165.TerminalSkeletonWords
import ErdosProblems.Erdos1165.TerminalVisitSpliceInvariance

/-!
# Invariance of compressed terminal skeletons under bridge insertion

The terminal skeleton deletes the first finitely many inner-to-outer pieces
and remembers every complementary increment together with the entrance and
exit endpoints.  This module supplies the inverse operation used by the
stopped-data disintegration: arbitrary finite first-hit bridge words are
inserted between the retained pieces.

The actual stopping horizon is the length of the assembled word.  In
particular it is not recorded in the compressed skeleton.  A validity
predicate records only that the skeleton occurred once on a stopped
successful path; the insertion invariance below shows that validity is
independent of all bridge interiors and durations.
-/

open Set
open scoped BigOperators

namespace Erdos1165.TerminalSkeletonInvariance

open ThickPoint Proposition13Measurability TerminalExcursionPathwise
open TerminalSkeletonWords MarkedBridgeFactorization
open TerminalGlobalExitSplice
open TerminalVisitSpliceInvariance

noncomputable section

@[simp] theorem requiredTerminalCount_one (profileDelta : ℝ) :
    AppendixLocalTime.requiredTerminalCount 1 profileDelta = 0 := by
  simp [AppendixLocalTime.requiredTerminalCount, terminalLower]

/-! ## Finite words and assembled prefixes -/

/-- A list viewed as a genuinely variable-length stopped word. -/
def stoppedWordOfList (v : List Direction) : StoppedWord :=
  ⟨v.length, fun j ↦ v.get j⟩

@[simp] theorem stoppedWordOfList_length (v : List Direction) :
    (stoppedWordOfList v).1 = v.length := rfl

@[simp] theorem stoppedWordOfList_toList (v : List Direction) :
    List.ofFn (stoppedWordOfList v).2 = v := by
  exact List.ofFn_get v

/-- The complete variable-length word reconstructed from one compressed code
and one word in every deleted coordinate. -/
def assembledTerminalWord {m : ℕ} (code : TerminalSkeletonCode m)
    (words : TerminalSegmentWords m) : StoppedWord :=
  stoppedWordOfList (reconstructTerminalPacket (code, words))

/-- Its intrinsic stopped horizon. -/
def assembledTerminalHorizon {m : ℕ} (code : TerminalSkeletonCode m)
    (words : TerminalSegmentWords m) : ℕ :=
  (assembledTerminalWord code words).1

/-- The canonical infinite extension of the assembled stopped prefix. -/
def assembledTerminalPath {m : ℕ} (code : TerminalSkeletonCode m)
    (words : TerminalSegmentWords m) : StepPath :=
  extendStoppedWord (assembledTerminalWord code words)

theorem assembledTerminalPath_eq_reconstructedTerminalStepPath
    {m : ℕ} (code : TerminalSkeletonCode m)
    (words : TerminalSegmentWords m) :
    assembledTerminalPath code words =
      reconstructedTerminalStepPath code.1.retainedPiece words := rfl

theorem assembledTerminalHorizon_eq_alternatingConcat_length
    {m : ℕ} (code : TerminalSkeletonCode m)
    (words : TerminalSegmentWords m) :
    assembledTerminalHorizon code words =
      (alternatingConcat m code.1.retainedPiece words).length := rfl

@[simp] theorem stepPrefix_assembledTerminalPath {m : ℕ}
    (code : TerminalSkeletonCode m) (words : TerminalSegmentWords m) :
    stepPrefix (assembledTerminalHorizon code words)
        (assembledTerminalPath code words) =
      (assembledTerminalWord code words).2 := by
  exact stepPrefix_extendStoppedWord _

@[simp] theorem incrementSlice_assembledTerminalPath {m : ℕ}
    (code : TerminalSkeletonCode m) (words : TerminalSegmentWords m) :
    incrementSlice (assembledTerminalPath code words) 0
      (assembledTerminalHorizon code words) =
      reconstructTerminalPacket (code, words) := by
  unfold incrementSlice
  simp only [Nat.sub_zero, Nat.zero_add]
  change List.ofFn
      (stepPrefix (assembledTerminalHorizon code words)
        (assembledTerminalPath code words)) = _
  rw [stepPrefix_assembledTerminalPath]
  exact stoppedWordOfList_toList _

/-- Any path in the exact reconstructed cylinder has the same trajectory as
the canonical extension through the assembled horizon. -/
theorem trajectory_eq_assembledTerminalPath_of_mem_stoppedWordCylinder
    {m : ℕ} {code : TerminalSkeletonCode m}
    {words : TerminalSegmentWords m} {omega : StepPath}
    (homega : omega ∈ stoppedWordCylinder (assembledTerminalWord code words))
    {q : ℕ} (hq : q ≤ assembledTerminalHorizon code words) :
    trajectory omega q = trajectory (assembledTerminalPath code words) q := by
  apply trajectory_congr_of_incrementPrefix _ hq
  intro k hk
  have hw := congrFun homega ⟨k, hk⟩
  have ha := congrFun (stepPrefix_assembledTerminalPath code words) ⟨k, hk⟩
  exact hw.trans ha.symm

/-- Prefix equality in functional form, for the extractor congruence lemmas. -/
theorem increment_eq_assembledTerminalPath_of_mem_stoppedWordCylinder
    {m : ℕ} {code : TerminalSkeletonCode m}
    {words : TerminalSegmentWords m} {omega : StepPath}
    (homega : omega ∈ stoppedWordCylinder (assembledTerminalWord code words)) :
    ∀ k < assembledTerminalHorizon code words,
      omega k = assembledTerminalPath code words k := by
  intro k hk
  have hw := congrFun homega ⟨k, hk⟩
  have ha := congrFun (stepPrefix_assembledTerminalPath code words) ⟨k, hk⟩
  exact hw.trans ha.symm

/-! The general extractor congruence in `TerminalSkeletonWords` uses one
extra increment because a total extractor may return sentinel times.  On a
well-formed stopped skeleton all selected clocks are at most the horizon, so
the exact stopped cylinder of length `horizon` is sufficient. -/

theorem extractedEntrance_congr_stoppedPrefix
    {scale horizon : ℕ} {x : Point} {omega omega' : StepPath}
    (hprefix : ∀ k < horizon, omega k = omega' k) (j : ℕ) :
    extractedEntrance (trajectory omega) scale horizon x j =
      extractedEntrance (trajectory omega') scale horizon x j := by
  classical
  have hst : ∀ k ≤ horizon, trajectory omega k = trajectory omega' k := by
    intro k hk
    exact trajectory_congr_of_incrementPrefix hprefix hk
  simpa [extractedEntrance] using excursionFinish_congr_prefix hst
    (terminalOuterBoundary scale x) (terminalInnerBoundary scale x) j

theorem extractedExit_congr_stoppedPrefix
    {scale horizon : ℕ} {x : Point} {omega omega' : StepPath}
    (hprefix : ∀ k < horizon, omega k = omega' k) (j : ℕ) :
    extractedExit (trajectory omega) scale horizon x j =
      extractedExit (trajectory omega') scale horizon x j := by
  classical
  have hst : ∀ k ≤ horizon, trajectory omega k = trajectory omega' k := by
    intro k hk
    exact trajectory_congr_of_incrementPrefix hprefix hk
  simpa [extractedExit, terminalSegmentExitTime] using
    excursionStart_congr_prefix hst (terminalOuterBoundary scale x)
      (terminalInnerBoundary scale x) (j + 1)

theorem extractedEntrancePoint_congr_stoppedPrefix
    {scale horizon : ℕ} {profileDelta : ℝ} {x : Point}
    {omega omega' : StepPath}
    (hprefix : ∀ k < horizon, omega k = omega' k)
    (hwell : (extractTimedTerminalSkeleton scale horizon profileDelta x omega).WellFormed)
    (j : Fin (AppendixLocalTime.requiredTerminalCount scale profileDelta)) :
    trajectory omega
        (extractedEntrance (trajectory omega) scale horizon x j) =
      trajectory omega'
        (extractedEntrance (trajectory omega') scale horizon x j) := by
  have htime := extractedEntrance_congr_stoppedPrefix
    (scale := scale) (x := x) hprefix (j : ℕ)
  calc
    trajectory omega
        (extractedEntrance (trajectory omega) scale horizon x j) =
      trajectory omega'
        (extractedEntrance (trajectory omega) scale horizon x j) :=
      trajectory_congr_of_incrementPrefix hprefix
        ((hwell.1 j).1.trans (hwell.1 j).2)
    _ = trajectory omega'
        (extractedEntrance (trajectory omega') scale horizon x j) := by rw [htime]

theorem extractedExitPoint_congr_stoppedPrefix
    {scale horizon : ℕ} {profileDelta : ℝ} {x : Point}
    {omega omega' : StepPath}
    (hprefix : ∀ k < horizon, omega k = omega' k)
    (hwell : (extractTimedTerminalSkeleton scale horizon profileDelta x omega).WellFormed)
    (j : Fin (AppendixLocalTime.requiredTerminalCount scale profileDelta)) :
    trajectory omega (extractedExit (trajectory omega) scale horizon x j) =
      trajectory omega'
        (extractedExit (trajectory omega') scale horizon x j) := by
  have htime := extractedExit_congr_stoppedPrefix
    (scale := scale) (x := x) hprefix (j : ℕ)
  calc
    trajectory omega (extractedExit (trajectory omega) scale horizon x j) =
      trajectory omega'
        (extractedExit (trajectory omega) scale horizon x j) :=
      trajectory_congr_of_incrementPrefix hprefix (hwell.1 j).2
    _ = trajectory omega'
        (extractedExit (trajectory omega') scale horizon x j) := by rw [htime]

theorem extractTimedTerminalSkeleton_congr_stoppedPrefix
    {scale horizon : ℕ} {profileDelta : ℝ} {x : Point}
    {omega omega' : StepPath}
    (hprefix : ∀ k < horizon, omega k = omega' k)
    (hwell : (extractTimedTerminalSkeleton scale horizon profileDelta x omega).WellFormed) :
    extractTimedTerminalSkeleton scale horizon profileDelta x omega =
      extractTimedTerminalSkeleton scale horizon profileDelta x omega' := by
  classical
  apply TimedTerminalSkeleton.ext
  · rfl
  · funext j
    simpa [extractTimedTerminalSkeleton] using
      extractedEntrance_congr_stoppedPrefix hprefix (j : ℕ)
  · funext j
    simpa [extractTimedTerminalSkeleton] using
      extractedExit_congr_stoppedPrefix hprefix (j : ℕ)
  · funext j
    simpa [extractTimedTerminalSkeleton] using
      extractedEntrancePoint_congr_stoppedPrefix hprefix hwell j
  · funext j
    simpa [extractTimedTerminalSkeleton] using
      extractedExitPoint_congr_stoppedPrefix hprefix hwell j

theorem extractTerminalSkeletonCode_congr_stoppedPrefix
    {scale horizon : ℕ} {profileDelta : ℝ} {x : Point}
    {omega omega' : StepPath}
    (hprefix : ∀ k < horizon, omega k = omega' k)
    (hwell : (extractTimedTerminalSkeleton scale horizon profileDelta x omega).WellFormed) :
    extractTerminalSkeletonCode scale horizon profileDelta x omega =
      extractTerminalSkeletonCode scale horizon profileDelta x omega' := by
  classical
  let tw := extractTimedTerminalSkeleton scale horizon profileDelta x omega
  let tw' := extractTimedTerminalSkeleton scale horizon profileDelta x omega'
  have htw : tw = tw' :=
    extractTimedTerminalSkeleton_congr_stoppedPrefix hprefix hwell
  have hwell' : tw'.WellFormed := htw ▸ hwell
  unfold extractTerminalSkeletonCode compressTimedSkeleton
  change (TerminalSkeletonData.mk
      (complementaryPieces _ omega 0 horizon tw.entrance tw.exit),
      (tw.entrancePoint, tw.exitPoint)) =
    (TerminalSkeletonData.mk
      (complementaryPieces _ omega' 0 horizon tw'.entrance tw'.exit),
      (tw'.entrancePoint, tw'.exitPoint))
  rw [htw]
  apply Prod.ext
  · apply TerminalSkeletonData.ext
    exact complementaryPieces_congr _ tw'.entrance tw'.exit hprefix le_rfl
      (fun j ↦ (hwell'.1 j).1.trans (hwell'.1 j).2)
  · rfl

theorem terminalVisitVector_congr_stoppedPrefix
    {scale horizon : ℕ} {profileDelta : ℝ} {x : Point}
    {omega omega' : StepPath}
    (hprefix : ∀ k < horizon, omega k = omega' k)
    (hwell : (extractTimedTerminalSkeleton scale horizon profileDelta x omega).WellFormed) :
    terminalVisitVector (trajectory omega) scale horizon profileDelta x =
      terminalVisitVector (trajectory omega') scale horizon profileDelta x := by
  classical
  have htraj : ∀ k ≤ horizon, trajectory omega k = trajectory omega' k := by
    intro k hk
    exact trajectory_congr_of_incrementPrefix hprefix hk
  funext j
  unfold terminalVisitVector terminalExcursionVisits innerVisitCount innerVisitTimes
  have hfinish := excursionFinish_congr_prefix htraj
    (terminalOuterBoundary scale x) (terminalInnerBoundary scale x) j
  have hstart := excursionStart_congr_prefix htraj
    (terminalOuterBoundary scale x) (terminalInnerBoundary scale x) (j + 1)
  rw [hfinish, hstart]
  apply congrArg Finset.card
  apply Finset.filter_congr
  intro k hk
  have hklt := (Finset.mem_Ico.mp hk).2
  have hexitEq := extractedExit_congr_stoppedPrefix
    (scale := scale) (x := x) hprefix (j : ℕ)
  have hstartBound : excursionStart (trajectory omega')
      (terminalOuterBoundary scale x) (terminalInnerBoundary scale x)
      horizon ((j : ℕ) + 1) ≤ horizon := by
    have hbound : extractedExit (trajectory omega') scale horizon x j ≤ horizon := by
      rw [← hexitEq]
      exact (hwell.1 j).2
    simpa [extractedExit, terminalSegmentExitTime] using hbound
  rw [htraj k (hklt.le.trans hstartBound)]

theorem extractMarkedTerminalCode_congr_stoppedPrefix
    {scale horizon : ℕ} {profileDelta : ℝ} {x : Point}
    {omega omega' : StepPath}
    (hprefix : ∀ k < horizon, omega k = omega' k)
    (hwell : (extractTimedTerminalSkeleton scale horizon profileDelta x omega).WellFormed) :
    extractMarkedTerminalCode scale horizon profileDelta x omega =
      extractMarkedTerminalCode scale horizon profileDelta x omega' := by
  have hcode := extractTerminalSkeletonCode_congr_stoppedPrefix hprefix hwell
  have hvisits := terminalVisitVector_congr_stoppedPrefix hprefix hwell
  unfold extractMarkedTerminalCode
  rw [hcode, hvisits]

theorem wordWalk_reconstruct_eq_trajectory_assembledTerminalPath_of_le
    {m : ℕ} (code : TerminalSkeletonCode m)
    (words : TerminalSegmentWords m) {q : ℕ}
    (hq : q ≤ assembledTerminalHorizon code words) :
    wordWalk (0, 0) (reconstructTerminalPacket (code, words)) q =
      trajectory (assembledTerminalPath code words) q := by
  unfold wordWalk
  have h := wordPosition_incrementSlice (assembledTerminalPath code words)
    (Nat.zero_le _) hq
  have hs := incrementSlice_assembledTerminalPath code words
  change incrementSlice (assembledTerminalPath code words) 0
      (reconstructTerminalPacket (code, words)).length =
    reconstructTerminalPacket (code, words) at hs
  rw [hs] at h
  simpa using h

theorem isOuterExitTime_assembledTerminalPath_of_wordWalk
    {m scale : ℕ} {code : TerminalSkeletonCode m}
    {words : TerminalSegmentWords m}
    (h : IsOuterExitTime
      (wordWalk (0, 0) (reconstructTerminalPacket (code, words))) scale
      (assembledTerminalHorizon code words)) :
    IsOuterExitTime (trajectory (assembledTerminalPath code words)) scale
      (assembledTerminalHorizon code words) := by
  constructor
  · rw [← wordWalk_reconstruct_eq_trajectory_assembledTerminalPath_of_le
      code words le_rfl]
    exact h.1
  · intro q hq
    rw [← wordWalk_reconstruct_eq_trajectory_assembledTerminalPath_of_le
      code words hq.le]
    exact h.2 q hq

/-! ## Literal canonical bridge families -/

/-- Unmarked finite first-hit bridge words for the endpoints recorded by a
compressed terminal skeleton. -/
abbrev UnmarkedTerminalBridgeCode {m : ℕ} (scale : ℕ) (x : Point)
    (code : TerminalSkeletonCode m) (j : Fin m) :=
  BoundaryExitWordCode (terminalOuterBoundary scale x)
    (code.2.1 j) (code.2.2 j)

/-- Marked bridge words with prescribed target-visit count. -/
abbrev MarkedTerminalBridgeCode {m : ℕ} (scale : ℕ) (x : Point)
    (code : TerminalSkeletonCode m) (visits : Fin m → ℕ) (j : Fin m) :=
  BoundaryVisitExitWordCode (terminalOuterBoundary scale x) x
    (code.2.1 j) (visits j) (code.2.2 j)

/-- Erase the proof fields of an unmarked bridge family to its inserted
direction words. -/
def unmarkedBridgeWords {m : ℕ} {scale : ℕ} {x : Point}
    {code : TerminalSkeletonCode m}
    (bridges : (j : Fin m) → UnmarkedTerminalBridgeCode scale x code j) :
    TerminalSegmentWords m :=
  fun j ↦ List.ofFn (bridges j).1.2

/-- Erase a marked bridge family to its inserted direction words. -/
def markedBridgeWords {m : ℕ} {scale : ℕ} {x : Point}
    {code : TerminalSkeletonCode m} {visits : Fin m → ℕ}
    (bridges : (j : Fin m) →
      MarkedTerminalBridgeCode scale x code visits j) :
    TerminalSegmentWords m :=
  fun j ↦ List.ofFn (bridges j).1.2

/-- Forget only the visit-count certificate of a marked bridge. -/
def eraseMarkedTerminalBridge {m : ℕ} {scale : ℕ} {x : Point}
    {code : TerminalSkeletonCode m} {visits : Fin m → ℕ} {j : Fin m}
    (bridge : MarkedTerminalBridgeCode scale x code visits j) :
    UnmarkedTerminalBridgeCode scale x code j :=
  ⟨bridge.1, bridge.2.1, bridge.2.2.2⟩

/-- Coordinatewise erasure of a marked terminal bridge tuple. -/
def eraseMarkedTerminalBridges {m : ℕ} {scale : ℕ} {x : Point}
    {code : TerminalSkeletonCode m} {visits : Fin m → ℕ}
    (bridges : (j : Fin m) →
      MarkedTerminalBridgeCode scale x code visits j) :
    (j : Fin m) → UnmarkedTerminalBridgeCode scale x code j :=
  fun j ↦ eraseMarkedTerminalBridge (bridges j)

@[simp] theorem unmarkedBridgeWords_eraseMarkedTerminalBridges
    {m : ℕ} {scale : ℕ} {x : Point}
    {code : TerminalSkeletonCode m} {visits : Fin m → ℕ}
    (bridges : (j : Fin m) →
      MarkedTerminalBridgeCode scale x code visits j) :
    unmarkedBridgeWords (eraseMarkedTerminalBridges bridges) =
      markedBridgeWords bridges := rfl

/-- The total stopped word consisting of an arbitrary deterministic
pre-start prefix followed by the inserted terminal packet. -/
def assembleAfterPrefix {start m : ℕ} (pre : Fin start → Direction)
    (code : TerminalSkeletonCode m) (words : TerminalSegmentWords m) :
    StoppedWord :=
  stoppedWordOfList (List.ofFn pre ++ reconstructTerminalPacket (code, words))

/-- Erase all bridge coordinates, retaining only the complete complementary
skeleton. -/
def emptyTerminalWords (m : ℕ) : TerminalSegmentWords m := fun _ ↦ []

def retainedTerminalWord {start m : ℕ} (pre : Fin start → Direction)
    (code : TerminalSkeletonCode m) : StoppedWord :=
  assembleAfterPrefix pre code (emptyTerminalWords m)

/-- Removing the arbitrary fixed-length pre-prefix from a complete assembled
cylinder exposes exactly the reconstructed terminal-tail cylinder. -/
theorem shiftSteps_mem_assembledTerminalWordCylinder_of_mem_assembleAfterPrefix
    {start m : ℕ} {pre : Fin start → Direction}
    {code : TerminalSkeletonCode m} {words : TerminalSegmentWords m}
    {omega : StepPath}
    (homega : omega ∈ stoppedWordCylinder
      (assembleAfterPrefix pre code words)) :
    shiftSteps start omega ∈
      stoppedWordCylinder (assembledTerminalWord code words) := by
  let tail := reconstructTerminalPacket (code, words)
  let full := List.ofFn pre ++ tail
  change stepPrefix tail.length (shiftSteps start omega) =
    (stoppedWordOfList tail).2
  funext q
  have hqfull : start + (q : ℕ) < full.length := by
    simp only [full, List.length_append, List.length_ofFn]
    omega
  have hprefix := congrFun homega ⟨start + q, by
    simpa only [assembleAfterPrefix, stoppedWordOfList_length,
      List.length_append, List.length_ofFn, full, tail] using hqfull⟩
  change omega (start + q) = full.get ⟨start + q, hqfull⟩ at hprefix
  change omega (start + q) = tail.get q
  rw [hprefix, List.get_eq_getElem, List.get_eq_getElem]
  simp [full]

/-- The concrete unmarked alternating insertion word. -/
def assembleUnmarkedTerminalBridges {start m scale : ℕ} {x : Point}
    (code : TerminalSkeletonCode m)
    (c : (Fin start → Direction) ×
      ((j : Fin m) → UnmarkedTerminalBridgeCode scale x code j)) :
    StoppedWord :=
  assembleAfterPrefix c.1 code (unmarkedBridgeWords c.2)

/-- The concrete fixed-visit alternating insertion word. -/
def assembleMarkedTerminalBridges {start m scale : ℕ} {x : Point}
    (code : TerminalSkeletonCode m) (visits : Fin m → ℕ)
    (c : (Fin start → Direction) ×
      ((j : Fin m) → MarkedTerminalBridgeCode scale x code visits j)) :
    StoppedWord :=
  assembleAfterPrefix c.1 code (markedBridgeWords c.2)

/-- Literal unmarked insertion union for a fixed compressed skeleton. -/
def unmarkedTerminalInsertionEvent {start m scale : ℕ} {x : Point}
    (code : TerminalSkeletonCode m) : Set StepPath :=
  stoppedWordEvent
    (assembleUnmarkedTerminalBridges (start := start) (scale := scale)
      (x := x) code)

/-- Literal fixed-visit insertion union for a fixed compressed skeleton. -/
def markedTerminalInsertionEvent {start m scale : ℕ} {x : Point}
    (code : TerminalSkeletonCode m) (visits : Fin m → ℕ) : Set StepPath :=
  stoppedWordEvent
    (assembleMarkedTerminalBridges (start := start) (scale := scale)
      (x := x) code visits)

@[simp] theorem assembleAfterPrefix_length {start m : ℕ}
    (pre : Fin start → Direction) (code : TerminalSkeletonCode m)
    (words : TerminalSegmentWords m) :
    (assembleAfterPrefix pre code words).1 =
      start + (assembledTerminalWord code words).1 := by
  simp [assembleAfterPrefix, assembledTerminalWord]

/-- The retained length is independent of all inserted bridge durations. -/
def retainedTerminalLength {m : ℕ} (code : TerminalSkeletonCode m) : ℕ :=
  ∑ j, (code.1.retainedPiece j).length

theorem alternatingConcat_length : ∀ (m : ℕ)
    (pieces : Fin (m + 1) → List Direction)
    (words : TerminalSegmentWords m),
    (alternatingConcat m pieces words).length =
      (∑ j, (pieces j).length) + ∑ j, (words j).length := by
  intro m
  induction m with
  | zero =>
      intro pieces words
      simp [alternatingConcat]
  | succ m ih =>
      intro pieces words
      simp only [alternatingConcat, List.length_append]
      rw [ih]
      have hp : (∑ j, (pieces j).length) =
          (pieces 0).length + ∑ j : Fin (m + 1), (pieces j.succ).length :=
        Fin.sum_univ_succ _
      have hw : (∑ j, (words j).length) =
          (words 0).length + ∑ j : Fin m, (words j.succ).length :=
        Fin.sum_univ_succ _
      rw [hp, hw]
      omega

theorem assembledTerminalWord_length {m : ℕ}
    (code : TerminalSkeletonCode m) (words : TerminalSegmentWords m) :
    (assembledTerminalWord code words).1 =
      retainedTerminalLength code + ∑ j, (words j).length := by
  exact alternatingConcat_length m code.1.retainedPiece words

theorem assembleAfterPrefix_length_eq {start m : ℕ}
    (pre : Fin start → Direction) (code : TerminalSkeletonCode m)
    (words : TerminalSegmentWords m) :
    (assembleAfterPrefix pre code words).1 =
      (start + retainedTerminalLength code) + ∑ j, (words j).length := by
  rw [assembleAfterPrefix_length, assembledTerminalWord_length]
  omega

@[simp] theorem retainedTerminalWord_length {start m : ℕ}
    (pre : Fin start → Direction) (code : TerminalSkeletonCode m) :
    (retainedTerminalWord pre code).1 = start + retainedTerminalLength code := by
  rw [retainedTerminalWord, assembleAfterPrefix_length_eq]
  simp [emptyTerminalWords]

theorem assembleUnmarkedTerminalBridges_length {start m scale : ℕ}
    {x : Point} (code : TerminalSkeletonCode m)
    (c : (Fin start → Direction) ×
      ((j : Fin m) → UnmarkedTerminalBridgeCode scale x code j)) :
    (assembleUnmarkedTerminalBridges code c).1 =
      (retainedTerminalWord c.1 code).1 + ∑ j, (c.2 j).1.1 := by
  rw [assembleUnmarkedTerminalBridges, assembleAfterPrefix_length_eq,
    retainedTerminalWord_length]
  simp only [unmarkedBridgeWords, List.length_ofFn]

theorem assembleMarkedTerminalBridges_length {start m scale : ℕ}
    {x : Point} (code : TerminalSkeletonCode m) (visits : Fin m → ℕ)
    (c : (Fin start → Direction) ×
      ((j : Fin m) → MarkedTerminalBridgeCode scale x code visits j)) :
    (assembleMarkedTerminalBridges code visits c).1 =
      (retainedTerminalWord c.1 code).1 + ∑ j, (c.2 j).1.1 := by
  rw [assembleMarkedTerminalBridges, assembleAfterPrefix_length_eq,
    retainedTerminalWord_length]
  simp only [markedBridgeWords, List.length_ofFn]

/-! ## Skeleton validity -/

/-- A compressed skeleton is valid when it is extracted from at least one
literal stopped successful path.  The existential witness is used only to
establish the insertion invariant; neither its horizon nor its deleted
bridge interiors are part of the skeleton code. -/
def ValidTerminalSkeleton (scale : ℕ) (profileDelta : ℝ) (x : Point)
    (code : TerminalSkeletonCode
      (AppendixLocalTime.requiredTerminalCount scale profileDelta)) : Prop :=
  ∃ horizon : ℕ, ∃ omega : StepPath,
    IsOuterExitTime (trajectory omega) scale horizon ∧
    SuccessfulPoint (trajectory omega) scale horizon profileDelta x ∧
    extractTerminalSkeletonCode scale horizon profileDelta x omega = code

theorem validTerminalSkeleton_candidate
    {scale : ℕ} {profileDelta : ℝ} {x : Point}
    {code : TerminalSkeletonCode
      (AppendixLocalTime.requiredTerminalCount scale profileDelta)}
    (hvalid : ValidTerminalSkeleton scale profileDelta x code) :
    x ∈ candidateBox scale := by
  obtain ⟨_horizon, _omega, _hexit, hx, _hcode⟩ := hvalid
  exact hx.1

/-- Valid compressed codes carry terminal-inner-boundary entrance marks. -/
theorem validTerminalSkeleton_entrance_mem
    {scale : ℕ} {profileDelta : ℝ} {x : Point}
    {code : TerminalSkeletonCode
      (AppendixLocalTime.requiredTerminalCount scale profileDelta)}
    (hscale : 1 ≤ scale)
    (hvalid : ValidTerminalSkeleton scale profileDelta x code)
    (j : Fin (AppendixLocalTime.requiredTerminalCount scale profileDelta)) :
    code.2.1 j ∈ terminalInnerBoundary scale x := by
  obtain ⟨horizon, omega, hexit, hx, hcode⟩ := hvalid
  rw [← hcode]
  exact extractTerminalSkeletonCode_entrance_mem hscale hexit hx j

/-- Valid compressed codes carry terminal-outer-boundary exit marks. -/
theorem validTerminalSkeleton_exit_mem
    {scale : ℕ} {profileDelta : ℝ} {x : Point}
    {code : TerminalSkeletonCode
      (AppendixLocalTime.requiredTerminalCount scale profileDelta)}
    (hscale : 1 ≤ scale)
    (hvalid : ValidTerminalSkeleton scale profileDelta x code)
    (j : Fin (AppendixLocalTime.requiredTerminalCount scale profileDelta)) :
    code.2.2 j ∈ terminalOuterBoundary scale x := by
  obtain ⟨horizon, omega, hexit, hx, hcode⟩ := hvalid
  rw [← hcode]
  exact extractTerminalSkeletonCode_exit_mem hscale hexit hx j

/-- Boundary-subtype version of a valid compressed code. -/
def supportedValidTerminalSkeletonCode
    {scale : ℕ} {profileDelta : ℝ} {x : Point}
    (code : TerminalSkeletonCode
      (AppendixLocalTime.requiredTerminalCount scale profileDelta))
    (hscale : 1 ≤ scale)
    (hvalid : ValidTerminalSkeleton scale profileDelta x code) :
    MarkedSkeletonPartition.SkeletonIndex
      (TerminalSkeletonData
        (AppendixLocalTime.requiredTerminalCount scale profileDelta))
      (TerminalEntrance scale x) (TerminalExit scale x)
      (AppendixLocalTime.requiredTerminalCount scale profileDelta) :=
  liftTerminalSkeletonCode code
    (validTerminalSkeleton_entrance_mem hscale hvalid)
    (validTerminalSkeleton_exit_mem hscale hvalid)

/-! ## Transfer from the canonical extension to its exact stopped cylinder -/

theorem stoppedSuccessfulAndCode_of_mem_assembledTerminalWordCylinder
    {scale : ℕ} {profileDelta : ℝ} {x : Point}
    {code : TerminalSkeletonCode
      (AppendixLocalTime.requiredTerminalCount scale profileDelta)}
    {words : TerminalSegmentWords
      (AppendixLocalTime.requiredTerminalCount scale profileDelta)}
    (hscale : 1 ≤ scale)
    (hexit : IsOuterExitTime
      (trajectory (assembledTerminalPath code words)) scale
      (assembledTerminalHorizon code words))
    (hsuccess : SuccessfulPoint
      (trajectory (assembledTerminalPath code words)) scale
      (assembledTerminalHorizon code words) profileDelta x)
    (hcode : extractTerminalSkeletonCode scale
      (assembledTerminalHorizon code words) profileDelta x
      (assembledTerminalPath code words) = code)
    {omega : StepPath}
    (homega : omega ∈ stoppedWordCylinder (assembledTerminalWord code words)) :
    IsOuterExitTime (trajectory omega) scale
        (assembledTerminalHorizon code words) ∧
      SuccessfulPoint (trajectory omega) scale
        (assembledTerminalHorizon code words) profileDelta x ∧
      extractTerminalSkeletonCode scale
        (assembledTerminalHorizon code words) profileDelta x omega = code := by
  let H := assembledTerminalHorizon code words
  have hinc : ∀ k < H, assembledTerminalPath code words k = omega k := by
    intro k hk
    exact (increment_eq_assembledTerminalPath_of_mem_stoppedWordCylinder
      homega k hk).symm
  have htraj : ∀ k ≤ H,
      trajectory (assembledTerminalPath code words) k = trajectory omega k := by
    intro k hk
    exact trajectory_congr_of_incrementPrefix hinc hk
  have hwell : (extractTimedTerminalSkeleton scale H profileDelta x
      (assembledTerminalPath code words)).WellFormed :=
    extractTimedTerminalSkeleton_wellFormed_of_stopped_success
      hscale hexit hsuccess
  refine ⟨(isOuterExitTime_congr_prefix htraj).mp hexit,
    (successfulPoint_congr_prefix htraj profileDelta x).mp hsuccess, ?_⟩
  have hcongr := extractTerminalSkeletonCode_congr_stoppedPrefix hinc hwell
  exact hcongr.symm.trans hcode

theorem stoppedSuccessfulAndMarkedCode_of_mem_assembledTerminalWordCylinder
    {scale : ℕ} {profileDelta : ℝ} {x : Point}
    {code : TerminalSkeletonCode
      (AppendixLocalTime.requiredTerminalCount scale profileDelta)}
    {words : TerminalSegmentWords
      (AppendixLocalTime.requiredTerminalCount scale profileDelta)}
    {visits : Fin
      (AppendixLocalTime.requiredTerminalCount scale profileDelta) → ℕ}
    (hscale : 1 ≤ scale)
    (hexit : IsOuterExitTime
      (trajectory (assembledTerminalPath code words)) scale
      (assembledTerminalHorizon code words))
    (hsuccess : SuccessfulPoint
      (trajectory (assembledTerminalPath code words)) scale
      (assembledTerminalHorizon code words) profileDelta x)
    (hmarked : extractMarkedTerminalCode scale
      (assembledTerminalHorizon code words) profileDelta x
      (assembledTerminalPath code words) =
        (code.1, (code.2.1, (code.2.2, visits))))
    {omega : StepPath}
    (homega : omega ∈ stoppedWordCylinder (assembledTerminalWord code words)) :
    IsOuterExitTime (trajectory omega) scale
        (assembledTerminalHorizon code words) ∧
      SuccessfulPoint (trajectory omega) scale
        (assembledTerminalHorizon code words) profileDelta x ∧
      extractMarkedTerminalCode scale
        (assembledTerminalHorizon code words) profileDelta x omega =
          (code.1, (code.2.1, (code.2.2, visits))) := by
  let H := assembledTerminalHorizon code words
  have hinc : ∀ k < H, assembledTerminalPath code words k = omega k := by
    intro k hk
    exact (increment_eq_assembledTerminalPath_of_mem_stoppedWordCylinder
      homega k hk).symm
  have htraj : ∀ k ≤ H,
      trajectory (assembledTerminalPath code words) k = trajectory omega k := by
    intro k hk
    exact trajectory_congr_of_incrementPrefix hinc hk
  have hwell : (extractTimedTerminalSkeleton scale H profileDelta x
      (assembledTerminalPath code words)).WellFormed :=
    extractTimedTerminalSkeleton_wellFormed_of_stopped_success
      hscale hexit hsuccess
  refine ⟨(isOuterExitTime_congr_prefix htraj).mp hexit,
    (successfulPoint_congr_prefix htraj profileDelta x).mp hsuccess, ?_⟩
  have hcongr := extractMarkedTerminalCode_congr_stoppedPrefix hinc hwell
  exact hcongr.symm.trans hmarked

/-! ## The first global exit after canonical insertion -/

/-- The endpoint component of a canonical first-hit word does not require
unfolding the (potentially large) terminal skeleton that supplies its
endpoints. -/
theorem unmarkedTerminalBridge_wordEndpoint
    {scale : ℕ} {x a endpoint : Point}
    (bridge : BoundaryExitWordCode
      (terminalOuterBoundary scale x) a endpoint) :
    wordEndpoint a (List.ofFn bridge.1.2) = endpoint := by
  calc
    wordEndpoint a (List.ofFn bridge.1.2) =
        wordEndpoint a
          (List.ofFn (stepPrefix bridge.1.1
            (extendStoppedWord bridge.1))) := by
      rw [stepPrefix_extendStoppedWord]
    _ = PlanarPotential.trajectoryFrom a (extendStoppedWord bridge.1)
        bridge.1.1 := wordEndpoint_ofFn_stepPrefix _ _ _
    _ = endpoint := bridge.2.2

/-- A canonical terminal bridge started on the terminal inner boundary stays
inside the terminal outer disc until its recorded exit endpoint. -/
theorem unmarkedTerminalBridge_wordWithin
    {scale : ℕ} {x a endpoint : Point} (hscale : 1 ≤ scale)
    (ha : a ∈ terminalInnerBoundary scale x)
    (bridge : BoundaryExitWordCode
      (terminalOuterBoundary scale x) a endpoint) :
    WordWithin (disc x (scaleRadius scale scale)) a
      (List.ofFn bridge.1.2) :=
  (terminalBoundaryExitWordCode_wordWithin_and_endpoint_of_innerDisc
    hscale ha.1 bridge).1

/-- Finite-list form of the first-global-exit insertion invariant for the
literal skeleton extracted from a stopped successful path. -/
theorem isOuterExitTime_wordWalk_reconstruct_unmarked_of_stopped_success
    {scale horizon : ℕ} {profileDelta : ℝ} {x : Point}
    {omega : StepPath}
    (hscale : 1 ≤ scale)
    (hexit : IsOuterExitTime (trajectory omega) scale horizon)
    (hx : SuccessfulPoint (trajectory omega) scale horizon profileDelta x)
    (bridges : (j : Fin
      (AppendixLocalTime.requiredTerminalCount scale profileDelta)) →
        UnmarkedTerminalBridgeCode scale x
          (extractTerminalSkeletonCode scale horizon profileDelta x omega) j) :
    IsOuterExitTime
      (wordWalk (0, 0)
        (reconstructTerminalPacket
          (extractTerminalSkeletonCode scale horizon profileDelta x omega,
            unmarkedBridgeWords bridges))) scale
      (reconstructTerminalPacket
        (extractTerminalSkeletonCode scale horizon profileDelta x omega,
          unmarkedBridgeWords bridges)).length := by
  rw [reconstructTerminalPacket_extractTerminalSkeletonCode]
  exact isOuterExitTime_alternatingConcat_canonical_of_stopped_success
    hscale hexit hx bridges

theorem isOuterExitTime_assembled_unmarked_of_stopped_success
    {scale horizon : ℕ} {profileDelta : ℝ} {x : Point}
    {omega : StepPath}
    (hscale : 1 ≤ scale)
    (hexit : IsOuterExitTime (trajectory omega) scale horizon)
    (hx : SuccessfulPoint (trajectory omega) scale horizon profileDelta x)
    (bridges : (j : Fin
      (AppendixLocalTime.requiredTerminalCount scale profileDelta)) →
        UnmarkedTerminalBridgeCode scale x
          (extractTerminalSkeletonCode scale horizon profileDelta x omega) j) :
    IsOuterExitTime
      (trajectory (assembledTerminalPath
        (extractTerminalSkeletonCode scale horizon profileDelta x omega)
        (unmarkedBridgeWords bridges)))
      scale (assembledTerminalHorizon
        (extractTerminalSkeletonCode scale horizon profileDelta x omega)
        (unmarkedBridgeWords bridges)) := by
  apply isOuterExitTime_assembledTerminalPath_of_wordWalk
  exact isOuterExitTime_wordWalk_reconstruct_unmarked_of_stopped_success
    hscale hexit hx bridges

theorem isOuterExitTime_assembled_unmarked_of_valid
    {scale : ℕ} {profileDelta : ℝ} {x : Point}
    {code : TerminalSkeletonCode
      (AppendixLocalTime.requiredTerminalCount scale profileDelta)}
    (hscale : 1 ≤ scale)
    (hvalid : ValidTerminalSkeleton scale profileDelta x code)
    (bridges : (j : Fin
      (AppendixLocalTime.requiredTerminalCount scale profileDelta)) →
        UnmarkedTerminalBridgeCode scale x code j) :
    IsOuterExitTime
      (trajectory (assembledTerminalPath code (unmarkedBridgeWords bridges)))
      scale (assembledTerminalHorizon code (unmarkedBridgeWords bridges)) := by
  obtain ⟨horizon, omega, hexit, hx, hcode⟩ := hvalid
  subst code
  exact isOuterExitTime_assembled_unmarked_of_stopped_success
    hscale hexit hx bridges

/-- The global-exit invariant is unchanged by carrying fixed visit-count
certificates on the inserted bridge words. -/
theorem isOuterExitTime_assembled_marked_of_valid
    {scale : ℕ} {profileDelta : ℝ} {x : Point}
    {code : TerminalSkeletonCode
      (AppendixLocalTime.requiredTerminalCount scale profileDelta)}
    (hscale : 1 ≤ scale)
    (hvalid : ValidTerminalSkeleton scale profileDelta x code)
    (visits : Fin
      (AppendixLocalTime.requiredTerminalCount scale profileDelta) → ℕ)
    (bridges : (j : Fin
      (AppendixLocalTime.requiredTerminalCount scale profileDelta)) →
        MarkedTerminalBridgeCode scale x code visits j) :
    IsOuterExitTime
      (trajectory (assembledTerminalPath code (markedBridgeWords bridges)))
      scale (assembledTerminalHorizon code (markedBridgeWords bridges)) := by
  simpa only [unmarkedBridgeWords_eraseMarkedTerminalBridges] using
    isOuterExitTime_assembled_unmarked_of_valid hscale hvalid
      (eraseMarkedTerminalBridges bridges)

/-! ## Exact re-extraction after canonical insertion -/

theorem extractTerminalSkeletonCode_retainedPiece
    (scale horizon : ℕ) (profileDelta : ℝ) (x : Point) (omega : StepPath) :
    (extractTerminalSkeletonCode scale horizon profileDelta x omega).1.retainedPiece =
      complementaryPieces
        (AppendixLocalTime.requiredTerminalCount scale profileDelta)
        omega 0 horizon
        (extractTimedTerminalSkeleton scale horizon profileDelta x omega).entrance
        (extractTimedTerminalSkeleton scale horizon profileDelta x omega).exit := rfl

end

end Erdos1165.TerminalSkeletonInvariance
