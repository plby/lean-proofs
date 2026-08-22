/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/
/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

import ErdosProblems.Erdos1165.SharedPrefixPairCoarsePartition

/-!
# Parsing stopped pair fibres into shared-prefix insertion atoms

This file proves the sound direction needed by an upper decomposition:
an actual separated successful pair path can be parsed by deleting its two
chronologically merged terminal interval families and then reinserting the
literal deleted words.  This is finite-word reconstruction only; it does not
assert that arbitrary replacement words preserve either successful profile.
-/

open Set

namespace Erdos1165.SharedPrefixPairEventParsing

open AppendixPair Hitting MarkedBridgeFactorization
open SharedPrefixPairCoarsePartition SharedPrefixPairExtraction
open SharedPrefixPairExtractedAtom SharedPrefixPairExtractedMarkedAtom
open SharedPrefixPairMergedSkeleton TerminalExcursionPathwise
open TerminalExtractedBridgeCodes TerminalSkeletonFactorization
open TerminalSkeletonInvariance TerminalSkeletonWords ThickPoint

noncomputable section

/-- The literal deleted word at a left logical coordinate. -/
def extractedLogicalPairLeftBoundaryExitWordCode
    {scale horizon : ℕ} {profileDelta : ℝ} {x y : Point}
    {omega : StepPath}
    (hscale : 1 ≤ scale)
    (hexit : IsOuterExitTime (trajectory omega) scale horizon)
    (hx : SuccessfulPoint (trajectory omega) scale horizon profileDelta x)
    (i : Fin (terminalCount scale profileDelta)) :
    ExtractedLogicalPairTerminalBridge
      scale horizon profileDelta x y omega
        (Fin.castAdd (terminalCount scale profileDelta) i) := by
  refine ⟨extractedTerminalStoppedWord
    scale horizon profileDelta x omega i, ?_, ?_⟩
  · simpa only [ExtractedLogicalPairTerminalBridge, LogicalPairTerminalBridge,
      pairEntrancePoint, logicalPairCenter, pairValue_castAdd,
      extractTimedTerminalSkeleton] using
        extractedTerminalStoppedWord_absoluteBoundaryFirstAt
          hscale hexit hx i
  · simpa only [ExtractedLogicalPairTerminalBridge, LogicalPairTerminalBridge,
      pairEntrancePoint, pairExitPoint, logicalPairCenter, pairValue_castAdd,
      extractTimedTerminalSkeleton] using
        extractedTerminalStoppedWord_endpoint hscale hexit hx i

/-- The literal deleted word at a right logical coordinate. -/
def extractedLogicalPairRightBoundaryExitWordCode
    {scale horizon : ℕ} {profileDelta : ℝ} {x y : Point}
    {omega : StepPath}
    (hscale : 1 ≤ scale)
    (hexit : IsOuterExitTime (trajectory omega) scale horizon)
    (hy : SuccessfulPoint (trajectory omega) scale horizon profileDelta y)
    (j : Fin (terminalCount scale profileDelta)) :
      ExtractedLogicalPairTerminalBridge scale horizon profileDelta x y omega
        (Fin.natAdd (terminalCount scale profileDelta) j) := by
  refine ⟨extractedTerminalStoppedWord
    scale horizon profileDelta y omega j, ?_, ?_⟩
  · simpa only [ExtractedLogicalPairTerminalBridge, LogicalPairTerminalBridge,
      pairEntrancePoint, logicalPairCenter, pairValue_natAdd,
      extractTimedTerminalSkeleton] using
        extractedTerminalStoppedWord_absoluteBoundaryFirstAt
          hscale hexit hy j
  · simpa only [ExtractedLogicalPairTerminalBridge, LogicalPairTerminalBridge,
      pairEntrancePoint, pairExitPoint, logicalPairCenter, pairValue_natAdd,
      extractTimedTerminalSkeleton] using
        extractedTerminalStoppedWord_endpoint hscale hexit hy j

@[simp] theorem extractedLogicalPairLeftBoundaryExitWordCode_word
    {scale horizon : ℕ} {profileDelta : ℝ} {x y : Point}
    {omega : StepPath}
    (hscale : 1 ≤ scale)
    (hexit : IsOuterExitTime (trajectory omega) scale horizon)
    (hx : SuccessfulPoint (trajectory omega) scale horizon profileDelta x)
    (i : Fin (terminalCount scale profileDelta)) :
    (extractedLogicalPairLeftBoundaryExitWordCode
      (y := y) hscale hexit hx i).1 =
      extractedTerminalStoppedWord scale horizon profileDelta x omega i := rfl

@[simp] theorem extractedLogicalPairRightBoundaryExitWordCode_word
    {scale horizon : ℕ} {profileDelta : ℝ} {x y : Point}
    {omega : StepPath}
    (hscale : 1 ≤ scale)
    (hexit : IsOuterExitTime (trajectory omega) scale horizon)
    (hy : SuccessfulPoint (trajectory omega) scale horizon profileDelta y)
    (j : Fin (terminalCount scale profileDelta)) :
    (extractedLogicalPairRightBoundaryExitWordCode
      (x := x) hscale hexit hy j).1 =
      extractedTerminalStoppedWord scale horizon profileDelta y omega j := rfl

/-- The literal deleted word at a logical left/right coordinate, packaged
with the first-hit and endpoint certificates expected by the pair atom. -/
def extractedLogicalPairBoundaryExitWordCode
    {scale horizon : ℕ} {profileDelta : ℝ} {x y : Point}
    {omega : StepPath}
    (hscale : 1 ≤ scale)
    (hexit : IsOuterExitTime (trajectory omega) scale horizon)
    (hx : SuccessfulPoint (trajectory omega) scale horizon profileDelta x)
    (hy : SuccessfulPoint (trajectory omega) scale horizon profileDelta y) :
    (q : Fin (terminalCount scale profileDelta +
      terminalCount scale profileDelta)) →
    ExtractedLogicalPairTerminalBridge
      scale horizon profileDelta x y omega q :=
  Fin.addCases
    (extractedLogicalPairLeftBoundaryExitWordCode hscale hexit hx)
    (extractedLogicalPairRightBoundaryExitWordCode hscale hexit hy)

@[simp] theorem extractedLogicalPairBoundaryExitWordCode_castAdd_erased
    {scale horizon : ℕ} {profileDelta : ℝ} {x y : Point}
    {omega : StepPath}
    (hscale : 1 ≤ scale)
    (hexit : IsOuterExitTime (trajectory omega) scale horizon)
    (hx : SuccessfulPoint (trajectory omega) scale horizon profileDelta x)
    (hy : SuccessfulPoint (trajectory omega) scale horizon profileDelta y)
    (i : Fin (terminalCount scale profileDelta)) :
    List.ofFn (extractedLogicalPairBoundaryExitWordCode hscale hexit hx hy
      (Fin.castAdd (terminalCount scale profileDelta) i)).1.2 =
      intervalWords omega
        (extractTimedTerminalSkeleton scale horizon profileDelta x omega).entrance
        (extractTimedTerminalSkeleton scale horizon profileDelta x omega).exit i := by
  rw [extractedLogicalPairBoundaryExitWordCode, Fin.addCases_left,
    extractedLogicalPairLeftBoundaryExitWordCode_word]
  exact extractedTerminalStoppedWord_erased
    scale horizon profileDelta x omega i

@[simp] theorem extractedLogicalPairBoundaryExitWordCode_natAdd_erased
    {scale horizon : ℕ} {profileDelta : ℝ} {x y : Point}
    {omega : StepPath}
    (hscale : 1 ≤ scale)
    (hexit : IsOuterExitTime (trajectory omega) scale horizon)
    (hx : SuccessfulPoint (trajectory omega) scale horizon profileDelta x)
    (hy : SuccessfulPoint (trajectory omega) scale horizon profileDelta y)
    (j : Fin (terminalCount scale profileDelta)) :
    List.ofFn (extractedLogicalPairBoundaryExitWordCode hscale hexit hx hy
      (Fin.natAdd (terminalCount scale profileDelta) j)).1.2 =
      intervalWords omega
        (extractTimedTerminalSkeleton scale horizon profileDelta y omega).entrance
        (extractTimedTerminalSkeleton scale horizon profileDelta y omega).exit j := by
  rw [extractedLogicalPairBoundaryExitWordCode, Fin.addCases_right,
    extractedLogicalPairRightBoundaryExitWordCode_word]
  exact extractedTerminalStoppedWord_erased
    scale horizon profileDelta y omega j

/-- Erasing the logical certificates gives precisely the two actual interval
word families, still in logical left-then-right order. -/
theorem extractedLogicalPairBoundaryExitWordCode_erased
    {scale horizon : ℕ} {profileDelta : ℝ} {x y : Point}
    {omega : StepPath}
    (hscale : 1 ≤ scale)
    (hexit : IsOuterExitTime (trajectory omega) scale horizon)
    (hx : SuccessfulPoint (trajectory omega) scale horizon profileDelta x)
    (hy : SuccessfulPoint (trajectory omega) scale horizon profileDelta y) :
    (fun q ↦ List.ofFn
      (extractedLogicalPairBoundaryExitWordCode hscale hexit hx hy q).1.2) =
      logicalIntervalWords omega
        (extractTimedTerminalSkeleton scale horizon profileDelta x omega)
        (extractTimedTerminalSkeleton scale horizon profileDelta y omega) := by
  funext q
  refine Fin.addCases (fun i ↦ ?_) (fun j ↦ ?_) q
  · simpa only [logicalIntervalWords, pairValue_castAdd] using
      extractedLogicalPairBoundaryExitWordCode_castAdd_erased
        hscale hexit hx hy i
  · simpa only [logicalIntervalWords, pairValue_natAdd] using
      extractedLogicalPairBoundaryExitWordCode_natAdd_erased
        hscale hexit hx hy j

/-- A separated successful pair path belongs to the insertion atom obtained
from its own merged complementary packet. -/
theorem mem_extractedLogicalPairComplementarySkeletonAtom_event
    {start scale horizon : ℕ} {profileDelta : ℝ} {x y : Point}
    {omega : StepPath}
    (hscale : 1 ≤ scale)
    (hlevel : separationLevel scale x y ≤ scale)
    (hexit : IsOuterExitTime (trajectory (shiftSteps start omega)) scale horizon)
    (hx : SuccessfulPoint (trajectory (shiftSteps start omega))
      scale horizon profileDelta x)
    (hy : SuccessfulPoint (trajectory (shiftSteps start omega))
      scale horizon profileDelta y)
    (hxbox : x ∈ candidateBox scale) (hybox : y ∈ candidateBox scale) :
    omega ∈ (coarsePairUnmarkedInsertionAtom
      (omega := omega) hscale hlevel hexit hx hy hxbox hybox).event := by
  let sigma := shiftSteps start omega
  let left := extractTimedTerminalSkeleton scale horizon profileDelta x sigma
  let right := extractTimedTerminalSkeleton scale horizon profileDelta y sigma
  let bridges : (q : Fin (terminalCount scale profileDelta +
      terminalCount scale profileDelta)) →
      ExtractedLogicalPairTerminalBridge
        scale horizon profileDelta x y sigma q :=
    fun q ↦ extractedLogicalPairBoundaryExitWordCode hscale hexit hx hy q
  have hwords : (fun q ↦ List.ofFn (bridges q).1.2) =
      logicalIntervalWords sigma left right := by
    exact extractedLogicalPairBoundaryExitWordCode_erased hscale hexit hx hy
  unfold ComplementarySkeletonAtom.event stoppedWordEvent
  apply Set.mem_iUnion.mpr
  refine ⟨(stepPrefix start omega, bridges), ?_⟩
  change omega ∈ stoppedWordCylinder
    (assembleAfterPrefix (stepPrefix start omega)
      (compressTimedSkeleton sigma (mergeTimedTerminalSkeleton left right))
      (chronologicalPairBridgeWords bridges))
  rw [chronologicalPairBridgeWords, hwords,
    chronologicalValues_logicalIntervalWords]
  exact mem_stoppedWordCylinder_assembleAfterPrefix_packetOfTimedSkeleton
    omega (mergeTimedTerminalSkeleton left right)
      (extractMergedTimedTerminalSkeleton_wellFormed
        hscale hlevel hexit hx hy)

/-! ## An insertion event indexed only by the coarse code -/

/-- Logical left/right entrance endpoints stored by a coarse pair code. -/
def coarsePairLogicalEntrance
    {scale : ℕ} {profileDelta : ℝ}
    (code : CoarseSharedPairSkeletonCode scale profileDelta) :
    Fin (terminalCount scale profileDelta +
      terminalCount scale profileDelta) → Point :=
  pairValue code.2.1.1 code.2.2.1

/-- Logical left/right exit endpoints stored by a coarse pair code. -/
def coarsePairLogicalExit
    {scale : ℕ} {profileDelta : ℝ}
    (code : CoarseSharedPairSkeletonCode scale profileDelta) :
    Fin (terminalCount scale profileDelta +
      terminalCount scale profileDelta) → Point :=
  pairValue code.2.1.2 code.2.2.2

/-- Reconstruct the chronologically indexed compressed terminal skeleton
from the one-copy retained data, its stored permutation, and the two branch
endpoint vectors. -/
def coarsePairMergedSkeletonCode
    {scale : ℕ} {profileDelta : ℝ}
    (code : CoarseSharedPairSkeletonCode scale profileDelta) :
    TerminalSkeletonCode (terminalCount scale profileDelta +
      terminalCount scale profileDelta) :=
  (code.1.1,
    (fun k ↦ coarsePairLogicalEntrance code (code.1.2 k),
      fun k ↦ coarsePairLogicalExit code (code.1.2 k)))

/-- The canonical unmarked logical bridge family determined solely by the
coarse code. -/
abbrev CoarsePairBoundaryExitWordCode
    {scale : ℕ} {profileDelta : ℝ} (x y : Point)
    (code : CoarseSharedPairSkeletonCode scale profileDelta)
    (q : Fin (terminalCount scale profileDelta +
      terminalCount scale profileDelta)) :=
  BoundaryExitWordCode
    (terminalOuterBoundary scale (logicalPairCenter x y q))
    (coarsePairLogicalEntrance code q) (coarsePairLogicalExit code q)

/-- Assemble a coarse-code bridge tuple in the stored chronological order. -/
def assembleCoarsePairBoundaryExitWords
    {start scale : ℕ} {profileDelta : ℝ} {x y : Point}
    (code : CoarseSharedPairSkeletonCode scale profileDelta)
    (input : (Fin start → Direction) ×
      ((q : Fin (terminalCount scale profileDelta +
        terminalCount scale profileDelta)) →
        CoarsePairBoundaryExitWordCode x y code q)) : StoppedWord :=
  assembleAfterPrefix input.1 (coarsePairMergedSkeletonCode code)
    (fun k ↦ List.ofFn (input.2 (code.1.2 k)).1.2)

/-- The symmetric terminal insertion event normalized by a coarse code,
without choosing a representative stopped path. -/
def coarsePairBoundaryExitInsertionEvent
    (start scale : ℕ) (profileDelta : ℝ) (x y : Point)
    (code : CoarseSharedPairSkeletonCode scale profileDelta) : Set StepPath :=
  stoppedWordEvent
    (assembleCoarsePairBoundaryExitWords (start := start) (x := x) (y := y) code)

end

end Erdos1165.SharedPrefixPairEventParsing
