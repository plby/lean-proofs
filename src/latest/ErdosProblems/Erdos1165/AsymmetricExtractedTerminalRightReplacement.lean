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

import ErdosProblems.Erdos1165.AsymmetricSharedPrefixRightReplacement
import ErdosProblems.Erdos1165.SharedPrefixPairEventParsing
import ErdosProblems.Erdos1165.TerminalExtractedBridgeCodes
import ErdosProblems.Erdos1165.TerminalExtractedMarkedVisitSplice

/-!
# Extracted terminal atoms which replace only the right branch

Starting from one stopped successful pair, the merged terminal extractor
provides a prefix-free chronological atom.  We freeze every `x` bridge to
the word extracted from that source path and leave only the `y` bridge
family variable.  This is the terminal coordinate API needed by the
asymmetric far-pair construction.
-/

open MeasureTheory Set
open scoped BigOperators ENNReal

namespace Erdos1165.AsymmetricExtractedTerminalRightReplacement

open AppendixPair AsymmetricSharedPrefixRightReplacement
open MarkedBoundaryVisitKernel MarkedBridgeFactorization
open SharedPrefixPairCoarsePartition SharedPrefixPairEventParsing
open SharedPrefixPairExtractedAtom SharedPrefixPairExtractedMarkedAtom
open SharedPrefixPairExtraction SharedPrefixPairFactorization
open SharedPrefixPairMergedSkeleton TerminalExcursionPathwise
open TerminalExtractedBridgeCodes TerminalSkeletonWords ThickPoint
open TerminalExtractedMarkedVisitSplice TerminalSkeletonInvariance
open TerminalSkeletonFactorization

noncomputable section

/-- The actual left terminal bridge tuple cut from the source path. -/
def sourceLeftUnmarkedBridges
    {scale horizon : ℕ} {profileDelta : ℝ} {x y : Point}
    {omega : StepPath}
    (hscale : 1 ≤ scale)
    (hexit : IsOuterExitTime (trajectory omega) scale horizon)
    (hx : SuccessfulPoint (trajectory omega) scale horizon profileDelta x) :
    (i : Fin (terminalCount scale profileDelta)) →
      ExtractedLogicalPairTerminalBridge scale horizon profileDelta x y omega
        (Fin.castAdd (terminalCount scale profileDelta) i) :=
  extractedLogicalPairLeftBoundaryExitWordCode hscale hexit hx

/-- Right-only unmarked terminal replacement atom.  Its left coordinates
are singleton choices containing the exact words of the source `x` branch. -/
def extractedRightOnlyUnmarkedAtom
    {start scale horizon : ℕ} {profileDelta : ℝ} {x y : Point}
    {omega : StepPath}
    (hscale : 1 ≤ scale)
    (hlevel : separationLevel scale x y ≤ scale)
    (hexit : IsOuterExitTime (trajectory omega) scale horizon)
    (hx : SuccessfulPoint (trajectory omega) scale horizon profileDelta x)
    (hy : SuccessfulPoint (trajectory omega) scale horizon profileDelta y)
    (hxbox : x ∈ candidateBox scale) (hybox : y ∈ candidateBox scale) :=
  fixLeft
    (extractedLogicalPairSharedPrefixAtom (start := start)
      hscale hlevel hexit hx hy hxbox hybox)
    (sourceLeftUnmarkedBridges (y := y) hscale hexit hx)

@[simp] theorem extractedLogicalPairComplementarySkeletonAtom_bridgeWord
    {start scale horizon : ℕ} {profileDelta : ℝ} {x y : Point}
    {omega : StepPath}
    (hscale : 1 ≤ scale)
    (hlevel : separationLevel scale x y ≤ scale)
    (hexit : IsOuterExitTime (trajectory omega) scale horizon)
    (hx : SuccessfulPoint (trajectory omega) scale horizon profileDelta x)
    (hy : SuccessfulPoint (trajectory omega) scale horizon profileDelta y)
    (hxbox : x ∈ candidateBox scale) (hybox : y ∈ candidateBox scale)
    (q : Fin (terminalCount scale profileDelta +
      terminalCount scale profileDelta))
    (bridge : ExtractedLogicalPairTerminalBridge scale horizon profileDelta
      x y omega q) :
    (extractedLogicalPairComplementarySkeletonAtom (start := start)
      hscale hlevel hexit hx hy hxbox hybox).bridgeWord q bridge =
        bridge.1 := rfl

@[simp] theorem extractedRightOnlyUnmarkedAtom_rightBridgeWord
    {start scale horizon : ℕ} {profileDelta : ℝ} {x y : Point}
    {omega : StepPath}
    (hscale : 1 ≤ scale)
    (hlevel : separationLevel scale x y ≤ scale)
    (hexit : IsOuterExitTime (trajectory omega) scale horizon)
    (hx : SuccessfulPoint (trajectory omega) scale horizon profileDelta x)
    (hy : SuccessfulPoint (trajectory omega) scale horizon profileDelta y)
    (hxbox : x ∈ candidateBox scale) (hybox : y ∈ candidateBox scale)
    (j : Fin (terminalCount scale profileDelta))
    (bridge : ExtractedLogicalPairTerminalBridge scale horizon profileDelta
      x y omega (Fin.natAdd (terminalCount scale profileDelta) j)) :
    (extractedRightOnlyUnmarkedAtom (start := start)
      hscale hlevel hexit hx hy hxbox hybox).rightBridgeWord j bridge =
        bridge.1 := rfl

/-- Erasure of a right marked logical bridge is injective because both code
types are subtypes of the same stopped word. -/
theorem eraseRightMarkedBridge_injective
    {scale horizon : ℕ} {profileDelta : ℝ} {x y : Point}
    {omega : StepPath}
    {leftVisits rightVisits : Fin (terminalCount scale profileDelta) → ℕ}
    (j : Fin (terminalCount scale profileDelta)) :
    Function.Injective
      (fun b : ExtractedLogicalPairMarkedTerminalBridge scale horizon
          profileDelta x y omega leftVisits rightVisits
          (Fin.natAdd (terminalCount scale profileDelta) j) ↦
        eraseExtractedLogicalPairMarkedTerminalBridge b) := by
  intro a b hab
  apply Subtype.ext
  exact congrArg
    (fun c : ExtractedLogicalPairTerminalBridge scale horizon profileDelta
      x y omega (Fin.natAdd (terminalCount scale profileDelta) j) ↦ c.1) hab

/-- Right-only marked terminal replacement atom.  The right visit vector
may vary (it is the mark exposed to the terminal Poisson kernel), whereas
the complete left source word remains fixed. -/
def extractedRightOnlyMarkedAtom
    {start scale horizon : ℕ} {profileDelta : ℝ} {x y : Point}
    {omega : StepPath}
    (rightVisits : Fin (terminalCount scale profileDelta) → ℕ)
    (hscale : 1 ≤ scale)
    (hlevel : separationLevel scale x y ≤ scale)
    (hexit : IsOuterExitTime (trajectory omega) scale horizon)
    (hx : SuccessfulPoint (trajectory omega) scale horizon profileDelta x)
    (hy : SuccessfulPoint (trajectory omega) scale horizon profileDelta y)
    (hxbox : x ∈ candidateBox scale) (hybox : y ∈ candidateBox scale) :=
  let leftVisits :=
    terminalVisitVector (trajectory omega) scale horizon profileDelta x
  markRight
    (extractedRightOnlyUnmarkedAtom (start := start)
      hscale hlevel hexit hx hy hxbox hybox)
    (fun j (b : ExtractedLogicalPairMarkedTerminalBridge scale horizon
        profileDelta x y omega leftVisits rightVisits
        (Fin.natAdd (terminalCount scale profileDelta) j)) ↦
      eraseExtractedLogicalPairMarkedTerminalBridge b)
    (fun j ↦ eraseRightMarkedBridge_injective j)

/-- Marking the right branch does not change the common retained weight or
the fixed left-word factor. -/
theorem fixedLeftWeight_marked_eq_unmarked
    {start scale horizon : ℕ} {profileDelta : ℝ} {x y : Point}
    {omega : StepPath}
    (rightVisits : Fin (terminalCount scale profileDelta) → ℕ)
    (hscale : 1 ≤ scale)
    (hlevel : separationLevel scale x y ≤ scale)
    (hexit : IsOuterExitTime (trajectory omega) scale horizon)
    (hx : SuccessfulPoint (trajectory omega) scale horizon profileDelta x)
    (hy : SuccessfulPoint (trajectory omega) scale horizon profileDelta y)
    (hxbox : x ∈ candidateBox scale) (hybox : y ∈ candidateBox scale) :
    let unmarked := extractedRightOnlyUnmarkedAtom (start := start)
      hscale hlevel hexit hx hy hxbox hybox
    let marked := extractedRightOnlyMarkedAtom (start := start) rightVisits
      hscale hlevel hexit hx hy hxbox hybox
    marked.commonWeight *
        (∏ i, stoppedWordMass (marked.leftBridgeWord i Unit.unit)) =
      unmarked.commonWeight *
        (∏ i, stoppedWordMass (unmarked.leftBridgeWord i Unit.unit)) := by
  rfl

/-- The right unmarked coordinate is exactly the canonical terminal exit
kernel at `y`; no `x` coordinate appears in the variable product. -/
theorem extractedRightOnlyUnmarkedAtom_rightKernel
    {start scale horizon : ℕ} {profileDelta : ℝ} {x y : Point}
    {omega : StepPath}
    (hscale : 1 ≤ scale)
    (hlevel : separationLevel scale x y ≤ scale)
    (hexit : IsOuterExitTime (trajectory omega) scale horizon)
    (hx : SuccessfulPoint (trajectory omega) scale horizon profileDelta x)
    (hy : SuccessfulPoint (trajectory omega) scale horizon profileDelta y)
    (hxbox : x ∈ candidateBox scale) (hybox : y ∈ candidateBox scale)
    (j : Fin (terminalCount scale profileDelta)) :
    (extractedRightOnlyUnmarkedAtom (start := start)
      hscale hlevel hexit hx hy hxbox hybox).rightKernel j =
      terminalSkeletonKernel (terminalOuterBoundary scale y)
        ((extractTimedTerminalSkeleton scale horizon profileDelta y omega).entrancePoint j)
        ((extractTimedTerminalSkeleton scale horizon profileDelta y omega).exitPoint j) := by
  unfold SharedPrefixPairAtom.rightKernel
  simp only [extractedRightOnlyUnmarkedAtom_rightBridgeWord]
  rw [← fairSteps_stoppedWordEvent
    (prefixFree_boundaryExitWordCode
      (terminalOuterBoundary scale
        (logicalPairCenter x y
          (Fin.natAdd (terminalCount scale profileDelta) j)))
      (pairEntrancePoint
        (extractTimedTerminalSkeleton scale horizon profileDelta x omega)
        (extractTimedTerminalSkeleton scale horizon profileDelta y omega)
        (Fin.natAdd (terminalCount scale profileDelta) j))
      (pairExitPoint
        (extractTimedTerminalSkeleton scale horizon profileDelta x omega)
        (extractTimedTerminalSkeleton scale horizon profileDelta y omega)
        (Fin.natAdd (terminalCount scale profileDelta) j)))]
  rw [← boundaryExitEndpointSteps_eq_stoppedWordEvent]
  unfold terminalSkeletonKernel
  simp only [pairEntrancePoint, pairExitPoint, logicalPairCenter,
    pairValue_natAdd]

/-- Marked right-coordinate analogue. -/
theorem extractedRightOnlyMarkedAtom_rightKernel
    {start scale horizon : ℕ} {profileDelta : ℝ} {x y : Point}
    {omega : StepPath}
    (rightVisits : Fin (terminalCount scale profileDelta) → ℕ)
    (hscale : 1 ≤ scale)
    (hlevel : separationLevel scale x y ≤ scale)
    (hexit : IsOuterExitTime (trajectory omega) scale horizon)
    (hx : SuccessfulPoint (trajectory omega) scale horizon profileDelta x)
    (hy : SuccessfulPoint (trajectory omega) scale horizon profileDelta y)
    (hxbox : x ∈ candidateBox scale) (hybox : y ∈ candidateBox scale)
    (j : Fin (terminalCount scale profileDelta)) :
    (extractedRightOnlyMarkedAtom (start := start) rightVisits
      hscale hlevel hexit hx hy hxbox hybox).rightKernel j =
      terminalMarkedKernel (terminalOuterBoundary scale y) y
        ((extractTimedTerminalSkeleton scale horizon profileDelta y omega).entrancePoint j)
        (rightVisits j)
        ((extractTimedTerminalSkeleton scale horizon profileDelta y omega).exitPoint j) := by
  unfold extractedRightOnlyMarkedAtom
  unfold SharedPrefixPairAtom.rightKernel
  simp only [markRight_rightBridgeWord,
    extractedRightOnlyUnmarkedAtom_rightBridgeWord,
    eraseExtractedLogicalPairMarkedTerminalBridge_word]
  rw [← fairSteps_stoppedWordEvent
    (prefixFree_boundaryVisitExitWordCode
        (terminalOuterBoundary scale
          (logicalPairCenter x y
            (Fin.natAdd (terminalCount scale profileDelta) j)))
        (logicalPairCenter x y
          (Fin.natAdd (terminalCount scale profileDelta) j))
        (pairEntrancePoint
          (extractTimedTerminalSkeleton scale horizon profileDelta x omega)
          (extractTimedTerminalSkeleton scale horizon profileDelta y omega)
          (Fin.natAdd (terminalCount scale profileDelta) j))
        (logicalPairVisitVector
          (terminalVisitVector (trajectory omega) scale horizon profileDelta x)
          rightVisits (Fin.natAdd (terminalCount scale profileDelta) j))
        (pairExitPoint
          (extractTimedTerminalSkeleton scale horizon profileDelta x omega)
          (extractTimedTerminalSkeleton scale horizon profileDelta y omega)
          (Fin.natAdd (terminalCount scale profileDelta) j)))]
  rw [← boundaryVisitExitAtom_eq_stoppedWordEvent _ _ _ _ _
    (logicalPairCenter_not_mem_terminalOuterBoundary hscale
      (Fin.natAdd (terminalCount scale profileDelta) j))]
  unfold terminalMarkedKernel
  simp only [pairEntrancePoint, pairExitPoint, logicalPairCenter,
    logicalPairVisitVector_natAdd, pairValue_natAdd]

/-- The source stopped word is contained in the right-only unmarked atom. -/
theorem source_mem_extractedRightOnlyUnmarkedAtom
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
    omega ∈ (extractedRightOnlyUnmarkedAtom
      (omega := shiftSteps start omega) (start := start)
      hscale hlevel hexit hx hy hxbox hybox).event := by
  let sourceRight := fun j ↦
    extractedLogicalPairRightBoundaryExitWordCode
      (x := x) hscale hexit hy j
  have hcylinder : omega ∈ stoppedWordCylinder
      ((extractedLogicalPairSharedPrefixAtom (start := start)
        hscale hlevel hexit hx hy hxbox hybox).assemble
        (stepPrefix start omega,
          (sourceLeftUnmarkedBridges (y := y) hscale hexit hx,
            sourceRight))) := by
    change omega ∈ stoppedWordCylinder
      ((extractedLogicalPairComplementarySkeletonAtom (start := start)
        hscale hlevel hexit hx hy hxbox hybox).assemble
          (stepPrefix start omega,
            extractedLogicalPairBoundaryExitWordCode hscale hexit hx hy))
    let sigma := shiftSteps start omega
    let left := extractTimedTerminalSkeleton scale horizon profileDelta x sigma
    let right := extractTimedTerminalSkeleton scale horizon profileDelta y sigma
    change omega ∈ stoppedWordCylinder
      (assembleAfterPrefix (stepPrefix start omega)
        (compressTimedSkeleton sigma (mergeTimedTerminalSkeleton left right))
        (chronologicalPairBridgeWords
          (extractedLogicalPairBoundaryExitWordCode hscale hexit hx hy)))
    rw [chronologicalPairBridgeWords,
      extractedLogicalPairBoundaryExitWordCode_erased,
      chronologicalValues_logicalIntervalWords]
    exact mem_stoppedWordCylinder_assembleAfterPrefix_packetOfTimedSkeleton
      omega (mergeTimedTerminalSkeleton left right)
        (extractMergedTimedTerminalSkeleton_wellFormed
          hscale hlevel hexit hx hy)
  exact stoppedWordCylinder_source_subset_fixLeft_event
    (extractedLogicalPairSharedPrefixAtom (start := start)
      hscale hlevel hexit hx hy hxbox hybox)
    (sourceLeftUnmarkedBridges (y := y) hscale hexit hx)
    sourceRight (stepPrefix start omega) hcylinder

end

end Erdos1165.AsymmetricExtractedTerminalRightReplacement
