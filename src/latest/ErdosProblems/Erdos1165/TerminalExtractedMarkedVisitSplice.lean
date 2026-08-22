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

import ErdosProblems.Erdos1165.TerminalExtractedClockSplice

/-!
# Marked visits under an extracted terminal splice

The declarations below isolate every dependent endpoint transport from the
final visit-vector theorem.  Its public statement therefore uses exactly the
compressed skeleton endpoints and the literal finite words in the marked
bridge tuple.
-/

namespace Erdos1165.TerminalExtractedMarkedVisitSplice

open ThickPoint TerminalExcursionPathwise TerminalSkeletonWords
open TerminalVisitSpliceInvariance TerminalClockSplice
open TerminalExtractedClockSplice TerminalPacketEndpointAlignment
open TerminalGlobalExitSplice MarkedBridgeFactorization
open TerminalSequentialVisitLaw

noncomputable section

/-- Forget the target-visit certificate of a marked first-boundary word. -/
def eraseBoundaryVisitExitWordCode
    {boundary : Set Point} {target start endpoint : Point} {visits : ℕ}
    (bridge : BoundaryVisitExitWordCode boundary target start visits endpoint) :
    BoundaryExitWordCode boundary start endpoint :=
  ⟨bridge.1, bridge.2.1, bridge.2.2.2⟩

@[simp] theorem eraseBoundaryVisitExitWordCode_word
    {boundary : Set Point} {target start endpoint : Point} {visits : ℕ}
    (bridge : BoundaryVisitExitWordCode boundary target start visits endpoint) :
    (eraseBoundaryVisitExitWordCode bridge).1 = bridge.1 := rfl

/-- Change only the displayed endpoints of a marked bridge code. -/
def transportBoundaryVisitExitWordCode
    {boundary : Set Point} {target start start' endpoint endpoint' : Point}
    {visits : ℕ}
    (hstart : start = start') (hendpoint : endpoint = endpoint')
    (bridge : BoundaryVisitExitWordCode boundary target start visits endpoint) :
    BoundaryVisitExitWordCode boundary target start' visits endpoint' := by
  cases hstart
  cases hendpoint
  exact bridge

@[simp] theorem transportBoundaryVisitExitWordCode_word
    {boundary : Set Point} {target start start' endpoint endpoint' : Point}
    {visits : ℕ}
    (hstart : start = start') (hendpoint : endpoint = endpoint')
    (bridge : BoundaryVisitExitWordCode boundary target start visits endpoint) :
    (transportBoundaryVisitExitWordCode hstart hendpoint bridge).1 = bridge.1 := by
  cases hstart
  cases hendpoint
  rfl

/-- The compressed endpoint projections transported to the corresponding
positions of the extracted timed skeleton. -/
def boundaryVisitExitWordCodeOfCompressedEndpoints
    {scale horizon : ℕ} {profileDelta : ℝ} {x : Point}
    {omega : StepPath}
    {visits : Fin (AppendixLocalTime.requiredTerminalCount scale profileDelta) → ℕ}
    {j : Fin (AppendixLocalTime.requiredTerminalCount scale profileDelta)}
    (bridge : BoundaryVisitExitWordCode (terminalOuterBoundary scale x) x
      ((extractTerminalSkeletonCode scale horizon profileDelta x omega).2.1 j)
      (visits j)
      ((extractTerminalSkeletonCode scale horizon profileDelta x omega).2.2 j)) :
    BoundaryVisitExitWordCode (terminalOuterBoundary scale x) x
      (trajectory omega
        ((extractTimedTerminalSkeleton scale horizon profileDelta x omega).entrance j))
      (visits j)
      (trajectory omega
        ((extractTimedTerminalSkeleton scale horizon profileDelta x omega).exit j)) := by
  have hstart := congrFun (extractTerminalSkeletonCode_entrancePoints_eq
    scale horizon profileDelta x omega) j
  have hend := congrFun (extractTerminalSkeletonCode_exitPoints_eq
    scale horizon profileDelta x omega) j
  exact transportBoundaryVisitExitWordCode
    (hstart.trans (extractTimedTerminalSkeleton_entrancePoint_eq
      scale horizon profileDelta x omega j))
    (hend.trans (extractTimedTerminalSkeleton_exitPoint_eq
      scale horizon profileDelta x omega j)) bridge

@[simp] theorem boundaryVisitExitWordCodeOfCompressedEndpoints_word
    {scale horizon : ℕ} {profileDelta : ℝ} {x : Point}
    {omega : StepPath}
    {visits : Fin (AppendixLocalTime.requiredTerminalCount scale profileDelta) → ℕ}
    {j : Fin (AppendixLocalTime.requiredTerminalCount scale profileDelta)}
    (bridge : BoundaryVisitExitWordCode (terminalOuterBoundary scale x) x
      ((extractTerminalSkeletonCode scale horizon profileDelta x omega).2.1 j)
      (visits j)
      ((extractTerminalSkeletonCode scale horizon profileDelta x omega).2.2 j)) :
    (boundaryVisitExitWordCodeOfCompressedEndpoints bridge).1 = bridge.1 := by
  unfold boundaryVisitExitWordCodeOfCompressedEndpoints
  exact transportBoundaryVisitExitWordCode_word _ _ _

/-- Marked bridges transported to the timed endpoint indices. -/
def timedMarkedBridgesOfCompressed
    {scale horizon : ℕ} {profileDelta : ℝ} {x : Point}
    {omega : StepPath}
    (visits : Fin (AppendixLocalTime.requiredTerminalCount scale profileDelta) → ℕ)
    (bridges : ∀ j : Fin
      (AppendixLocalTime.requiredTerminalCount scale profileDelta),
      BoundaryVisitExitWordCode (terminalOuterBoundary scale x) x
        ((extractTerminalSkeletonCode scale horizon profileDelta x omega).2.1 j)
        (visits j)
        ((extractTerminalSkeletonCode scale horizon profileDelta x omega).2.2 j)) :
    ∀ j : Fin (AppendixLocalTime.requiredTerminalCount scale profileDelta),
      BoundaryVisitExitWordCode (terminalOuterBoundary scale x) x
        (trajectory omega
          ((extractTimedTerminalSkeleton scale horizon profileDelta x omega).entrance j))
        (visits j)
        (trajectory omega
          ((extractTimedTerminalSkeleton scale horizon profileDelta x omega).exit j)) :=
  fun j ↦ boundaryVisitExitWordCodeOfCompressedEndpoints (bridges j)

/-- The same timed bridge tuple with its visit proof forgotten. -/
def timedUnmarkedBridgesOfCompressedMarked
    {scale horizon : ℕ} {profileDelta : ℝ} {x : Point}
    {omega : StepPath}
    (visits : Fin (AppendixLocalTime.requiredTerminalCount scale profileDelta) → ℕ)
    (bridges : ∀ j : Fin
      (AppendixLocalTime.requiredTerminalCount scale profileDelta),
      BoundaryVisitExitWordCode (terminalOuterBoundary scale x) x
        ((extractTerminalSkeletonCode scale horizon profileDelta x omega).2.1 j)
        (visits j)
        ((extractTerminalSkeletonCode scale horizon profileDelta x omega).2.2 j)) :
    ∀ j : Fin (AppendixLocalTime.requiredTerminalCount scale profileDelta),
      BoundaryExitWordCode (terminalOuterBoundary scale x)
        (trajectory omega
          ((extractTimedTerminalSkeleton scale horizon profileDelta x omega).entrance j))
        (trajectory omega
          ((extractTimedTerminalSkeleton scale horizon profileDelta x omega).exit j)) :=
  fun j ↦ eraseBoundaryVisitExitWordCode
    (timedMarkedBridgesOfCompressed visits bridges j)

/-- Literal word family of the transported marked bridges. -/
def timedWordsOfCompressedBoundaryVisitExitWordCodes
    {scale horizon : ℕ} {profileDelta : ℝ} {x : Point}
    {omega : StepPath}
    (visits : Fin (AppendixLocalTime.requiredTerminalCount scale profileDelta) → ℕ)
    (bridges : ∀ j : Fin
      (AppendixLocalTime.requiredTerminalCount scale profileDelta),
      BoundaryVisitExitWordCode (terminalOuterBoundary scale x) x
        ((extractTerminalSkeletonCode scale horizon profileDelta x omega).2.1 j)
        (visits j)
        ((extractTerminalSkeletonCode scale horizon profileDelta x omega).2.2 j)) :
    TerminalSegmentWords
      (AppendixLocalTime.requiredTerminalCount scale profileDelta) :=
  fun j ↦ List.ofFn (timedMarkedBridgesOfCompressed visits bridges j).1.2

@[simp] theorem timedWordsOfCompressedBoundaryVisitExitWordCodes_eq
    {scale horizon : ℕ} {profileDelta : ℝ} {x : Point}
    {omega : StepPath}
    (visits : Fin (AppendixLocalTime.requiredTerminalCount scale profileDelta) → ℕ)
    (bridges : ∀ j : Fin
      (AppendixLocalTime.requiredTerminalCount scale profileDelta),
      BoundaryVisitExitWordCode (terminalOuterBoundary scale x) x
        ((extractTerminalSkeletonCode scale horizon profileDelta x omega).2.1 j)
        (visits j)
        ((extractTerminalSkeletonCode scale horizon profileDelta x omega).2.2 j)) :
    timedWordsOfCompressedBoundaryVisitExitWordCodes visits bridges =
      (fun j ↦ List.ofFn (bridges j).1.2) := by
  funext j
  unfold timedWordsOfCompressedBoundaryVisitExitWordCodes
  rw [show (timedMarkedBridgesOfCompressed visits bridges j).1 =
      (bridges j).1 by
    exact boundaryVisitExitWordCodeOfCompressedEndpoints_word (bridges j)]

/-! ## Compressed unmarked erasure -/

/-- Forget the visit certificate without changing the compressed endpoint
indices. -/
def compressedUnmarkedBridgesOfMarked
    {scale horizon : ℕ} {profileDelta : ℝ} {x : Point}
    {omega : StepPath}
    (visits : Fin (AppendixLocalTime.requiredTerminalCount scale profileDelta) → ℕ)
    (bridges : ∀ j : Fin
      (AppendixLocalTime.requiredTerminalCount scale profileDelta),
      BoundaryVisitExitWordCode (terminalOuterBoundary scale x) x
        ((extractTerminalSkeletonCode scale horizon profileDelta x omega).2.1 j)
        (visits j)
        ((extractTerminalSkeletonCode scale horizon profileDelta x omega).2.2 j)) :
    ∀ j : Fin (AppendixLocalTime.requiredTerminalCount scale profileDelta),
      BoundaryExitWordCode (terminalOuterBoundary scale x)
        ((extractTerminalSkeletonCode scale horizon profileDelta x omega).2.1 j)
        ((extractTerminalSkeletonCode scale horizon profileDelta x omega).2.2 j) :=
  fun j ↦ eraseBoundaryVisitExitWordCode (bridges j)

@[simp] theorem compressedUnmarkedBridgesOfMarked_word
    {scale horizon : ℕ} {profileDelta : ℝ} {x : Point}
    {omega : StepPath}
    (visits : Fin (AppendixLocalTime.requiredTerminalCount scale profileDelta) → ℕ)
    (bridges : ∀ j : Fin
      (AppendixLocalTime.requiredTerminalCount scale profileDelta),
      BoundaryVisitExitWordCode (terminalOuterBoundary scale x) x
        ((extractTerminalSkeletonCode scale horizon profileDelta x omega).2.1 j)
        (visits j)
        ((extractTerminalSkeletonCode scale horizon profileDelta x omega).2.2 j))
    (j : Fin (AppendixLocalTime.requiredTerminalCount scale profileDelta)) :
    (compressedUnmarkedBridgesOfMarked visits bridges j).1 = (bridges j).1 := rfl

/-! ## Marked visit recovery -/

/-- A recovered compressed code turns an identified entrance clock into the
corresponding compressed entrance point. -/
theorem trajectory_offset_eq_compressedEntrance_of_clock_code
    {scale oldHorizon newHorizon : ℕ} {profileDelta : ℝ} {x : Point}
    {oldOmega newOmega : StepPath}
    {j : Fin (AppendixLocalTime.requiredTerminalCount scale profileDelta)}
    {offset : ℕ}
    (hclock : extractedEntrance (trajectory newOmega) scale newHorizon x (j : ℕ) =
      offset)
    (hcode : extractTerminalSkeletonCode scale newHorizon profileDelta x newOmega =
      extractTerminalSkeletonCode scale oldHorizon profileDelta x oldOmega) :
    trajectory newOmega offset =
      (extractTerminalSkeletonCode scale oldHorizon profileDelta x oldOmega).2.1 j := by
  rw [← hclock]
  change trajectory newOmega
      ((extractTimedTerminalSkeleton scale newHorizon profileDelta x newOmega).entrance j) = _
  rw [← extractTimedTerminalSkeleton_entrancePoint_eq]
  rw [← congrFun (extractTerminalSkeletonCode_entrancePoints_eq
    scale newHorizon profileDelta x newOmega) j]
  rw [hcode]

/-- Positive-packet visit-vector recovery for literal compressed marked
bridge words. -/
theorem terminalVisitVector_reconstructed_of_compressedBoundaryVisitExitWordCodes_of_pos
    {scale horizon : ℕ} {profileDelta : ℝ} {x : Point}
    {omega : StepPath}
    (hscale : 1 ≤ scale)
    (hexit : IsOuterExitTime (trajectory omega) scale horizon)
    (hx : SuccessfulPoint (trajectory omega) scale horizon profileDelta x)
    (hm : 0 < AppendixLocalTime.requiredTerminalCount scale profileDelta)
    (visits : Fin (AppendixLocalTime.requiredTerminalCount scale profileDelta) → ℕ)
    (bridges : ∀ j : Fin
      (AppendixLocalTime.requiredTerminalCount scale profileDelta),
      BoundaryVisitExitWordCode (terminalOuterBoundary scale x) x
        ((extractTerminalSkeletonCode scale horizon profileDelta x omega).2.1 j)
        (visits j)
        ((extractTerminalSkeletonCode scale horizon profileDelta x omega).2.2 j)) :
    let m := AppendixLocalTime.requiredTerminalCount scale profileDelta
    let t := extractTimedTerminalSkeleton scale horizon profileDelta x omega
    let pieces := complementaryPieces m omega 0 horizon t.entrance t.exit
    let words : TerminalSegmentWords m := fun j ↦ List.ofFn (bridges j).1.2
    let newHorizon := (alternatingConcat m pieces words).length
    terminalVisitVector
      (trajectory (reconstructedTerminalStepPath pieces words)) scale
      newHorizon profileDelta x = visits := by
  classical
  dsimp only
  let m := AppendixLocalTime.requiredTerminalCount scale profileDelta
  let t := extractTimedTerminalSkeleton scale horizon profileDelta x omega
  let pieces := complementaryPieces m omega 0 horizon t.entrance t.exit
  let words : TerminalSegmentWords m := fun j ↦ List.ofFn (bridges j).1.2
  let newOmega := reconstructedTerminalStepPath pieces words
  let newHorizon := (alternatingConcat m pieces words).length
  let unmarked := compressedUnmarkedBridgesOfMarked visits bridges
  have hwords : (fun j ↦ List.ofFn (unmarked j).1.2) = words := by
    funext j
    rfl
  have hclocks :=
    terminalClocks_reconstructed_of_compressedBoundaryExitWordCodes_of_pos
      hscale hexit hx hm unmarked
  dsimp only at hclocks
  rw [hwords] at hclocks
  have hcode :=
    extractTerminalSkeletonCode_reconstructed_of_compressedBoundaryExitWordCodes
      hscale hexit hx unmarked
  dsimp only at hcode
  rw [hwords] at hcode
  apply terminalVisitVector_reconstructed_eq_of_admissibleReplacementWords
    scale newHorizon profileDelta x pieces words
      (extractTerminalSkeletonCode scale horizon profileDelta x omega).2.1
      (extractTerminalSkeletonCode scale horizon profileDelta x omega).2.2 visits
  · intro j
    exact trajectory_offset_eq_compressedEntrance_of_clock_code
      (hclocks j).1 hcode
  · intro j
    exact admissibleReplacementWord_of_boundaryVisitExitWordCode
      (terminalOuterBoundary scale x) x
      ((extractTerminalSkeletonCode scale horizon profileDelta x omega).2.1 j)
      ((extractTerminalSkeletonCode scale horizon profileDelta x omega).2.2 j)
      (visits j) (bridges j)
  · intro j
    exact (hclocks j).1
  · intro j
    exact (hclocks j).2

/-- Compressed-endpoint marked visit recovery with the literal raw words in
the reconstructed path.  This includes the vacuous empty-packet case. -/
theorem terminalVisitVector_reconstructed_of_compressedBoundaryVisitExitWordCodes
    {scale horizon : ℕ} {profileDelta : ℝ} {x : Point}
    {omega : StepPath}
    (hscale : 1 ≤ scale)
    (hexit : IsOuterExitTime (trajectory omega) scale horizon)
    (hx : SuccessfulPoint (trajectory omega) scale horizon profileDelta x)
    (visits : Fin (AppendixLocalTime.requiredTerminalCount scale profileDelta) → ℕ)
    (bridges : ∀ j : Fin
      (AppendixLocalTime.requiredTerminalCount scale profileDelta),
      BoundaryVisitExitWordCode (terminalOuterBoundary scale x) x
        ((extractTerminalSkeletonCode scale horizon profileDelta x omega).2.1 j)
        (visits j)
        ((extractTerminalSkeletonCode scale horizon profileDelta x omega).2.2 j)) :
    let m := AppendixLocalTime.requiredTerminalCount scale profileDelta
    let t := extractTimedTerminalSkeleton scale horizon profileDelta x omega
    let pieces := complementaryPieces m omega 0 horizon t.entrance t.exit
    let words : TerminalSegmentWords m := fun j ↦ List.ofFn (bridges j).1.2
    let newHorizon := (alternatingConcat m pieces words).length
    terminalVisitVector
      (trajectory (reconstructedTerminalStepPath pieces words)) scale
      newHorizon profileDelta x = visits := by
  classical
  by_cases hm : 0 < AppendixLocalTime.requiredTerminalCount scale profileDelta
  · exact
      terminalVisitVector_reconstructed_of_compressedBoundaryVisitExitWordCodes_of_pos
        hscale hexit hx hm visits bridges
  · dsimp only
    funext j
    exact (hm (Nat.zero_lt_of_lt j.isLt)).elim

end

end Erdos1165.TerminalExtractedMarkedVisitSplice
