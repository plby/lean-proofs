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

import ErdosProblems.Erdos1165.TerminalPacketEndpointAlignment
import ErdosProblems.Erdos1165.TerminalRetainedHitSplice

/-!
# Exact terminal clocks after canonical finite-word replacement

This file is the concrete adapter from an extracted timed terminal skeleton
to the generic splice-clock theorem.  The only replacement data are literal
`BoundaryExitWordCode`s with the endpoints recorded by the original timed
skeleton.  Endpoint alignment, all retained first-hit segments, and the
absolute first-hit property of every inserted word are then derived rather
than assumed.
-/

namespace Erdos1165.TerminalExtractedClockSplice

open ThickPoint TerminalExcursionPathwise TerminalSkeletonWords
open TerminalVisitSpliceInvariance TerminalClockSplice
open TerminalRetainedHitSplice TerminalPacketEndpointAlignment
open TerminalRetainedPieceOffsets
open TerminalGlobalExitSplice MarkedBridgeFactorization

noncomputable section

/-- Canonical endpoint-matched replacement words identify the first selected
terminal excursion clocks with their literal offsets in the reconstructed
alternating word. -/
theorem terminalClocks_reconstructed_of_boundaryExitWordCodes
    {scale horizon : ℕ} {profileDelta : ℝ} {x : Point}
    {omega : StepPath}
    (hscale : 1 ≤ scale)
    (hexit : IsOuterExitTime (trajectory omega) scale horizon)
    (hx : SuccessfulPoint (trajectory omega) scale horizon profileDelta x)
    (hm : 0 < AppendixLocalTime.requiredTerminalCount scale profileDelta)
    (bridges : ∀ j : Fin
      (AppendixLocalTime.requiredTerminalCount scale profileDelta),
      BoundaryExitWordCode (terminalOuterBoundary scale x)
        (trajectory omega
          ((extractTimedTerminalSkeleton scale horizon profileDelta x omega).entrance j))
        (trajectory omega
          ((extractTimedTerminalSkeleton scale horizon profileDelta x omega).exit j))) :
    let m := AppendixLocalTime.requiredTerminalCount scale profileDelta
    let t := extractTimedTerminalSkeleton scale horizon profileDelta x omega
    let pieces := complementaryPieces m omega 0 horizon t.entrance t.exit
    let words : TerminalSegmentWords m := fun j ↦ List.ofFn (bridges j).1.2
    let newHorizon := (alternatingConcat m pieces words).length
    ∀ j : Fin m,
      extractedEntrance
          (trajectory (reconstructedTerminalStepPath pieces words))
          scale newHorizon x (j : ℕ) =
        replacementWordStart m pieces words j ∧
      extractedExit
          (trajectory (reconstructedTerminalStepPath pieces words))
          scale newHorizon x (j : ℕ) =
        replacementWordStop pieces words j := by
  classical
  dsimp only
  let m := AppendixLocalTime.requiredTerminalCount scale profileDelta
  let t := extractTimedTerminalSkeleton scale horizon profileDelta x omega
  let pieces := complementaryPieces m omega 0 horizon t.entrance t.exit
  let words : TerminalSegmentWords m := fun j ↦ List.ofFn (bridges j).1.2
  let newHorizon := (alternatingConcat m pieces words).length
  have ht : t.WellFormed := by
    exact extractTimedTerminalSkeleton_wellFormed_of_stopped_success
      hscale hexit hx
  have halign : ∀ j : Fin m,
      trajectory (reconstructedTerminalStepPath pieces words)
          (replacementWordStart m pieces words j) =
            trajectory omega (t.entrance j) ∧
      trajectory (reconstructedTerminalStepPath pieces words)
          (replacementWordStop pieces words j) =
            trajectory omega (t.exit j) := by
    simpa [m, t, pieces, words, extractTimedTerminalSkeleton] using
      replacementWordStart_stop_alignment_of_boundaryExitWordCodes
        omega t ht (terminalOuterBoundary scale x) bridges
  have retained : RetainedFirstHitInputs omega t words
      (terminalOuterBoundary scale x) (terminalInnerBoundary scale x) := by
    apply retainedFirstHitInputsOfExtractedTimedSkeleton
      hscale hexit hx hm words
    intro j
    simpa [m, t, pieces, words] using (halign j).2
  let visits : Fin m → ℕ := fun j ↦
    replacementWordVisitCount (trajectory omega (t.entrance j)) x (words j)
  have hadmissible : ∀ j : Fin m,
      AdmissibleReplacementWord (terminalOuterBoundary scale x) x
        (trajectory omega (t.entrance j)) (trajectory omega (t.exit j))
        (visits j) (words j) := by
    intro j
    simpa [visits, words] using
      admissibleReplacementWord_of_boundaryExitWordCode
        (terminalOuterBoundary scale x) x
        (trajectory omega (t.entrance j)) (trajectory omega (t.exit j))
        (bridges j)
  have hclocks := terminalClocks_reconstructed_eq_replacementOffsets hm
    pieces words (terminalOuterBoundary scale x) (terminalInnerBoundary scale x)
    x (fun j ↦ trajectory omega (t.entrance j))
    (fun j ↦ trajectory omega (t.exit j)) visits newHorizon
    retained.initialOuterTime le_rfl retained.firstOuter
    (retained.firstInnerZero hm) retained.firstInnerSucc
    (fun j ↦ (halign j).1) hadmissible
  intro j
  have hj := hclocks j
  simpa [extractedEntrance, extractedExit, terminalSegmentExitTime,
    m, t, pieces, words, newHorizon] using hj

/-- Re-extracting the compressed terminal skeleton after canonical word
replacement recovers the original compressed code exactly. -/
theorem extractTerminalSkeletonCode_reconstructed_of_boundaryExitWordCodes_of_pos
    {scale horizon : ℕ} {profileDelta : ℝ} {x : Point}
    {omega : StepPath}
    (hscale : 1 ≤ scale)
    (hexit : IsOuterExitTime (trajectory omega) scale horizon)
    (hx : SuccessfulPoint (trajectory omega) scale horizon profileDelta x)
    (hm : 0 < AppendixLocalTime.requiredTerminalCount scale profileDelta)
    (bridges : ∀ j : Fin
      (AppendixLocalTime.requiredTerminalCount scale profileDelta),
      BoundaryExitWordCode (terminalOuterBoundary scale x)
        (trajectory omega
          ((extractTimedTerminalSkeleton scale horizon profileDelta x omega).entrance j))
        (trajectory omega
          ((extractTimedTerminalSkeleton scale horizon profileDelta x omega).exit j))) :
    let m := AppendixLocalTime.requiredTerminalCount scale profileDelta
    let t := extractTimedTerminalSkeleton scale horizon profileDelta x omega
    let pieces := complementaryPieces m omega 0 horizon t.entrance t.exit
    let words : TerminalSegmentWords m := fun j ↦ List.ofFn (bridges j).1.2
    let newHorizon := (alternatingConcat m pieces words).length
    extractTerminalSkeletonCode scale newHorizon profileDelta x
        (reconstructedTerminalStepPath pieces words) =
      extractTerminalSkeletonCode scale horizon profileDelta x omega := by
  classical
  dsimp only
  let m := AppendixLocalTime.requiredTerminalCount scale profileDelta
  let t := extractTimedTerminalSkeleton scale horizon profileDelta x omega
  let pieces := complementaryPieces m omega 0 horizon t.entrance t.exit
  let words : TerminalSegmentWords m := fun j ↦ List.ofFn (bridges j).1.2
  let newOmega := reconstructedTerminalStepPath pieces words
  let newHorizon := (alternatingConcat m pieces words).length
  let newT := extractTimedTerminalSkeleton scale newHorizon profileDelta x newOmega
  have ht : t.WellFormed :=
    extractTimedTerminalSkeleton_wellFormed_of_stopped_success hscale hexit hx
  have halign : ∀ j : Fin m,
      trajectory newOmega (replacementWordStart m pieces words j) =
          trajectory omega (t.entrance j) ∧
      trajectory newOmega (replacementWordStop pieces words j) =
          trajectory omega (t.exit j) := by
    simpa [m, t, pieces, words, newOmega, extractTimedTerminalSkeleton] using
      replacementWordStart_stop_alignment_of_boundaryExitWordCodes
        omega t ht (terminalOuterBoundary scale x) bridges
  have hclocks : ∀ j : Fin m,
      newT.entrance j = replacementWordStart m pieces words j ∧
      newT.exit j = replacementWordStop pieces words j := by
    exact terminalClocks_reconstructed_of_boundaryExitWordCodes
      hscale hexit hx hm bridges
  have hentrancePoint : newT.entrancePoint = t.entrancePoint := by
    funext j
    rw [extractTimedTerminalSkeleton_entrancePoint_eq]
    rw [extractTimedTerminalSkeleton_entrancePoint_eq]
    rw [(hclocks j).1]
    exact (halign j).1
  have hexitPoint : newT.exitPoint = t.exitPoint := by
    funext j
    rw [extractTimedTerminalSkeleton_exitPoint_eq]
    rw [extractTimedTerminalSkeleton_exitPoint_eq]
    rw [(hclocks j).2]
    exact (halign j).2
  have hrecovery :=
    compressTimedSkeleton_reconstructed_eq_of_replacementOffsets pieces words newT
      t.entrancePoint t.exitPoint rfl (fun j ↦ (hclocks j).1)
      (fun j ↦ (hclocks j).2) hentrancePoint hexitPoint
  unfold extractTerminalSkeletonCode
  have horiginal : compressTimedSkeleton omega t =
      (⟨pieces⟩, (t.entrancePoint, t.exitPoint)) := rfl
  exact hrecovery.trans horiginal.symm

/-- Public code-recovery adapter, including the degenerate empty terminal
packet.  Positivity is needed only to identify nonempty terminal clocks; for
an empty packet all clock and endpoint arrays are vacuous. -/
theorem extractTerminalSkeletonCode_reconstructed_of_boundaryExitWordCodes
    {scale horizon : ℕ} {profileDelta : ℝ} {x : Point}
    {omega : StepPath}
    (hscale : 1 ≤ scale)
    (hexit : IsOuterExitTime (trajectory omega) scale horizon)
    (hx : SuccessfulPoint (trajectory omega) scale horizon profileDelta x)
    (bridges : ∀ j : Fin
      (AppendixLocalTime.requiredTerminalCount scale profileDelta),
      BoundaryExitWordCode (terminalOuterBoundary scale x)
        (trajectory omega
          ((extractTimedTerminalSkeleton scale horizon profileDelta x omega).entrance j))
        (trajectory omega
          ((extractTimedTerminalSkeleton scale horizon profileDelta x omega).exit j))) :
    let m := AppendixLocalTime.requiredTerminalCount scale profileDelta
    let t := extractTimedTerminalSkeleton scale horizon profileDelta x omega
    let pieces := complementaryPieces m omega 0 horizon t.entrance t.exit
    let words : TerminalSegmentWords m := fun j ↦ List.ofFn (bridges j).1.2
    let newHorizon := (alternatingConcat m pieces words).length
    extractTerminalSkeletonCode scale newHorizon profileDelta x
        (reconstructedTerminalStepPath pieces words) =
      extractTerminalSkeletonCode scale horizon profileDelta x omega := by
  classical
  by_cases hm : 0 < AppendixLocalTime.requiredTerminalCount scale profileDelta
  · exact extractTerminalSkeletonCode_reconstructed_of_boundaryExitWordCodes_of_pos
      hscale hexit hx hm bridges
  · dsimp only
    let m := AppendixLocalTime.requiredTerminalCount scale profileDelta
    have hm0 : m = 0 := Nat.eq_zero_of_not_pos hm
    let t := extractTimedTerminalSkeleton scale horizon profileDelta x omega
    let pieces := complementaryPieces m omega 0 horizon t.entrance t.exit
    let words : TerminalSegmentWords m := fun j ↦ List.ofFn (bridges j).1.2
    let newOmega := reconstructedTerminalStepPath pieces words
    let newHorizon := (alternatingConcat m pieces words).length
    let newT := extractTimedTerminalSkeleton scale newHorizon profileDelta x newOmega
    have hempty (j : Fin m) : False := by
      have hj := j.isLt
      omega
    have hrecovery :=
      compressTimedSkeleton_reconstructed_eq_of_replacementOffsets pieces words newT
        t.entrancePoint t.exitPoint rfl
        (fun j ↦ (hempty j).elim) (fun j ↦ (hempty j).elim)
        (by funext j; exact (hempty j).elim)
        (by funext j; exact (hempty j).elim)
    unfold extractTerminalSkeletonCode
    have horiginal : compressTimedSkeleton omega t =
        (⟨pieces⟩, (t.entrancePoint, t.exitPoint)) := by
      apply Prod.ext
      · apply TerminalSkeletonData.ext
        change complementaryPieces m omega 0 t.horizon t.entrance t.exit = pieces
        rfl
      · rfl
    exact hrecovery.trans horiginal.symm

/-- Lightweight transport of the endpoint indices of a boundary word code. -/
def transportBoundaryExitWordCode
    {boundary : Set Point} {start start' endpoint endpoint' : Point}
    (hstart : start = start') (hendpoint : endpoint = endpoint')
    (bridge : BoundaryExitWordCode boundary start endpoint) :
    BoundaryExitWordCode boundary start' endpoint' := by
  subst start'
  subst endpoint'
  exact bridge

@[simp] theorem transportBoundaryExitWordCode_word
    {boundary : Set Point} {start start' endpoint endpoint' : Point}
    (hstart : start = start') (hendpoint : endpoint = endpoint')
    (bridge : BoundaryExitWordCode boundary start endpoint) :
    (transportBoundaryExitWordCode hstart hendpoint bridge).1 = bridge.1 := by
  subst start'
  subst endpoint'
  rfl

/-- Change only the displayed endpoint indices of a bridge from the
compressed code projections to the definitionally equal timed positions. -/
def boundaryExitWordCodeOfCompressedEndpoints
    {scale horizon : ℕ} {profileDelta : ℝ} {x : Point}
    {omega : StepPath}
    {j : Fin (AppendixLocalTime.requiredTerminalCount scale profileDelta)}
    (bridge : BoundaryExitWordCode (terminalOuterBoundary scale x)
      ((extractTerminalSkeletonCode scale horizon profileDelta x omega).2.1 j)
      ((extractTerminalSkeletonCode scale horizon profileDelta x omega).2.2 j)) :
    BoundaryExitWordCode (terminalOuterBoundary scale x)
      (trajectory omega
        ((extractTimedTerminalSkeleton scale horizon profileDelta x omega).entrance j))
      (trajectory omega
        ((extractTimedTerminalSkeleton scale horizon profileDelta x omega).exit j)) := by
  have hstart :
      (extractTerminalSkeletonCode scale horizon profileDelta x omega).2.1 j =
        trajectory omega
          ((extractTimedTerminalSkeleton scale horizon profileDelta x omega).entrance j) :=
    (congrFun (extractTerminalSkeletonCode_entrancePoints_eq
      scale horizon profileDelta x omega) j).trans
      (extractTimedTerminalSkeleton_entrancePoint_eq
        scale horizon profileDelta x omega j)
  have hend :
      (extractTerminalSkeletonCode scale horizon profileDelta x omega).2.2 j =
        trajectory omega
          ((extractTimedTerminalSkeleton scale horizon profileDelta x omega).exit j) :=
    (congrFun (extractTerminalSkeletonCode_exitPoints_eq
      scale horizon profileDelta x omega) j).trans
      (extractTimedTerminalSkeleton_exitPoint_eq
        scale horizon profileDelta x omega j)
  exact transportBoundaryExitWordCode hstart hend bridge

@[simp] theorem boundaryExitWordCodeOfCompressedEndpoints_word
    {scale horizon : ℕ} {profileDelta : ℝ} {x : Point}
    {omega : StepPath}
    {j : Fin (AppendixLocalTime.requiredTerminalCount scale profileDelta)}
    (bridge : BoundaryExitWordCode (terminalOuterBoundary scale x)
      ((extractTerminalSkeletonCode scale horizon profileDelta x omega).2.1 j)
      ((extractTerminalSkeletonCode scale horizon profileDelta x omega).2.2 j)) :
    (boundaryExitWordCodeOfCompressedEndpoints bridge).1 = bridge.1 := by
  unfold boundaryExitWordCodeOfCompressedEndpoints
  exact transportBoundaryExitWordCode_word _ _ _

/-- Word family obtained after changing only the displayed endpoint type. -/
def timedWordsOfCompressedBoundaryExitWordCodes
    {scale horizon : ℕ} {profileDelta : ℝ} {x : Point}
    {omega : StepPath}
    (bridges : ∀ j : Fin
      (AppendixLocalTime.requiredTerminalCount scale profileDelta),
      BoundaryExitWordCode (terminalOuterBoundary scale x)
        ((extractTerminalSkeletonCode scale horizon profileDelta x omega).2.1 j)
        ((extractTerminalSkeletonCode scale horizon profileDelta x omega).2.2 j)) :
    TerminalSegmentWords
      (AppendixLocalTime.requiredTerminalCount scale profileDelta) :=
  fun j ↦ List.ofFn
    (boundaryExitWordCodeOfCompressedEndpoints (bridges j)).1.2

/-- The endpoint-type change leaves every literal direction word unchanged. -/
@[simp] theorem timedWordsOfCompressedBoundaryExitWordCodes_eq
    {scale horizon : ℕ} {profileDelta : ℝ} {x : Point}
    {omega : StepPath}
    (bridges : ∀ j : Fin
      (AppendixLocalTime.requiredTerminalCount scale profileDelta),
      BoundaryExitWordCode (terminalOuterBoundary scale x)
        ((extractTerminalSkeletonCode scale horizon profileDelta x omega).2.1 j)
        ((extractTerminalSkeletonCode scale horizon profileDelta x omega).2.2 j)) :
    timedWordsOfCompressedBoundaryExitWordCodes bridges =
      (fun j ↦ List.ofFn (bridges j).1.2) := by
  funext j
  unfold timedWordsOfCompressedBoundaryExitWordCodes
  rw [boundaryExitWordCodeOfCompressedEndpoints_word]

/-- The terminal-clock adapter after changing only the displayed endpoint
indices of a compressed bridge family. -/
theorem terminalClocks_reconstructed_of_transportedCompressedWords_of_pos
    {scale horizon : ℕ} {profileDelta : ℝ} {x : Point}
    {omega : StepPath}
    (hscale : 1 ≤ scale)
    (hexit : IsOuterExitTime (trajectory omega) scale horizon)
    (hx : SuccessfulPoint (trajectory omega) scale horizon profileDelta x)
    (hm : 0 < AppendixLocalTime.requiredTerminalCount scale profileDelta)
    (bridges : ∀ j : Fin
      (AppendixLocalTime.requiredTerminalCount scale profileDelta),
      BoundaryExitWordCode (terminalOuterBoundary scale x)
        ((extractTerminalSkeletonCode scale horizon profileDelta x omega).2.1 j)
        ((extractTerminalSkeletonCode scale horizon profileDelta x omega).2.2 j)) :
    let m := AppendixLocalTime.requiredTerminalCount scale profileDelta
    let t := extractTimedTerminalSkeleton scale horizon profileDelta x omega
    let pieces := complementaryPieces m omega 0 horizon t.entrance t.exit
    let words := timedWordsOfCompressedBoundaryExitWordCodes bridges
    let newHorizon := (alternatingConcat m pieces words).length
    ∀ j : Fin m,
      extractedEntrance
          (trajectory (reconstructedTerminalStepPath pieces words))
          scale newHorizon x (j : ℕ) =
        replacementWordStart m pieces words j ∧
      extractedExit
          (trajectory (reconstructedTerminalStepPath pieces words))
          scale newHorizon x (j : ℕ) =
        replacementWordStop pieces words j := by
  exact terminalClocks_reconstructed_of_boundaryExitWordCodes
    hscale hexit hx hm
      (fun j ↦ boundaryExitWordCodeOfCompressedEndpoints (bridges j))

/-- Compressed-endpoint terminal-clock adapter with the literal bridge words
in the reconstructed path. -/
theorem terminalClocks_reconstructed_of_compressedBoundaryExitWordCodes_of_pos
    {scale horizon : ℕ} {profileDelta : ℝ} {x : Point}
    {omega : StepPath}
    (hscale : 1 ≤ scale)
    (hexit : IsOuterExitTime (trajectory omega) scale horizon)
    (hx : SuccessfulPoint (trajectory omega) scale horizon profileDelta x)
    (hm : 0 < AppendixLocalTime.requiredTerminalCount scale profileDelta)
    (bridges : ∀ j : Fin
      (AppendixLocalTime.requiredTerminalCount scale profileDelta),
      BoundaryExitWordCode (terminalOuterBoundary scale x)
        ((extractTerminalSkeletonCode scale horizon profileDelta x omega).2.1 j)
        ((extractTerminalSkeletonCode scale horizon profileDelta x omega).2.2 j)) :
    let m := AppendixLocalTime.requiredTerminalCount scale profileDelta
    let t := extractTimedTerminalSkeleton scale horizon profileDelta x omega
    let pieces := complementaryPieces m omega 0 horizon t.entrance t.exit
    let words : TerminalSegmentWords m := fun j ↦ List.ofFn (bridges j).1.2
    let newHorizon := (alternatingConcat m pieces words).length
    ∀ j : Fin m,
      extractedEntrance
          (trajectory (reconstructedTerminalStepPath pieces words))
          scale newHorizon x (j : ℕ) =
        replacementWordStart m pieces words j ∧
      extractedExit
          (trajectory (reconstructedTerminalStepPath pieces words))
          scale newHorizon x (j : ℕ) =
        replacementWordStop pieces words j := by
  have h := terminalClocks_reconstructed_of_transportedCompressedWords_of_pos
    hscale hexit hx hm bridges
  rw [timedWordsOfCompressedBoundaryExitWordCodes_eq] at h
  exact h

/-- First, apply code recovery to the explicitly endpoint-transported bridge
family.  Keeping this as a separate declaration bounds elaboration of the
dependent endpoint conversion. -/
theorem extractTerminalSkeletonCode_reconstructed_of_transportedCompressedWords
    {scale horizon : ℕ} {profileDelta : ℝ} {x : Point}
    {omega : StepPath}
    (hscale : 1 ≤ scale)
    (hexit : IsOuterExitTime (trajectory omega) scale horizon)
    (hx : SuccessfulPoint (trajectory omega) scale horizon profileDelta x)
    (bridges : ∀ j : Fin
      (AppendixLocalTime.requiredTerminalCount scale profileDelta),
      BoundaryExitWordCode (terminalOuterBoundary scale x)
        ((extractTerminalSkeletonCode scale horizon profileDelta x omega).2.1 j)
        ((extractTerminalSkeletonCode scale horizon profileDelta x omega).2.2 j)) :
    let m := AppendixLocalTime.requiredTerminalCount scale profileDelta
    let t := extractTimedTerminalSkeleton scale horizon profileDelta x omega
    let pieces := complementaryPieces m omega 0 horizon t.entrance t.exit
    let words := timedWordsOfCompressedBoundaryExitWordCodes bridges
    let newHorizon := (alternatingConcat m pieces words).length
    extractTerminalSkeletonCode scale newHorizon profileDelta x
        (reconstructedTerminalStepPath pieces words) =
      extractTerminalSkeletonCode scale horizon profileDelta x omega := by
  exact extractTerminalSkeletonCode_reconstructed_of_boundaryExitWordCodes
    hscale hexit hx
      (fun j ↦ boundaryExitWordCodeOfCompressedEndpoints (bridges j))

/-- Compressed-endpoint form used by insertion events.  This declaration
packages the definitional identification between the endpoint arrays of the
extracted code and the position fields of its timed witness, so callers do
not need a large dependent `simpa`. -/
theorem extractTerminalSkeletonCode_reconstructed_of_compressedBoundaryExitWordCodes
    {scale horizon : ℕ} {profileDelta : ℝ} {x : Point}
    {omega : StepPath}
    (hscale : 1 ≤ scale)
    (hexit : IsOuterExitTime (trajectory omega) scale horizon)
    (hx : SuccessfulPoint (trajectory omega) scale horizon profileDelta x)
    (bridges : ∀ j : Fin
      (AppendixLocalTime.requiredTerminalCount scale profileDelta),
      BoundaryExitWordCode (terminalOuterBoundary scale x)
        ((extractTerminalSkeletonCode scale horizon profileDelta x omega).2.1 j)
        ((extractTerminalSkeletonCode scale horizon profileDelta x omega).2.2 j)) :
    let m := AppendixLocalTime.requiredTerminalCount scale profileDelta
    let t := extractTimedTerminalSkeleton scale horizon profileDelta x omega
    let pieces := complementaryPieces m omega 0 horizon t.entrance t.exit
    let words : TerminalSegmentWords m := fun j ↦ List.ofFn (bridges j).1.2
    let newHorizon := (alternatingConcat m pieces words).length
    extractTerminalSkeletonCode scale newHorizon profileDelta x
        (reconstructedTerminalStepPath pieces words) =
      extractTerminalSkeletonCode scale horizon profileDelta x omega := by
  have h := extractTerminalSkeletonCode_reconstructed_of_transportedCompressedWords
    hscale hexit hx bridges
  rw [timedWordsOfCompressedBoundaryExitWordCodes_eq] at h
  exact h

end

end Erdos1165.TerminalExtractedClockSplice
