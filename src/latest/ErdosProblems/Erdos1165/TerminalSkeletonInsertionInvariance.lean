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

import ErdosProblems.Erdos1165.TerminalExtractedClockSplice
import ErdosProblems.Erdos1165.TerminalExtractedMarkedVisitSplice
import ErdosProblems.Erdos1165.TerminalExtractedSpliceInvariance
import ErdosProblems.Erdos1165.TerminalSkeletonFactorization

/-!
# Exact terminal-skeleton insertion invariance

This final adapter keeps the stable finite-word skeleton API separate from
the more expensive clock and profile transports.  It proves that canonical
endpoint-matched terminal first-hit words re-extract the same compressed
skeleton, and then identifies the literal insertion unions with the
horizon-collapsed stopped atoms.
-/

open Set

namespace Erdos1165.TerminalSkeletonInsertionInvariance

open ThickPoint Proposition13Measurability TerminalExcursionPathwise
open TerminalSkeletonWords MarkedBridgeFactorization
open TerminalSkeletonInvariance TerminalSkeletonFactorization
open TerminalExtractedClockSplice TerminalVisitSpliceInvariance
open TerminalExtractedSpliceInvariance
open TerminalExtractedMarkedVisitSplice
open TerminalProfileClockEquivalence TerminalClockSplice
open TerminalGlobalExitSplice
open TerminalPacketEndpointAlignment
open TerminalSequentialVisitLaw

noncomputable section

/-! ## Re-extraction from endpoint-matched finite words -/

/-- Re-extraction after insertion recovers any valid compressed skeleton
when the supplied finite words have the recorded endpoints and first hit the
terminal outer boundary at their last vertex.  The nondependent word-family
interface keeps this reusable statement cheap to elaborate. -/
theorem extractTerminalSkeletonCode_assembled_of_valid_words
    {scale : ℕ} {profileDelta : ℝ} {x : Point}
    {code : TerminalSkeletonCode
      (AppendixLocalTime.requiredTerminalCount scale profileDelta)}
    (hscale : 1 ≤ scale)
    (hvalid : ValidTerminalSkeleton scale profileDelta x code)
    (words : TerminalSegmentWords
      (AppendixLocalTime.requiredTerminalCount scale profileDelta))
    (hfirst : ∀ j, AbsoluteBoundaryFirstAt (terminalOuterBoundary scale x)
      (code.2.1 j) (extendStoppedWord
        (TerminalSkeletonInvariance.stoppedWordOfList (words j)))
      (words j).length)
    (hendpoint : ∀ j, PlanarPotential.trajectoryFrom (code.2.1 j)
      (extendStoppedWord
        (TerminalSkeletonInvariance.stoppedWordOfList (words j)))
      (words j).length =
        code.2.2 j) :
    extractTerminalSkeletonCode scale
        (assembledTerminalHorizon code words)
        profileDelta x
        (assembledTerminalPath code words) = code := by
  classical
  obtain ⟨horizon, omega, hexit, hx, hcode⟩ := hvalid
  subst code
  let bridges : (j : Fin
      (AppendixLocalTime.requiredTerminalCount scale profileDelta)) →
      UnmarkedTerminalBridgeCode scale x
        (extractTerminalSkeletonCode scale horizon profileDelta x omega) j :=
    fun j ↦ ⟨TerminalSkeletonInvariance.stoppedWordOfList (words j),
      hfirst j, hendpoint j⟩
  have hrecovered :=
    extractTerminalSkeletonCode_reconstructed_of_compressedBoundaryExitWordCodes
      hscale hexit hx bridges
  have hbridgeWords :
      (fun j ↦ List.ofFn (bridges j).1.2) = words := by
    funext j
    change List.ofFn
      (TerminalSkeletonInvariance.stoppedWordOfList (words j)).2 = words j
    exact TerminalSkeletonInvariance.stoppedWordOfList_toList (words j)
  dsimp only at hrecovered
  rw [hbridgeWords] at hrecovered
  rw [assembledTerminalPath_eq_reconstructedTerminalStepPath,
    assembledTerminalHorizon_eq_alternatingConcat_length,
    extractTerminalSkeletonCode_retainedPiece]
  exact hrecovered

/-! ## Unmarked insertion event -/

/-- Every literal insertion word belongs to the corresponding
horizon-collapsed stopped skeleton atom. -/
theorem unmarkedTerminalInsertionEvent_subset_stoppedTerminalSkeletonAtom
    {start scale : ℕ} {profileDelta : ℝ} {x : Point}
    (hscale : 1 ≤ scale)
    (code : TerminalSkeletonCode
      (AppendixLocalTime.requiredTerminalCount scale profileDelta))
    (hvalid : ValidTerminalSkeleton scale profileDelta x code) :
    unmarkedTerminalInsertionEvent (start := start) (scale := scale)
        (x := x) code ⊆
      stoppedTerminalSkeletonAtom start scale profileDelta x code := by
  classical
  intro sample hsample
  unfold unmarkedTerminalInsertionEvent stoppedWordEvent at hsample
  obtain ⟨⟨pre, bridges⟩, hcylinder⟩ := Set.mem_iUnion.mp hsample
  have htail :=
    TerminalSkeletonInvariance.shiftSteps_mem_assembledTerminalWordCylinder_of_mem_assembleAfterPrefix
      hcylinder
  obtain ⟨horizon, omega, hexit, hx, hcode⟩ := hvalid
  subst code
  let words := unmarkedBridgeWords bridges
  have hglobal : IsOuterExitTime
      (trajectory (assembledTerminalPath
        (extractTerminalSkeletonCode scale horizon profileDelta x omega) words))
      scale (assembledTerminalHorizon
        (extractTerminalSkeletonCode scale horizon profileDelta x omega) words) :=
    isOuterExitTime_assembled_unmarked_of_stopped_success
      (by omega) hexit hx bridges
  have hsuccessful : SuccessfulPoint
      (trajectory (assembledTerminalPath
        (extractTerminalSkeletonCode scale horizon profileDelta x omega) words))
      scale (assembledTerminalHorizon
        (extractTerminalSkeletonCode scale horizon profileDelta x omega) words)
      profileDelta x := by
    have h :=
      successfulPoint_reconstructed_of_compressedBoundaryExitWordCodes_of_one_le
        hscale hexit hx bridges
    rw [assembledTerminalPath_eq_reconstructedTerminalStepPath,
      assembledTerminalHorizon_eq_alternatingConcat_length,
      extractTerminalSkeletonCode_retainedPiece]
    exact h
  have hcode' : extractTerminalSkeletonCode scale
      (assembledTerminalHorizon
        (extractTerminalSkeletonCode scale horizon profileDelta x omega) words)
      profileDelta x
      (assembledTerminalPath
        (extractTerminalSkeletonCode scale horizon profileDelta x omega) words) =
        extractTerminalSkeletonCode scale horizon profileDelta x omega := by
    have h :=
      extractTerminalSkeletonCode_reconstructed_of_compressedBoundaryExitWordCodes
        (by omega) hexit hx bridges
    rw [assembledTerminalPath_eq_reconstructedTerminalStepPath,
      assembledTerminalHorizon_eq_alternatingConcat_length,
      extractTerminalSkeletonCode_retainedPiece]
    exact h
  have hcanonical :=
    stoppedSuccessfulAndCode_of_mem_assembledTerminalWordCylinder
      (by omega) hglobal hsuccessful hcode' htail
  unfold stoppedTerminalSkeletonAtom
  apply Set.mem_iUnion.mpr
  refine ⟨assembledTerminalHorizon
    (extractTerminalSkeletonCode scale horizon profileDelta x omega) words, ?_⟩
  exact ⟨⟨hcanonical.1, hcanonical.2.1⟩, hcanonical.2.2⟩

/-- Exact unmarked event equality at every terminal scale. -/
theorem stoppedTerminalSkeletonAtom_eq_unmarkedTerminalInsertionEvent
    {start scale : ℕ} {profileDelta : ℝ} {x : Point}
    (hscale : 1 ≤ scale)
    (code : TerminalSkeletonCode
      (AppendixLocalTime.requiredTerminalCount scale profileDelta))
    (hvalid : ValidTerminalSkeleton scale profileDelta x code) :
    stoppedTerminalSkeletonAtom start scale profileDelta x code =
      unmarkedTerminalInsertionEvent (start := start) (scale := scale)
        (x := x) code := by
  apply Set.Subset.antisymm
  · exact
      TerminalSkeletonFactorization.stoppedTerminalSkeletonAtom_subset_unmarkedTerminalInsertionEvent
        hscale code
  · exact
      unmarkedTerminalInsertionEvent_subset_stoppedTerminalSkeletonAtom
        hscale code hvalid

/-! ## Marked insertion event -/

/-- Fixed visit marks are recovered coordinatewise from the canonical
inserted words, so the marked insertion union lies in the corresponding
horizon-collapsed marked skeleton atom. -/
theorem markedTerminalInsertionEvent_subset_stoppedMarkedTerminalAtom
    {start scale : ℕ} {profileDelta : ℝ} {x : Point}
    (hscale : 1 ≤ scale)
    (code : TerminalSkeletonCode
      (AppendixLocalTime.requiredTerminalCount scale profileDelta))
    (hvalid : ValidTerminalSkeleton scale profileDelta x code)
    (visits : Fin
      (AppendixLocalTime.requiredTerminalCount scale profileDelta) → ℕ) :
    markedTerminalInsertionEvent (start := start) (scale := scale)
        (x := x) code visits ⊆
      stoppedMarkedTerminalAtom start scale profileDelta x
        (code.1, (code.2.1, (code.2.2, visits))) := by
  classical
  intro sample hsample
  unfold markedTerminalInsertionEvent stoppedWordEvent at hsample
  obtain ⟨⟨pre, bridges⟩, hcylinder⟩ := Set.mem_iUnion.mp hsample
  have htail :=
    TerminalSkeletonInvariance.shiftSteps_mem_assembledTerminalWordCylinder_of_mem_assembleAfterPrefix
      hcylinder
  have hglobal := isOuterExitTime_assembled_marked_of_valid
    (by omega) hvalid visits bridges
  obtain ⟨horizon, omega, hexit, hx, hcode⟩ := hvalid
  subst code
  let words := markedBridgeWords bridges
  let erased := eraseMarkedTerminalBridges bridges
  have hwords : (fun j ↦ List.ofFn (erased j).1.2) = words := by
    change unmarkedBridgeWords erased = words
    exact (unmarkedBridgeWords_eraseMarkedTerminalBridges bridges).trans rfl
  have hsuccessful : SuccessfulPoint
      (trajectory (assembledTerminalPath
        (extractTerminalSkeletonCode scale horizon profileDelta x omega) words))
      scale (assembledTerminalHorizon
        (extractTerminalSkeletonCode scale horizon profileDelta x omega) words)
      profileDelta x := by
    have h :=
      successfulPoint_reconstructed_of_compressedBoundaryExitWordCodes_of_one_le
        hscale hexit hx erased
    dsimp only at h
    rw [hwords] at h
    rw [assembledTerminalPath_eq_reconstructedTerminalStepPath,
      assembledTerminalHorizon_eq_alternatingConcat_length,
      extractTerminalSkeletonCode_retainedPiece]
    exact h
  have hrawCode : extractTerminalSkeletonCode scale
      (assembledTerminalHorizon
        (extractTerminalSkeletonCode scale horizon profileDelta x omega) words)
      profileDelta x
      (assembledTerminalPath
        (extractTerminalSkeletonCode scale horizon profileDelta x omega) words) =
        extractTerminalSkeletonCode scale horizon profileDelta x omega := by
    have h :=
      extractTerminalSkeletonCode_reconstructed_of_compressedBoundaryExitWordCodes
        (by omega) hexit hx erased
    dsimp only at h
    rw [hwords] at h
    rw [assembledTerminalPath_eq_reconstructedTerminalStepPath,
      assembledTerminalHorizon_eq_alternatingConcat_length,
      extractTerminalSkeletonCode_retainedPiece]
    exact h
  have hvisits : terminalVisitVector
      (trajectory (assembledTerminalPath
        (extractTerminalSkeletonCode scale horizon profileDelta x omega) words))
      scale (assembledTerminalHorizon
        (extractTerminalSkeletonCode scale horizon profileDelta x omega) words)
      profileDelta x = visits := by
    have h :=
      terminalVisitVector_reconstructed_of_compressedBoundaryVisitExitWordCodes
        (by omega) hexit hx visits bridges
    rw [assembledTerminalPath_eq_reconstructedTerminalStepPath,
      assembledTerminalHorizon_eq_alternatingConcat_length,
      extractTerminalSkeletonCode_retainedPiece]
    exact h
  have hmarked : extractMarkedTerminalCode scale
      (assembledTerminalHorizon
        (extractTerminalSkeletonCode scale horizon profileDelta x omega) words)
      profileDelta x
      (assembledTerminalPath
        (extractTerminalSkeletonCode scale horizon profileDelta x omega) words) =
        ((extractTerminalSkeletonCode scale horizon profileDelta x omega).1,
          ((extractTerminalSkeletonCode scale horizon profileDelta x omega).2.1,
            ((extractTerminalSkeletonCode scale horizon profileDelta x omega).2.2,
              visits))) := by
    unfold extractMarkedTerminalCode
    rw [hrawCode, hvisits]
  have hcanonical :=
    stoppedSuccessfulAndMarkedCode_of_mem_assembledTerminalWordCylinder
      (by omega) hglobal hsuccessful hmarked htail
  unfold stoppedMarkedTerminalAtom
  apply Set.mem_iUnion.mpr
  refine ⟨assembledTerminalHorizon
    (extractTerminalSkeletonCode scale horizon profileDelta x omega) words, ?_⟩
  exact ⟨⟨hcanonical.1, hcanonical.2.1⟩, hcanonical.2.2⟩

/-- Exact fixed-visit marked event equality at every terminal scale. -/
theorem stoppedMarkedTerminalAtom_eq_markedTerminalInsertionEvent
    {start scale : ℕ} {profileDelta : ℝ} {x : Point}
    (hscale : 1 ≤ scale)
    (code : TerminalSkeletonCode
      (AppendixLocalTime.requiredTerminalCount scale profileDelta))
    (hvalid : ValidTerminalSkeleton scale profileDelta x code)
    (visits : Fin
      (AppendixLocalTime.requiredTerminalCount scale profileDelta) → ℕ) :
    stoppedMarkedTerminalAtom start scale profileDelta x
        (code.1, (code.2.1, (code.2.2, visits))) =
      markedTerminalInsertionEvent (start := start) (scale := scale)
        (x := x) code visits := by
  apply Set.Subset.antisymm
  · exact
      TerminalSkeletonFactorization.stoppedMarkedTerminalAtom_subset_markedTerminalInsertionEvent
        hscale (code.1, (code.2.1, (code.2.2, visits)))
  · exact markedTerminalInsertionEvent_subset_stoppedMarkedTerminalAtom
      hscale code hvalid visits

/-! ## Concrete complementary atoms for the stopped events -/

/-- The canonical unmarked complementary atom has exactly the genuine
horizon-collapsed stopped skeleton event. -/
theorem validUnmarkedComplementarySkeletonAtom_event_eq_stoppedTerminalSkeletonAtom
    {start scale : ℕ} {profileDelta : ℝ} {x : Point}
    (code : TerminalSkeletonCode
      (AppendixLocalTime.requiredTerminalCount scale profileDelta))
    (hscale : 1 ≤ scale)
    (hvalid : ValidTerminalSkeleton scale profileDelta x code) :
    (validUnmarkedComplementarySkeletonAtom (start := start)
      code hscale hvalid).event =
        stoppedTerminalSkeletonAtom start scale profileDelta x code := by
  rw [validUnmarkedComplementarySkeletonAtom_event]
  exact (stoppedTerminalSkeletonAtom_eq_unmarkedTerminalInsertionEvent
    hscale code hvalid).symm

/-- The canonical fixed-visit complementary atom has exactly the genuine
horizon-collapsed marked skeleton event. -/
theorem validMarkedComplementarySkeletonAtom_event_eq_stoppedMarkedTerminalAtom
    {start scale : ℕ} {profileDelta : ℝ} {x : Point}
    (code : TerminalSkeletonCode
      (AppendixLocalTime.requiredTerminalCount scale profileDelta))
    (hscale : 1 ≤ scale)
    (hvalid : ValidTerminalSkeleton scale profileDelta x code)
    (visits : Fin
      (AppendixLocalTime.requiredTerminalCount scale profileDelta) → ℕ) :
    (validMarkedComplementarySkeletonAtom (start := start)
      code hscale hvalid visits).event =
        stoppedMarkedTerminalAtom start scale profileDelta x
          (code.1, (code.2.1, (code.2.2, visits))) := by
  rw [validMarkedComplementarySkeletonAtom_event]
  exact (stoppedMarkedTerminalAtom_eq_markedTerminalInsertionEvent
    hscale code hvalid visits).symm

end

end Erdos1165.TerminalSkeletonInsertionInvariance
