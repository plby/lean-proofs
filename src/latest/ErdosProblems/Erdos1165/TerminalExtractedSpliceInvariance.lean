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
import ErdosProblems.Erdos1165.TerminalProfileClockEquivalence

/-!
# Extracted terminal-splice invariants

This file packages the pathwise splice theorems in the endpoint language of
the compressed terminal skeleton.  The endpoint transports are kept behind
small definitions so insertion-event callers retain the literal finite-word
family in their statements.
-/

namespace Erdos1165.TerminalExtractedSpliceInvariance

open ThickPoint TerminalExcursionPathwise TerminalSkeletonWords
open TerminalVisitSpliceInvariance TerminalClockSplice
open TerminalExtractedClockSplice TerminalProfileClockEquivalence
open TerminalPacketEndpointAlignment TerminalGlobalExitSplice
open MarkedBridgeFactorization TerminalSequentialVisitLaw

noncomputable section

/-! ## Whole excursion profile and successful-point status -/

/-- Whole-profile invariance after first changing the displayed endpoint
indices of the bridge family. -/
theorem excursionProfile_reconstructed_of_transportedCompressedWords
    {scale horizon : ℕ} {profileDelta : ℝ} {x : Point}
    {omega : StepPath}
    (hscale : 2 ≤ scale)
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
    excursionProfile (trajectory omega) scale horizon x =
      excursionProfile
        (trajectory (reconstructedTerminalStepPath pieces words)) scale
        (alternatingConcat m pieces words).length x := by
  exact excursionProfile_reconstructed_of_boundaryExitWordCodes
    hscale hexit hx
      (fun j ↦ boundaryExitWordCodeOfCompressedEndpoints (bridges j))

/-- Compressed-endpoint form used by unmarked insertion events.  Its
reconstructed path uses the literal words carried by the input bridges. -/
theorem excursionProfile_reconstructed_of_compressedBoundaryExitWordCodes
    {scale horizon : ℕ} {profileDelta : ℝ} {x : Point}
    {omega : StepPath}
    (hscale : 2 ≤ scale)
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
    excursionProfile (trajectory omega) scale horizon x =
      excursionProfile
        (trajectory (reconstructedTerminalStepPath pieces words)) scale
        (alternatingConcat m pieces words).length x := by
  have h := excursionProfile_reconstructed_of_transportedCompressedWords
    hscale hexit hx bridges
  rw [timedWordsOfCompressedBoundaryExitWordCodes_eq] at h
  exact h

/-- Successful-point status is preserved by the same compressed-endpoint
terminal splice. -/
theorem successfulPoint_reconstructed_of_compressedBoundaryExitWordCodes
    {scale horizon : ℕ} {profileDelta : ℝ} {x : Point}
    {omega : StepPath}
    (hscale : 2 ≤ scale)
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
    SuccessfulPoint
      (trajectory (reconstructedTerminalStepPath pieces words)) scale
      newHorizon profileDelta x := by
  have hprofile :=
    excursionProfile_reconstructed_of_compressedBoundaryExitWordCodes
      hscale hexit hx bridges
  exact (successfulPoint_iff_of_excursionProfile_eq hprofile).mp hx

/-! ## Degenerate one-scale packet -/

/-- An empty extracted packet reconstructs the original finite prefix, so
its whole excursion profile is unchanged without any boundary-separation
assumption. -/
theorem excursionProfile_reconstructed_of_compressedBoundaryExitWordCodes_of_count_eq_zero
    {scale horizon : ℕ} {profileDelta : ℝ} {x : Point}
    {omega : StepPath}
    (hscale : 1 ≤ scale)
    (hexit : IsOuterExitTime (trajectory omega) scale horizon)
    (hx : SuccessfulPoint (trajectory omega) scale horizon profileDelta x)
    (hm0 : AppendixLocalTime.requiredTerminalCount scale profileDelta = 0)
    (bridges : ∀ j : Fin
      (AppendixLocalTime.requiredTerminalCount scale profileDelta),
      BoundaryExitWordCode (terminalOuterBoundary scale x)
        ((extractTerminalSkeletonCode scale horizon profileDelta x omega).2.1 j)
        ((extractTerminalSkeletonCode scale horizon profileDelta x omega).2.2 j)) :
    let m := AppendixLocalTime.requiredTerminalCount scale profileDelta
    let t := extractTimedTerminalSkeleton scale horizon profileDelta x omega
    let pieces := complementaryPieces m omega 0 horizon t.entrance t.exit
    let words : TerminalSegmentWords m := fun j ↦ List.ofFn (bridges j).1.2
    excursionProfile (trajectory omega) scale horizon x =
      excursionProfile
        (trajectory (reconstructedTerminalStepPath pieces words)) scale
        (alternatingConcat m pieces words).length x := by
  classical
  dsimp only
  let m := AppendixLocalTime.requiredTerminalCount scale profileDelta
  let t := extractTimedTerminalSkeleton scale horizon profileDelta x omega
  let pieces := complementaryPieces m omega 0 horizon t.entrance t.exit
  let leftWords := intervalWords omega t.entrance t.exit
  have hwords :
      (fun j ↦ List.ofFn (bridges j).1.2) = leftWords := by
    funext j
    have hj : False := by
      have := j.isLt
      omega
    exact hj.elim
  rw [hwords]
  have ht : t.WellFormed :=
    extractTimedTerminalSkeleton_wellFormed_of_stopped_success hscale hexit hx
  have hfull : alternatingConcat m pieces leftWords =
      incrementSlice omega 0 horizon := by
    exact alternatingConcat_complementaryPieces m omega 0 horizon
      t.entrance t.exit (orderedIntervals_of_wellFormed ht)
  have hpath : reconstructedTerminalStepPath pieces leftWords =
      extendStoppedWord (stoppedWordOfList (incrementSlice omega 0 horizon)) := by
    unfold reconstructedTerminalStepPath
    rw [hfull]
  rw [hpath]
  rw [hfull]
  simp only [incrementSlice_length, Nat.sub_zero]
  apply Proposition13Measurability.excursionProfile_congr_prefix
  intro q hq
  symm
  rw [show trajectory
      (extendStoppedWord (stoppedWordOfList (incrementSlice omega 0 horizon))) q =
      PlanarPotential.trajectoryFrom (0, 0)
        (extendStoppedWord (stoppedWordOfList (incrementSlice omega 0 horizon))) q by
    simp [PlanarPotential.trajectoryFrom]]
  rw [← TerminalProfileClockEquivalence.wordWalk_eq_trajectoryFrom_extendStoppedWord
    (0, 0) (incrementSlice omega 0 horizon) (by simpa using hq)]
  simpa [TerminalGlobalExitSplice.wordWalk] using
    wordPosition_incrementSlice omega (Nat.zero_le horizon) hq

/-- Whole-profile invariance at every positive scale.  At scale one the
selected terminal packet is empty; all larger scales use the separated
profile-boundary theorem. -/
theorem excursionProfile_reconstructed_of_compressedBoundaryExitWordCodes_of_one_le
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
    excursionProfile (trajectory omega) scale horizon x =
      excursionProfile
        (trajectory (reconstructedTerminalStepPath pieces words)) scale
        (alternatingConcat m pieces words).length x := by
  by_cases htwo : 2 ≤ scale
  · exact excursionProfile_reconstructed_of_compressedBoundaryExitWordCodes
      htwo hexit hx bridges
  · have hscaleEq : scale = 1 := by omega
    have hm0 : AppendixLocalTime.requiredTerminalCount scale profileDelta = 0 := by
      subst scale
      simp [AppendixLocalTime.requiredTerminalCount, terminalLower]
    exact
      excursionProfile_reconstructed_of_compressedBoundaryExitWordCodes_of_count_eq_zero
        hscale hexit hx hm0 bridges

/-- Successful-point preservation at every positive scale. -/
theorem successfulPoint_reconstructed_of_compressedBoundaryExitWordCodes_of_one_le
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
    SuccessfulPoint
      (trajectory (reconstructedTerminalStepPath pieces words)) scale
      newHorizon profileDelta x := by
  have hprofile :=
    excursionProfile_reconstructed_of_compressedBoundaryExitWordCodes_of_one_le
      hscale hexit hx bridges
  exact (successfulPoint_iff_of_excursionProfile_eq hprofile).mp hx

end

end Erdos1165.TerminalExtractedSpliceInvariance
