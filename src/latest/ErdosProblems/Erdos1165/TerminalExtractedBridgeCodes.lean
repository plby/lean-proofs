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

import ErdosProblems.Erdos1165.TerminalSkeletonWords
import ErdosProblems.Erdos1165.MarkedBridgeFactorization

/-!
# Canonical bridge codes carried by extracted terminal segments

Every complete terminal inner-to-outer segment of a stopped successful path
has a literal finite increment word.  This file packages that word as both
the unmarked and visit-marked canonical first-boundary codes.  The underlying
word is exactly the corresponding coordinate of `intervalWords`.
-/

namespace Erdos1165.TerminalExtractedBridgeCodes

open ThickPoint TerminalExcursionPathwise TerminalSkeletonWords
open TerminalSequentialVisitLaw MarkedBridgeFactorization
open TerminalExcursionBridge BoundaryVisitRegeneration

noncomputable section

/-- The stopped word formed from the literal shifted prefix of one extracted
terminal segment. -/
def extractedTerminalStoppedWord
    (scale horizon : ℕ) (profileDelta : ℝ) (x : Point)
    (omega : StepPath)
    (j : Fin (AppendixLocalTime.requiredTerminalCount scale profileDelta)) :
    StoppedWord :=
  let t := extractTimedTerminalSkeleton scale horizon profileDelta x omega
  ⟨t.exit j - t.entrance j,
    stepPrefix (t.exit j - t.entrance j) (shiftSteps (t.entrance j) omega)⟩

@[simp] theorem extractedTerminalStoppedWord_length
    (scale horizon : ℕ) (profileDelta : ℝ) (x : Point)
    (omega : StepPath)
    (j : Fin (AppendixLocalTime.requiredTerminalCount scale profileDelta)) :
    (extractedTerminalStoppedWord scale horizon profileDelta x omega j).1 =
      (extractTimedTerminalSkeleton scale horizon profileDelta x omega).exit j -
        (extractTimedTerminalSkeleton scale horizon profileDelta x omega).entrance j :=
  rfl

/-- Erasing the stopped-word wrapper gives precisely the segment word removed
by the terminal skeleton extraction. -/
theorem extractedTerminalStoppedWord_erased
    (scale horizon : ℕ) (profileDelta : ℝ) (x : Point)
    (omega : StepPath)
    (j : Fin (AppendixLocalTime.requiredTerminalCount scale profileDelta)) :
    List.ofFn
        (extractedTerminalStoppedWord scale horizon profileDelta x omega j).2 =
      intervalWords omega
        (extractTimedTerminalSkeleton scale horizon profileDelta x omega).entrance
        (extractTimedTerminalSkeleton scale horizon profileDelta x omega).exit j := by
  rfl

private theorem extractedTerminalShift_absoluteBoundaryFirstAt
    {scale horizon : ℕ} {profileDelta : ℝ} {x : Point}
    {omega : StepPath}
    (hscale : 1 ≤ scale)
    (hexit : IsOuterExitTime (trajectory omega) scale horizon)
    (hx : SuccessfulPoint (trajectory omega) scale horizon profileDelta x)
    (j : Fin (AppendixLocalTime.requiredTerminalCount scale profileDelta)) :
    let t := extractTimedTerminalSkeleton scale horizon profileDelta x omega
    AbsoluteBoundaryFirstAt (terminalOuterBoundary scale x)
      (t.entrancePoint j) (shiftSteps (t.entrance j) omega)
      (t.exit j - t.entrance j) := by
  classical
  dsimp only
  let t := extractTimedTerminalSkeleton scale horizon profileDelta x omega
  have ht : t.WellFormed :=
    extractTimedTerminalSkeleton_wellFormed_of_stopped_success hscale hexit hx
  have hcomplete : excursionStart (trajectory omega)
      (terminalOuterBoundary scale x) (terminalInnerBoundary scale x)
      horizon ((j : ℕ) + 1) ≤ horizon := by
    simpa [t, extractTimedTerminalSkeleton, extractedExit,
      terminalSegmentExitTime] using (ht.1 j).2
  have hentrance : terminalEntranceTime zeroClock
      (terminalOuterBoundary scale x) (terminalInnerBoundary scale x) j omega =
      t.entrance j := by
    simpa [t, extractTimedTerminalSkeleton, extractedEntrance] using
      terminalEntranceTime_eq_excursionFinish omega
        (terminalOuterBoundary scale x) (terminalInnerBoundary scale x)
        horizon j hcomplete
  have hexitTime : terminalExitTime zeroClock
      (terminalOuterBoundary scale x) (terminalInnerBoundary scale x) j omega =
      t.exit j := by
    simpa [t, extractTimedTerminalSkeleton, extractedExit,
      terminalSegmentExitTime] using
      terminalExitTime_eq_excursionStart omega
        (terminalOuterBoundary scale x) (terminalInnerBoundary scale x)
        horizon j hcomplete
  have hfirstEq : firstHitSetAfter
      (terminalEntranceTime zeroClock
        (terminalOuterBoundary scale x) (terminalInnerBoundary scale x) j)
      (terminalOuterBoundary scale x) omega = t.exit j := by
    rw [← terminalExitTime_eq_firstHitSetAfter
      (terminalOuterBoundary scale x) (terminalInnerBoundary scale x) j]
    exact hexitTime
  have hfirst := absoluteBoundaryFirstAt_post_firstHitSetAfter
    hentrance hfirstEq
  have hpost : postWithTopStoppingSteps
      (terminalEntranceTime zeroClock
        (terminalOuterBoundary scale x) (terminalInnerBoundary scale x) j) omega =
      shiftSteps (t.entrance j) omega :=
    postWithTopStoppingSteps_eq_shiftSteps_of_eq hentrance
  have hpos : stoppedPosition
      (terminalEntranceTime zeroClock
        (terminalOuterBoundary scale x) (terminalInnerBoundary scale x) j) omega =
      trajectory omega (t.entrance j) := stoppedPosition_eq_of_eq hentrance
  rw [hpost, hpos] at hfirst
  simpa [t, extractTimedTerminalSkeleton] using hfirst

/-- The literal extracted word first hits the terminal outer boundary exactly
at its last vertex. -/
theorem extractedTerminalStoppedWord_absoluteBoundaryFirstAt
    {scale horizon : ℕ} {profileDelta : ℝ} {x : Point}
    {omega : StepPath}
    (hscale : 1 ≤ scale)
    (hexit : IsOuterExitTime (trajectory omega) scale horizon)
    (hx : SuccessfulPoint (trajectory omega) scale horizon profileDelta x)
    (j : Fin (AppendixLocalTime.requiredTerminalCount scale profileDelta)) :
    let t := extractTimedTerminalSkeleton scale horizon profileDelta x omega
    let w := extractedTerminalStoppedWord scale horizon profileDelta x omega j
    AbsoluteBoundaryFirstAt (terminalOuterBoundary scale x)
      (t.entrancePoint j) (extendStoppedWord w) w.1 := by
  classical
  dsimp only
  let t := extractTimedTerminalSkeleton scale horizon profileDelta x omega
  let w := extractedTerminalStoppedWord scale horizon profileDelta x omega j
  have hmem : shiftSteps (t.entrance j) omega ∈ stoppedWordCylinder w := by
    rfl
  have hfirst := extractedTerminalShift_absoluteBoundaryFirstAt
    hscale hexit hx j
  constructor
  · rw [← trajectoryFrom_eq_extendStoppedWord_of_mem hmem
      (t.entrancePoint j) le_rfl]
    exact hfirst.1
  · intro q hq
    rw [← trajectoryFrom_eq_extendStoppedWord_of_mem hmem
      (t.entrancePoint j) hq.le]
    exact hfirst.2 q hq

/-- The terminal stopped word ends at the endpoint recorded by extraction. -/
theorem extractedTerminalStoppedWord_endpoint
    {scale horizon : ℕ} {profileDelta : ℝ} {x : Point}
    {omega : StepPath}
    (hscale : 1 ≤ scale)
    (hexit : IsOuterExitTime (trajectory omega) scale horizon)
    (hx : SuccessfulPoint (trajectory omega) scale horizon profileDelta x)
    (j : Fin (AppendixLocalTime.requiredTerminalCount scale profileDelta)) :
    let t := extractTimedTerminalSkeleton scale horizon profileDelta x omega
    let w := extractedTerminalStoppedWord scale horizon profileDelta x omega j
    PlanarPotential.trajectoryFrom (t.entrancePoint j)
      (extendStoppedWord w) w.1 = t.exitPoint j := by
  classical
  dsimp only
  let t := extractTimedTerminalSkeleton scale horizon profileDelta x omega
  let w := extractedTerminalStoppedWord scale horizon profileDelta x omega j
  have ht : t.WellFormed :=
    extractTimedTerminalSkeleton_wellFormed_of_stopped_success hscale hexit hx
  have hmem : shiftSteps (t.entrance j) omega ∈ stoppedWordCylinder w := by
    rfl
  rw [← trajectoryFrom_eq_extendStoppedWord_of_mem hmem
    (t.entrancePoint j) le_rfl]
  rw [show t.entrancePoint j = trajectory omega (t.entrance j) by rfl]
  rw [trajectoryFrom_shiftSteps_eq]
  change trajectory omega
      (t.entrance j + (t.exit j - t.entrance j)) = t.exitPoint j
  rw [Nat.add_sub_of_le (ht.1 j).1]
  rfl

/-- The literal target-visit count of an extracted terminal word is its
coordinate in the canonical terminal visit vector. -/
theorem extractedTerminalStoppedWord_visitCount
    {scale horizon : ℕ} {profileDelta : ℝ} {x : Point}
    {omega : StepPath}
    (hscale : 1 ≤ scale)
    (hexit : IsOuterExitTime (trajectory omega) scale horizon)
    (hx : SuccessfulPoint (trajectory omega) scale horizon profileDelta x)
    (j : Fin (AppendixLocalTime.requiredTerminalCount scale profileDelta)) :
    let t := extractTimedTerminalSkeleton scale horizon profileDelta x omega
    let w := extractedTerminalStoppedWord scale horizon profileDelta x omega j
    targetVisitSum (t.entrancePoint j) x (extendStoppedWord w) w.1 =
      terminalVisitVector (trajectory omega) scale horizon profileDelta x j := by
  classical
  dsimp only
  let t := extractTimedTerminalSkeleton scale horizon profileDelta x omega
  let w := extractedTerminalStoppedWord scale horizon profileDelta x omega j
  have ht : t.WellFormed :=
    extractTimedTerminalSkeleton_wellFormed_of_stopped_success hscale hexit hx
  have hmem : shiftSteps (t.entrance j) omega ∈ stoppedWordCylinder w := by
    rfl
  rw [← targetVisitSum_eq_extendStoppedWord_of_mem hmem
    (t.entrancePoint j) x]
  rw [show t.entrancePoint j = trajectory omega (t.entrance j) by rfl]
  change targetVisitSum (trajectory omega (t.entrance j)) x
      (shiftSteps (t.entrance j) omega) (t.exit j - t.entrance j) = _
  have hcount := targetVisitSum_shift_eq_Ico_card omega x (ht.1 j).1
  rw [hcount]
  rfl

/-! ## Canonical unmarked and marked codes -/

/-- The canonical unmarked first-outer-hit code carried by one actual
extracted terminal segment. -/
def extractedTerminalBoundaryExitWordCode
    {scale horizon : ℕ} {profileDelta : ℝ} {x : Point}
    {omega : StepPath}
    (hscale : 1 ≤ scale)
    (hexit : IsOuterExitTime (trajectory omega) scale horizon)
    (hx : SuccessfulPoint (trajectory omega) scale horizon profileDelta x)
    (j : Fin (AppendixLocalTime.requiredTerminalCount scale profileDelta)) :
    BoundaryExitWordCode (terminalOuterBoundary scale x)
      ((extractTerminalSkeletonCode scale horizon profileDelta x omega).2.1 j)
      ((extractTerminalSkeletonCode scale horizon profileDelta x omega).2.2 j) := by
  refine ⟨extractedTerminalStoppedWord scale horizon profileDelta x omega j,
    ?_, ?_⟩
  · simpa [extractTerminalSkeletonCode] using
      extractedTerminalStoppedWord_absoluteBoundaryFirstAt hscale hexit hx j
  · simpa [extractTerminalSkeletonCode] using
      extractedTerminalStoppedWord_endpoint hscale hexit hx j

/-- The canonical target-visit-marked first-outer-hit code carried by one
actual extracted terminal segment. -/
def extractedTerminalBoundaryVisitExitWordCode
    {scale horizon : ℕ} {profileDelta : ℝ} {x : Point}
    {omega : StepPath}
    (hscale : 1 ≤ scale)
    (hexit : IsOuterExitTime (trajectory omega) scale horizon)
    (hx : SuccessfulPoint (trajectory omega) scale horizon profileDelta x)
    (j : Fin (AppendixLocalTime.requiredTerminalCount scale profileDelta)) :
    BoundaryVisitExitWordCode (terminalOuterBoundary scale x) x
      ((extractTerminalSkeletonCode scale horizon profileDelta x omega).2.1 j)
      (terminalVisitVector (trajectory omega) scale horizon profileDelta x j)
      ((extractTerminalSkeletonCode scale horizon profileDelta x omega).2.2 j) := by
  refine ⟨extractedTerminalStoppedWord scale horizon profileDelta x omega j,
    ?_, ?_, ?_⟩
  · simpa [extractTerminalSkeletonCode] using
      extractedTerminalStoppedWord_absoluteBoundaryFirstAt hscale hexit hx j
  · simpa [extractTerminalSkeletonCode] using
      extractedTerminalStoppedWord_visitCount hscale hexit hx j
  · simpa [extractTerminalSkeletonCode] using
      extractedTerminalStoppedWord_endpoint hscale hexit hx j

@[simp] theorem extractedTerminalBoundaryExitWordCode_word
    {scale horizon : ℕ} {profileDelta : ℝ} {x : Point}
    {omega : StepPath}
    (hscale : 1 ≤ scale)
    (hexit : IsOuterExitTime (trajectory omega) scale horizon)
    (hx : SuccessfulPoint (trajectory omega) scale horizon profileDelta x)
    (j : Fin (AppendixLocalTime.requiredTerminalCount scale profileDelta)) :
    (extractedTerminalBoundaryExitWordCode hscale hexit hx j).1 =
      extractedTerminalStoppedWord scale horizon profileDelta x omega j := by
  rfl

@[simp] theorem extractedTerminalBoundaryVisitExitWordCode_word
    {scale horizon : ℕ} {profileDelta : ℝ} {x : Point}
    {omega : StepPath}
    (hscale : 1 ≤ scale)
    (hexit : IsOuterExitTime (trajectory omega) scale horizon)
    (hx : SuccessfulPoint (trajectory omega) scale horizon profileDelta x)
    (j : Fin (AppendixLocalTime.requiredTerminalCount scale profileDelta)) :
    (extractedTerminalBoundaryVisitExitWordCode hscale hexit hx j).1 =
      extractedTerminalStoppedWord scale horizon profileDelta x omega j := by
  rfl

theorem extractedTerminalBoundaryExitWordCode_erased
    {scale horizon : ℕ} {profileDelta : ℝ} {x : Point}
    {omega : StepPath}
    (hscale : 1 ≤ scale)
    (hexit : IsOuterExitTime (trajectory omega) scale horizon)
    (hx : SuccessfulPoint (trajectory omega) scale horizon profileDelta x)
    (j : Fin (AppendixLocalTime.requiredTerminalCount scale profileDelta)) :
    List.ofFn (extractedTerminalBoundaryExitWordCode hscale hexit hx j).1.2 =
      intervalWords omega
        (extractTimedTerminalSkeleton scale horizon profileDelta x omega).entrance
        (extractTimedTerminalSkeleton scale horizon profileDelta x omega).exit j := by
  rw [extractedTerminalBoundaryExitWordCode_word]
  exact extractedTerminalStoppedWord_erased
    scale horizon profileDelta x omega j

theorem extractedTerminalBoundaryVisitExitWordCode_erased
    {scale horizon : ℕ} {profileDelta : ℝ} {x : Point}
    {omega : StepPath}
    (hscale : 1 ≤ scale)
    (hexit : IsOuterExitTime (trajectory omega) scale horizon)
    (hx : SuccessfulPoint (trajectory omega) scale horizon profileDelta x)
    (j : Fin (AppendixLocalTime.requiredTerminalCount scale profileDelta)) :
    List.ofFn
        (extractedTerminalBoundaryVisitExitWordCode hscale hexit hx j).1.2 =
      intervalWords omega
        (extractTimedTerminalSkeleton scale horizon profileDelta x omega).entrance
        (extractTimedTerminalSkeleton scale horizon profileDelta x omega).exit j := by
  rw [extractedTerminalBoundaryVisitExitWordCode_word]
  exact extractedTerminalStoppedWord_erased
    scale horizon profileDelta x omega j

theorem extractedTerminalBoundaryVisitExitWordCode_visitCount
    {scale horizon : ℕ} {profileDelta : ℝ} {x : Point}
    {omega : StepPath}
    (hscale : 1 ≤ scale)
    (hexit : IsOuterExitTime (trajectory omega) scale horizon)
    (hx : SuccessfulPoint (trajectory omega) scale horizon profileDelta x)
    (j : Fin (AppendixLocalTime.requiredTerminalCount scale profileDelta)) :
    targetVisitSum
        ((extractTerminalSkeletonCode scale horizon profileDelta x omega).2.1 j) x
        (extendStoppedWord
          (extractedTerminalBoundaryVisitExitWordCode hscale hexit hx j).1)
        (extractedTerminalBoundaryVisitExitWordCode hscale hexit hx j).1.1 =
      terminalVisitVector (trajectory omega) scale horizon profileDelta x j :=
  (extractedTerminalBoundaryVisitExitWordCode hscale hexit hx j).2.2.1

end


end Erdos1165.TerminalExtractedBridgeCodes
