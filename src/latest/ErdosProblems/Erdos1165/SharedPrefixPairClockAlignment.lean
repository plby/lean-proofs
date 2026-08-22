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

import ErdosProblems.Erdos1165.SharedPrefixPairExtraction
import ErdosProblems.Erdos1165.TerminalExtractedBridgeCodes
import ErdosProblems.Erdos1165.TerminalGlobalExitSplice
import ErdosProblems.Erdos1165.TerminalSpliceProfileGeometry

/-!
# Cross-branch alignment of separated terminal clocks

For a far pair, the terminal outer discs are contained in the two discs at
the first separation level and hence are disjoint.  Each extracted terminal
word stays inside its own terminal outer disc until its recorded exit.  Two
left/right erased intervals therefore cannot overlap in time.  This closes
the cross-clock premise isolated in `SharedPrefixPairExtraction` without any
probabilistic input.
-/

open Set

namespace Erdos1165.SharedPrefixPairClockAlignment

open AppendixPair MarkedBridgeFactorization SharedPrefixPairExtraction
open TerminalExcursionPathwise TerminalExtractedBridgeCodes
open TerminalGlobalExitSplice TerminalSequentialVisitLaw
open TerminalSkeletonWords TerminalSpliceProfileGeometry ThickPoint

noncomputable section

/-- The terminal outer discs of a far pair are disjoint. -/
theorem terminalDiscs_disjoint_of_separationLevel_le
    {scale : ℕ} {x y : Point}
    (hlevel : separationLevel scale x y ≤ scale) :
    Disjoint (disc x (scaleRadius scale scale))
      (disc y (scaleRadius scale scale)) := by
  have hnonempty : (separatingIndices scale x y).Nonempty := by
    by_contra hempty
    have hsentinel : separationLevel scale x y = scale + 2 :=
      separationLevel_eq_sentinel_iff.mpr hempty
    omega
  have hseparated := separationLevel_isSeparated hnonempty
  have hradius : scaleRadius scale scale ≤
      scaleRadius scale (separationLevel scale x y) :=
    scaleRadius_antitone_of_le hlevel le_rfl
  apply hseparated.mono
  · intro z hz
    exact hz.trans hradius
  · intro z hz
    exact hz.trans hradius

/-- Every absolute time in one extracted terminal interval lies inside that
point's terminal outer disc. -/
theorem trajectory_mem_terminalDisc_of_mem_extractedInterval
    {scale horizon : ℕ} {profileDelta : ℝ} {x : Point}
    {omega : StepPath}
    (hscale : 1 ≤ scale)
    (hexit : IsOuterExitTime (trajectory omega) scale horizon)
    (hx : SuccessfulPoint (trajectory omega) scale horizon profileDelta x)
    (j : Fin (AppendixLocalTime.requiredTerminalCount scale profileDelta))
    {t : ℕ}
    (hstart : extractedEntrance (trajectory omega) scale horizon x j ≤ t)
    (hstop : t ≤ extractedExit (trajectory omega) scale horizon x j) :
    trajectory omega t ∈ disc x (scaleRadius scale scale) := by
  let timed := extractTimedTerminalSkeleton scale horizon profileDelta x omega
  let word := extractedTerminalStoppedWord scale horizon profileDelta x omega j
  have hwell : timed.WellFormed :=
    extractTimedTerminalSkeleton_wellFormed_of_stopped_success hscale hexit hx
  have hstartInner : timed.entrancePoint j ∈ terminalInnerBoundary scale x := by
    simpa [timed, extractTimedTerminalSkeleton] using
      extractTerminalSkeletonCode_entrance_mem hscale hexit hx j
  have hstartDisc : timed.entrancePoint j ∈
      disc x (scaleRadius scale scale) :=
    hstartInner.1.trans (terminalRadius_le_regularRadius_self scale hscale)
  have hfirst :=
    extractedTerminalStoppedWord_absoluteBoundaryFirstAt hscale hexit hx j
  have hfirstDisc : AbsoluteBoundaryFirstAt
      (innerBoundary (disc x (scaleRadius scale scale)))
      (timed.entrancePoint j) (extendStoppedWord word) word.1 := by
    simpa [timed, word, terminalOuterBoundary, discBoundary] using hfirst
  let q := t - timed.entrance j
  have hq : q ≤ word.1 := by
    change t - timed.entrance j ≤ timed.exit j - timed.entrance j
    exact Nat.sub_le_sub_right hstop (timed.entrance j)
  have hwithin := trajectoryFrom_mem_of_absoluteBoundaryFirstAt_innerBoundary
    hstartDisc hfirstDisc q hq
  have hwordmem : shiftSteps (timed.entrance j) omega ∈
      stoppedWordCylinder word := by
    rfl
  have hactual : PlanarPotential.trajectoryFrom (timed.entrancePoint j)
      (shiftSteps (timed.entrance j) omega) q =
      PlanarPotential.trajectoryFrom (timed.entrancePoint j)
        (extendStoppedWord word) q :=
    trajectoryFrom_eq_extendStoppedWord_of_mem hwordmem _ hq
  have hfresh : PlanarPotential.trajectoryFrom (timed.entrancePoint j)
      (shiftSteps (timed.entrance j) omega) q ∈
      disc x (scaleRadius scale scale) := by
    rw [hactual]
    exact hwithin
  have hadd : timed.entrance j + q = t := by
    dsimp only [q]
    exact Nat.add_sub_of_le hstart
  rw [show timed.entrancePoint j =
    trajectory omega (timed.entrance j) by rfl] at hfresh
  rw [trajectoryFrom_shiftSteps_eq, hadd] at hfresh
  exact hfresh

/-- At the actual first outer-exit horizon, separated terminal interval
families are cross-branch aligned. -/
theorem terminalPairClockAligned_of_separationLevel_le
    {scale horizon : ℕ} {profileDelta : ℝ} {x y : Point}
    {omega : StepPath}
    (hscale : 1 ≤ scale)
    (hlevel : separationLevel scale x y ≤ scale)
    (hexit : IsOuterExitTime (trajectory omega) scale horizon)
    (hx : SuccessfulPoint (trajectory omega) scale horizon profileDelta x)
    (hy : SuccessfulPoint (trajectory omega) scale horizon profileDelta y) :
    TerminalPairClockAligned (trajectory omega) scale horizon profileDelta x y := by
  intro i j
  by_contra hnot
  simp only [not_or, not_le] at hnot
  let t := max
    (extractedEntrance (trajectory omega) scale horizon x i)
    (extractedEntrance (trajectory omega) scale horizon y j)
  have htxStart : extractedEntrance (trajectory omega) scale horizon x i ≤ t :=
    le_max_left _ _
  have htyStart : extractedEntrance (trajectory omega) scale horizon y j ≤ t :=
    le_max_right _ _
  have htxStop : t ≤ extractedExit (trajectory omega) scale horizon x i := by
    apply max_le
    · exact extractedEntrance_le_extractedExit
        (trajectory omega) scale horizon x i
    · exact hnot.1.le
  have htyStop : t ≤ extractedExit (trajectory omega) scale horizon y j := by
    apply max_le
    · exact hnot.2.le
    · exact extractedEntrance_le_extractedExit
        (trajectory omega) scale horizon y j
  have hxin : trajectory omega t ∈ disc x (scaleRadius scale scale) :=
    trajectory_mem_terminalDisc_of_mem_extractedInterval
      hscale hexit hx i htxStart htxStop
  have hyin : trajectory omega t ∈ disc y (scaleRadius scale scale) :=
    trajectory_mem_terminalDisc_of_mem_extractedInterval
      hscale hexit hy j htyStart htyStop
  exact Set.disjoint_left.mp
    (terminalDiscs_disjoint_of_separationLevel_le hlevel) hxin hyin

end

end Erdos1165.SharedPrefixPairClockAlignment
