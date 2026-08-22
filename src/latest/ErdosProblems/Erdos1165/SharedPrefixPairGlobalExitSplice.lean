/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/
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

import ErdosProblems.Erdos1165.SharedPrefixPairMergedSkeleton

/-!
# The first global exit for a merged two-point terminal splice

The two chronological terminal families use different local discs.  Their
union is nevertheless disjoint from the common global boundary, so the
finite-list splice invariant applies to every mixed replacement tuple.
-/

open Set

namespace Erdos1165.SharedPrefixPairGlobalExitSplice

open AppendixPair Hitting MarkedBridgeFactorization
open SharedPrefixPairMergedSkeleton TerminalExcursionPathwise
open TerminalGlobalExitSplice TerminalSkeletonInvariance TerminalSkeletonWords
open TerminalSequentialVisitLaw ThickPoint

noncomputable section

/-- Containment of every vertex is monotone in the containing set. -/
theorem wordWithin_mono {D E : Set Point} (hDE : D ⊆ E) :
    ∀ {a : Point} {word : List Direction}, WordWithin D a word → WordWithin E a word := by
  intro a word hword
  induction word generalizing a with
  | nil => exact hDE hword
  | cons d word ih => exact ⟨hDE hword.1, ih hword.2⟩

/-- Point alignment is preserved when two timed interval families are sorted
into one chronological skeleton. -/
theorem mergeTimedTerminalSkeleton_point_alignment
    {mLeft mRight : ℕ} (omega : StepPath)
    (left : TimedTerminalSkeleton mLeft)
    (right : TimedTerminalSkeleton mRight)
    (hleftEntrance : ∀ i,
      left.entrancePoint i = trajectory omega (left.entrance i))
    (hleftExit : ∀ i, left.exitPoint i = trajectory omega (left.exit i))
    (hrightEntrance : ∀ j,
      right.entrancePoint j = trajectory omega (right.entrance j))
    (hrightExit : ∀ j, right.exitPoint j = trajectory omega (right.exit j)) :
    (∀ k, (mergeTimedTerminalSkeleton left right).entrancePoint k =
        trajectory omega ((mergeTimedTerminalSkeleton left right).entrance k)) ∧
      (∀ k, (mergeTimedTerminalSkeleton left right).exitPoint k =
        trajectory omega ((mergeTimedTerminalSkeleton left right).exit k)) := by
  have hentrance : ∀ q,
      pairEntrancePoint left right q = trajectory omega (pairEntrance left right q) := by
    intro q
    obtain ⟨i | j, rfl⟩ := finSumFinEquiv.surjective q
    · simpa [pairEntrancePoint, pairEntrance, pairValue] using hleftEntrance i
    · simpa [pairEntrancePoint, pairEntrance, pairValue] using hrightEntrance j
  have hexit : ∀ q,
      pairExitPoint left right q = trajectory omega (pairExit left right q) := by
    intro q
    obtain ⟨i | j, rfl⟩ := finSumFinEquiv.surjective q
    · simpa [pairExitPoint, pairExit, pairValue] using hleftExit i
    · simpa [pairExitPoint, pairExit, pairValue] using hrightExit j
  constructor
  · intro k
    change pairEntrancePoint left right (chronologicalEquiv left right k) =
      trajectory omega (pairEntrance left right (chronologicalEquiv left right k))
    exact hentrance _
  · intro k
    change pairExitPoint left right (chronologicalEquiv left right k) =
      trajectory omega (pairExit left right (chronologicalEquiv left right k))
    exact hexit _

/-- Every mixed left/right tuple of endpoint-matched terminal words preserves
the first hit of the common global boundary.  The hypotheses are stated for
arbitrary already-aligned timed families, so the result also applies to
merged interval systems beyond the literal two-point extractor. -/
theorem assembledMergedPair_globalFirstAt
    {mLeft mRight scale : ℕ} {x y : Point} {omega : StepPath}
    (left : TimedTerminalSkeleton mLeft)
    (right : TimedTerminalSkeleton mRight)
    (hscale : 1 ≤ scale)
    (hxbox : x ∈ candidateBox scale) (hybox : y ∈ candidateBox scale)
    (hmerged : (mergeTimedTerminalSkeleton left right).WellFormed)
    (hexit : IsOuterExitTime (trajectory omega) scale left.horizon)
    (hpoints :
      (∀ k, (mergeTimedTerminalSkeleton left right).entrancePoint k =
        trajectory omega ((mergeTimedTerminalSkeleton left right).entrance k)) ∧
      (∀ k, (mergeTimedTerminalSkeleton left right).exitPoint k =
        trajectory omega ((mergeTimedTerminalSkeleton left right).exit k)))
    (hinner : ∀ q, pairEntrancePoint left right q ∈
      terminalInnerBoundary scale (logicalPairCenter x y q))
    (bridges : (q : Fin (mLeft + mRight)) →
      LogicalPairTerminalBridge scale x y left right q) :
    AbsoluteBoundaryFirstAt (discBoundary (0, 0) (outerScale scale)) (0, 0)
      (assembledTerminalPath
        (compressTimedSkeleton omega
          (mergeTimedTerminalSkeleton left right))
        (chronologicalPairBridgeWords bridges))
      (assembledTerminalHorizon
        (compressTimedSkeleton omega
          (mergeTimedTerminalSkeleton left right))
        (chronologicalPairBridgeWords bridges)) := by
  classical
  let merged := mergeTimedTerminalSkeleton left right
  let words := chronologicalPairBridgeWords bridges
  let D := disc x (scaleRadius scale scale) ∪ disc y (scaleRadius scale scale)
  have hdisjoint : ∀ z, z ∈ D →
      z ∉ discBoundary (0, 0) (outerScale scale) := by
    intro z hz
    rcases hz with hz | hz
    · exact terminalDisc_disjoint_globalBoundary hscale hxbox hz
    · exact terminalDisc_disjoint_globalBoundary hscale hybox hz
  have hwithin : ∀ k,
      WordWithin D (trajectory omega (merged.entrance k)) (words k) := by
    intro k
    let q := chronologicalEquiv left right k
    have hlocal := terminalBoundaryExitWordCode_wordWithin_of_innerDisc
      hscale (hinner q).1 (bridges q)
    rw [← hpoints.1 k]
    change WordWithin D (pairEntrancePoint left right q)
      (List.ofFn (bridges q).1.2)
    obtain ⟨i | j, hq⟩ := finSumFinEquiv.surjective q
    · refine wordWithin_mono (D :=
        disc (logicalPairCenter x y q) (scaleRadius scale scale))
          (E := D) ?_ hlocal
      intro z hz
      left
      simpa [logicalPairCenter, pairValue, ← hq] using hz
    · refine wordWithin_mono (D :=
        disc (logicalPairCenter x y q) (scaleRadius scale scale))
          (E := D) ?_ hlocal
      intro z hz
      right
      simpa [logicalPairCenter, pairValue, ← hq] using hz
  have hwordEnd : ∀ k,
      wordEndpoint (trajectory omega (merged.entrance k)) (words k) =
        trajectory omega (merged.exit k) := by
    intro k
    let q := chronologicalEquiv left right k
    rw [← hpoints.1 k, ← hpoints.2 k]
    change wordEndpoint (pairEntrancePoint left right q)
      (List.ofFn (bridges q).1.2) = pairExitPoint left right q
    exact boundaryExitWordCode_wordEndpoint (bridges q)
  have hsafe : AlternatingTerminalSpliceSafe
      (discBoundary (0, 0) (outerScale scale)) D
      (mLeft + mRight)
      (trajectory omega 0)
      (complementaryPieces
        (mLeft + mRight) omega 0 left.horizon
          merged.entrance merged.exit) words := by
    exact alternatingTerminalSpliceSafe_complementaryPieces
      (mLeft + mRight) omega 0 left.horizon merged.entrance merged.exit
      (discBoundary (0, 0) (outerScale scale)) D words
      (Nat.zero_le _) (orderedIntervals_of_wellFormed hmerged)
      hexit.1 hexit.2 hdisjoint hwithin hwordEnd
  have hfirstWord :=
    WordFirstHitsAtEnd.alternatingConcat_of_terminalSpliceSafe hdisjoint hsafe
  have houterWord : IsOuterExitTime
      (wordWalk (0, 0)
        (reconstructTerminalPacket
          (compressTimedSkeleton omega merged, words))) scale
      (assembledTerminalHorizon
        (compressTimedSkeleton omega merged) words) := by
    exact hfirstWord.isFirstHit
  have houter := isOuterExitTime_assembledTerminalPath_of_wordWalk houterWord
  have hzeroAdd : ∀ p : Point, (0, 0) + p = p := by
    rintro ⟨a, b⟩
    simp only [Prod.mk_add_mk, zero_add]
  simpa only [AbsoluteBoundaryFirstAt, IsOuterExitTime,
    PlanarPotential.trajectoryFrom, hzeroAdd] using houter

end

end Erdos1165.SharedPrefixPairGlobalExitSplice
