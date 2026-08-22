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

import ErdosProblems.Erdos1165.SharedPrefixPairGlobalExitSplice

/-!
# The concrete extracted two-point complementary atom

This downstream adapter instantiates the generic merged pair atom with the
two terminal skeletons extracted from one stopped walk.  Far separation
supplies cross-clock alignment, while the mixed-splice theorem supplies the
uniform global first-hit property.  Consequently the exported atom has no
remaining `hfirst` argument.
-/

open Set

namespace Erdos1165.SharedPrefixPairExtractedAtom

open AppendixPair Hitting MarkedBridgeFactorization
open SharedPrefixPairExtraction SharedPrefixPairFactorization
open SharedPrefixPairGlobalExitSplice SharedPrefixPairMergedSkeleton
open TerminalExcursionPathwise TerminalSequentialVisitLaw
open TerminalSkeletonInvariance TerminalSkeletonWords ThickPoint

noncomputable section

/-- The actual left/right first-boundary bridge family, kept behind a named
abbreviation so downstream signatures need not unfold both timed extractors. -/
abbrev ExtractedLogicalPairTerminalBridge
    (scale horizon : ℕ) (profileDelta : ℝ) (x y : Point)
    (omega : StepPath)
    (q : Fin (terminalCount scale profileDelta +
      terminalCount scale profileDelta)) :=
  LogicalPairTerminalBridge scale x y
    (extractTimedTerminalSkeleton scale horizon profileDelta x omega)
    (extractTimedTerminalSkeleton scale horizon profileDelta y omega) q

/-- The logical entrance endpoint of either extracted branch lies on that
branch's terminal inner boundary. -/
theorem extractedPair_entrance_mem
    {scale horizon : ℕ} {profileDelta : ℝ} {x y : Point}
    {omega : StepPath}
    (hscale : 1 ≤ scale)
    (hexit : IsOuterExitTime (trajectory omega) scale horizon)
    (hx : SuccessfulPoint (trajectory omega) scale horizon profileDelta x)
    (hy : SuccessfulPoint (trajectory omega) scale horizon profileDelta y) :
    ∀ q, pairEntrancePoint
        (extractTimedTerminalSkeleton scale horizon profileDelta x omega)
        (extractTimedTerminalSkeleton scale horizon profileDelta y omega) q ∈
      terminalInnerBoundary scale (logicalPairCenter x y q) := by
  intro q
  obtain ⟨i | j, hq⟩ := finSumFinEquiv.surjective q
  · rw [← hq]
    unfold pairEntrancePoint logicalPairCenter
    rw [finSumFinEquiv_apply_left, pairValue_castAdd, pairValue_castAdd]
    simpa [extractTimedTerminalSkeleton] using
      extractTerminalSkeletonCode_entrance_mem hscale hexit hx i
  · rw [← hq]
    unfold pairEntrancePoint logicalPairCenter
    rw [finSumFinEquiv_apply_right, pairValue_natAdd, pairValue_natAdd]
    simpa [extractTimedTerminalSkeleton] using
      extractTerminalSkeletonCode_entrance_mem hscale hexit hy j

/-- Point alignment for a merged timed pair, behind a named proposition to
keep extracted-atom signatures small. -/
def MergedPairPointAligned {mLeft mRight : ℕ} (omega : StepPath)
    (left : TimedTerminalSkeleton mLeft)
    (right : TimedTerminalSkeleton mRight) : Prop :=
  (∀ k, (mergeTimedTerminalSkeleton left right).entrancePoint k =
    trajectory omega ((mergeTimedTerminalSkeleton left right).entrance k)) ∧
  ∀ k, (mergeTimedTerminalSkeleton left right).exitPoint k =
    trajectory omega ((mergeTimedTerminalSkeleton left right).exit k)

/-- The two literal extracted timed skeletons satisfy merged point
alignment. -/
theorem extractedPair_pointAligned
    (scale horizon : ℕ) (profileDelta : ℝ) (x y : Point)
    (omega : StepPath) :
    MergedPairPointAligned omega
      (extractTimedTerminalSkeleton scale horizon profileDelta x omega)
      (extractTimedTerminalSkeleton scale horizon profileDelta y omega) := by
  unfold MergedPairPointAligned
  exact mergeTimedTerminalSkeleton_point_alignment omega
    (extractTimedTerminalSkeleton scale horizon profileDelta x omega)
    (extractTimedTerminalSkeleton scale horizon profileDelta y omega)
    (TerminalGlobalExitSplice.extractTimedTerminalSkeleton_entrancePoint_eq
      scale horizon profileDelta x omega)
    (TerminalGlobalExitSplice.extractTimedTerminalSkeleton_exitPoint_eq
      scale horizon profileDelta x omega)
    (TerminalGlobalExitSplice.extractTimedTerminalSkeleton_entrancePoint_eq
      scale horizon profileDelta y omega)
    (TerminalGlobalExitSplice.extractTimedTerminalSkeleton_exitPoint_eq
      scale horizon profileDelta y omega)

/-- Package the mixed global-exit splice theorem directly as a complementary
skeleton atom. -/
def logicalPairComplementarySkeletonAtom_of_splice
    {start mLeft mRight scale : ℕ} {x y : Point} {omega : StepPath}
    (left : TimedTerminalSkeleton mLeft)
    (right : TimedTerminalSkeleton mRight)
    (hscale : 1 ≤ scale)
    (hxbox : x ∈ candidateBox scale) (hybox : y ∈ candidateBox scale)
    (hmerged : (mergeTimedTerminalSkeleton left right).WellFormed)
    (hexit : IsOuterExitTime (trajectory omega) scale left.horizon)
    (hpoints : MergedPairPointAligned omega left right)
    (hinner : ∀ q, pairEntrancePoint left right q ∈
      terminalInnerBoundary scale (logicalPairCenter x y q)) :
    ComplementarySkeletonAtom (mLeft + mRight) (Fin start → Direction)
      (LogicalPairTerminalBridge scale x y left right) :=
  logicalPairComplementarySkeletonAtom omega left right
    (discBoundary (0, 0) (outerScale scale)) (0, 0)
    (assembledMergedPair_globalFirstAt left right hscale hxbox hybox
      hmerged hexit hpoints hinner)

/-- The actual unmarked two-point complementary atom.  Its only inputs are
the genuine geometric/stopped-success hypotheses; in particular it has no
user-supplied global-first-hit or probability premise. -/
def extractedLogicalPairComplementarySkeletonAtom
    {start scale horizon : ℕ} {profileDelta : ℝ} {x y : Point}
    {omega : StepPath}
    (hscale : 1 ≤ scale)
    (hlevel : separationLevel scale x y ≤ scale)
    (hexit : IsOuterExitTime (trajectory omega) scale horizon)
    (hx : SuccessfulPoint (trajectory omega) scale horizon profileDelta x)
    (hy : SuccessfulPoint (trajectory omega) scale horizon profileDelta y)
    (hxbox : x ∈ candidateBox scale) (hybox : y ∈ candidateBox scale) :
    ComplementarySkeletonAtom
      (terminalCount scale profileDelta + terminalCount scale profileDelta)
      (Fin start → Direction)
      (ExtractedLogicalPairTerminalBridge
        scale horizon profileDelta x y omega) :=
  logicalPairComplementarySkeletonAtom_of_splice
    (start := start)
    (extractTimedTerminalSkeleton scale horizon profileDelta x omega)
    (extractTimedTerminalSkeleton scale horizon profileDelta y omega)
    hscale hxbox hybox
    (extractMergedTimedTerminalSkeleton_wellFormed
      hscale hlevel hexit hx hy)
    hexit
    (extractedPair_pointAligned scale horizon profileDelta x y omega)
    (extractedPair_entrance_mem hscale hexit hx hy)

/-- Pair-factorization view of the concrete extracted atom.  Logical
coordinates split as left then right and the common retained word remains
unchanged. -/
def extractedLogicalPairSharedPrefixAtom
    {start scale horizon : ℕ} {profileDelta : ℝ} {x y : Point}
    {omega : StepPath}
    (hscale : 1 ≤ scale)
    (hlevel : separationLevel scale x y ≤ scale)
    (hexit : IsOuterExitTime (trajectory omega) scale horizon)
    (hx : SuccessfulPoint (trajectory omega) scale horizon profileDelta x)
    (hy : SuccessfulPoint (trajectory omega) scale horizon profileDelta y)
    (hxbox : x ∈ candidateBox scale) (hybox : y ∈ candidateBox scale) :=
  SharedPrefixPairAtom.ofComplementarySkeletonAtom
    (mLeft := terminalCount scale profileDelta)
    (mRight := terminalCount scale profileDelta)
    (extractedLogicalPairComplementarySkeletonAtom (start := start)
      hscale hlevel hexit hx hy hxbox hybox)

end

end Erdos1165.SharedPrefixPairExtractedAtom
