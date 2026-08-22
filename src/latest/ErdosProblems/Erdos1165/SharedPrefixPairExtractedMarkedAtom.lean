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

import ErdosProblems.Erdos1165.SharedPrefixPairExtractedAtom
import ErdosProblems.Erdos1165.TerminalMarkedSkeletonMass

/-!
# Marking the concrete extracted two-point complementary atom

This file restricts every logical bridge of the extracted pair atom to the
canonical first-boundary words having a prescribed number of visits to the
corresponding centre.  Forgetting the visit certificate is injective, so the
marked atom inherits the unmarked atom's prefix-free chronological assembly.
In particular, the common retained word is unchanged and still occurs once.
-/

open MeasureTheory Set
open scoped BigOperators ENNReal

namespace Erdos1165.SharedPrefixPairExtractedMarkedAtom

open AppendixPair Hitting MarkedBoundaryVisitKernel MarkedBridgeFactorization
open SharedPrefixPairExtraction SharedPrefixPairFactorization
open SharedPrefixPairExtractedAtom SharedPrefixPairMergedSkeleton
open TerminalExcursionPathwise TerminalMarkedSkeletonMass
open TerminalSequentialVisitLaw TerminalSkeletonInvariance
open TerminalSkeletonWords ThickPoint

noncomputable section

/-- Combine prescribed left and right visit vectors while retaining logical
left-then-right coordinates. -/
def logicalPairVisitVector {mLeft mRight : ℕ}
    (leftVisits : Fin mLeft → ℕ) (rightVisits : Fin mRight → ℕ) :
    Fin (mLeft + mRight) → ℕ :=
  Fin.addCases leftVisits rightVisits

@[simp] theorem logicalPairVisitVector_castAdd
    {mLeft mRight : ℕ} (leftVisits : Fin mLeft → ℕ)
    (rightVisits : Fin mRight → ℕ) (i : Fin mLeft) :
    logicalPairVisitVector leftVisits rightVisits (Fin.castAdd mRight i) =
      leftVisits i := by
  simp [logicalPairVisitVector]

@[simp] theorem logicalPairVisitVector_natAdd
    {mLeft mRight : ℕ} (leftVisits : Fin mLeft → ℕ)
    (rightVisits : Fin mRight → ℕ) (j : Fin mRight) :
    logicalPairVisitVector leftVisits rightVisits (Fin.natAdd mLeft j) =
      rightVisits j := by
  simp [logicalPairVisitVector]

/-- The canonical visit-certified bridge at a logical coordinate of the two
literal extracted terminal skeletons. -/
abbrev ExtractedLogicalPairMarkedTerminalBridge
    (scale horizon : ℕ) (profileDelta : ℝ) (x y : Point)
    (omega : StepPath)
    (leftVisits rightVisits : Fin (terminalCount scale profileDelta) → ℕ)
    (q : Fin (terminalCount scale profileDelta +
      terminalCount scale profileDelta)) :=
  BoundaryVisitExitWordCode
    (terminalOuterBoundary scale (logicalPairCenter x y q))
    (logicalPairCenter x y q)
    (pairEntrancePoint
      (extractTimedTerminalSkeleton scale horizon profileDelta x omega)
      (extractTimedTerminalSkeleton scale horizon profileDelta y omega) q)
    (logicalPairVisitVector leftVisits rightVisits q)
    (pairExitPoint
      (extractTimedTerminalSkeleton scale horizon profileDelta x omega)
      (extractTimedTerminalSkeleton scale horizon profileDelta y omega) q)

/-- Forget the visit-count certificate of one marked logical bridge. -/
def eraseExtractedLogicalPairMarkedTerminalBridge
    {scale horizon : ℕ} {profileDelta : ℝ} {x y : Point}
    {omega : StepPath}
    {leftVisits rightVisits : Fin (terminalCount scale profileDelta) → ℕ}
    {q : Fin (terminalCount scale profileDelta +
      terminalCount scale profileDelta)}
    (bridge : ExtractedLogicalPairMarkedTerminalBridge scale horizon
      profileDelta x y omega leftVisits rightVisits q) :
    ExtractedLogicalPairTerminalBridge scale horizon profileDelta x y omega q :=
  ⟨bridge.1, bridge.2.1, bridge.2.2.2⟩

@[simp] theorem eraseExtractedLogicalPairMarkedTerminalBridge_word
    {scale horizon : ℕ} {profileDelta : ℝ} {x y : Point}
    {omega : StepPath}
    {leftVisits rightVisits : Fin (terminalCount scale profileDelta) → ℕ}
    {q : Fin (terminalCount scale profileDelta +
      terminalCount scale profileDelta)}
    (bridge : ExtractedLogicalPairMarkedTerminalBridge scale horizon
      profileDelta x y omega leftVisits rightVisits q) :
    (eraseExtractedLogicalPairMarkedTerminalBridge bridge).1 = bridge.1 := rfl

/-- Erase every marked coordinate, leaving the shared retained code
unchanged. -/
def eraseExtractedLogicalPairMarkedCode
    {start scale horizon : ℕ} {profileDelta : ℝ} {x y : Point}
    {omega : StepPath}
    {leftVisits rightVisits : Fin (terminalCount scale profileDelta) → ℕ} :
    (Fin start → Direction) ×
        ((q : Fin (terminalCount scale profileDelta +
          terminalCount scale profileDelta)) →
          ExtractedLogicalPairMarkedTerminalBridge scale horizon
            profileDelta x y omega leftVisits rightVisits q) →
      (Fin start → Direction) ×
        ((q : Fin (terminalCount scale profileDelta +
          terminalCount scale profileDelta)) →
          ExtractedLogicalPairTerminalBridge scale horizon
            profileDelta x y omega q) :=
  fun code ↦ ⟨code.1,
    fun q ↦ eraseExtractedLogicalPairMarkedTerminalBridge (code.2 q)⟩

/-- Visit-certificate erasure is injective on the full pair code. -/
theorem eraseExtractedLogicalPairMarkedCode_injective
    {start scale horizon : ℕ} {profileDelta : ℝ} {x y : Point}
    {omega : StepPath}
    {leftVisits rightVisits : Fin (terminalCount scale profileDelta) → ℕ} :
    Function.Injective
      (eraseExtractedLogicalPairMarkedCode
        (start := start) (scale := scale) (horizon := horizon)
        (profileDelta := profileDelta) (x := x) (y := y) (omega := omega)
        (leftVisits := leftVisits) (rightVisits := rightVisits)) := by
  intro c d hcd
  apply Prod.ext
  · simpa [eraseExtractedLogicalPairMarkedCode] using congrArg Prod.fst hcd
  · funext q
    apply Subtype.ext
    have htuple := congrArg Prod.snd hcd
    have hq := congrFun htuple q
    simpa [eraseExtractedLogicalPairMarkedCode,
      eraseExtractedLogicalPairMarkedTerminalBridge] using
        congrArg Subtype.val hq

/-- Restrict an actual extracted unmarked atom to prescribed visit counts.
The complete complementary word and chronological assembly are inherited by
literal erasure of visit certificates. -/
def markExtractedLogicalPairComplementarySkeletonAtom
    {start scale horizon : ℕ} {profileDelta : ℝ} {x y : Point}
    {omega : StepPath}
    (leftVisits rightVisits : Fin (terminalCount scale profileDelta) → ℕ)
    (base : ComplementarySkeletonAtom
      (terminalCount scale profileDelta + terminalCount scale profileDelta)
      (Fin start → Direction)
      (ExtractedLogicalPairTerminalBridge
        scale horizon profileDelta x y omega))
    (hword : ∀ q bridge, base.bridgeWord q bridge = bridge.1) :
    ComplementarySkeletonAtom
      (terminalCount scale profileDelta + terminalCount scale profileDelta)
      (Fin start → Direction)
      (ExtractedLogicalPairMarkedTerminalBridge scale horizon profileDelta
        x y omega leftVisits rightVisits) where
  complementWord := base.complementWord
  bridgeWord := fun _ bridge ↦ bridge.1
  assemble := fun code ↦
    base.assemble (eraseExtractedLogicalPairMarkedCode code)
  prefixFree_assemble := by
    intro c d hcd
    apply base.prefixFree_assemble
    exact fun herase ↦ hcd
      (eraseExtractedLogicalPairMarkedCode_injective herase)
  prefixFree_bridge := fun q ↦
    prefixFree_boundaryVisitExitWordCode
      (terminalOuterBoundary scale (logicalPairCenter x y q))
      (logicalPairCenter x y q)
      (pairEntrancePoint
        (extractTimedTerminalSkeleton scale horizon profileDelta x omega)
        (extractTimedTerminalSkeleton scale horizon profileDelta y omega) q)
      (logicalPairVisitVector leftVisits rightVisits q)
      (pairExitPoint
        (extractTimedTerminalSkeleton scale horizon profileDelta x omega)
        (extractTimedTerminalSkeleton scale horizon profileDelta y omega) q)
  length_assemble := by
    intro code
    simpa only [eraseExtractedLogicalPairMarkedCode,
      eraseExtractedLogicalPairMarkedTerminalBridge_word, hword] using
        base.length_assemble (eraseExtractedLogicalPairMarkedCode code)

/-- The concrete marked extracted pair atom, with no new pathwise premise
beyond those required by the unmarked extracted atom. -/
def extractedLogicalPairMarkedComplementarySkeletonAtom
    {start scale horizon : ℕ} {profileDelta : ℝ} {x y : Point}
    {omega : StepPath}
    (leftVisits rightVisits : Fin (terminalCount scale profileDelta) → ℕ)
    (hscale : 1 ≤ scale)
    (hlevel : separationLevel scale x y ≤ scale)
    (hexit : IsOuterExitTime (trajectory omega) scale horizon)
    (hx : SuccessfulPoint (trajectory omega) scale horizon profileDelta x)
    (hy : SuccessfulPoint (trajectory omega) scale horizon profileDelta y)
    (hxbox : x ∈ candidateBox scale) (hybox : y ∈ candidateBox scale) :
    ComplementarySkeletonAtom
      (terminalCount scale profileDelta + terminalCount scale profileDelta)
      (Fin start → Direction)
      (ExtractedLogicalPairMarkedTerminalBridge scale horizon profileDelta
        x y omega leftVisits rightVisits) :=
  markExtractedLogicalPairComplementarySkeletonAtom leftVisits rightVisits
    (extractedLogicalPairComplementarySkeletonAtom
      hscale hlevel hexit hx hy hxbox hybox) (fun _ _ => rfl)

/-- The marked atom uses exactly the unmarked atom's complementary word. -/
@[simp] theorem extractedLogicalPairMarkedComplementarySkeletonAtom_complementWord
    {start scale horizon : ℕ} {profileDelta : ℝ} {x y : Point}
    {omega : StepPath}
    (leftVisits rightVisits : Fin (terminalCount scale profileDelta) → ℕ)
    (hscale : 1 ≤ scale)
    (hlevel : separationLevel scale x y ≤ scale)
    (hexit : IsOuterExitTime (trajectory omega) scale horizon)
    (hx : SuccessfulPoint (trajectory omega) scale horizon profileDelta x)
    (hy : SuccessfulPoint (trajectory omega) scale horizon profileDelta y)
    (hxbox : x ∈ candidateBox scale) (hybox : y ∈ candidateBox scale)
    (pre : Fin start → Direction) :
    (extractedLogicalPairMarkedComplementarySkeletonAtom leftVisits rightVisits
      hscale hlevel hexit hx hy hxbox hybox).complementWord pre =
      (extractedLogicalPairComplementarySkeletonAtom
        hscale hlevel hexit hx hy hxbox hybox).complementWord pre := rfl

/-- Consequently, marking does not change the one-copy common weight. -/
@[simp] theorem extractedLogicalPairMarkedComplementarySkeletonAtom_weight
    {start scale horizon : ℕ} {profileDelta : ℝ} {x y : Point}
    {omega : StepPath}
    (leftVisits rightVisits : Fin (terminalCount scale profileDelta) → ℕ)
    (hscale : 1 ≤ scale)
    (hlevel : separationLevel scale x y ≤ scale)
    (hexit : IsOuterExitTime (trajectory omega) scale horizon)
    (hx : SuccessfulPoint (trajectory omega) scale horizon profileDelta x)
    (hy : SuccessfulPoint (trajectory omega) scale horizon profileDelta y)
    (hxbox : x ∈ candidateBox scale) (hybox : y ∈ candidateBox scale) :
    (extractedLogicalPairMarkedComplementarySkeletonAtom
      (start := start) leftVisits rightVisits hscale hlevel hexit hx hy
        hxbox hybox).weight =
      (extractedLogicalPairComplementarySkeletonAtom
        (start := start) hscale hlevel hexit hx hy hxbox hybox).weight := rfl

/-- Marked chronological assembly is precisely unmarked chronological
assembly after erasing the visit certificates. -/
@[simp] theorem extractedLogicalPairMarkedComplementarySkeletonAtom_assemble
    {start scale horizon : ℕ} {profileDelta : ℝ} {x y : Point}
    {omega : StepPath}
    (leftVisits rightVisits : Fin (terminalCount scale profileDelta) → ℕ)
    (hscale : 1 ≤ scale)
    (hlevel : separationLevel scale x y ≤ scale)
    (hexit : IsOuterExitTime (trajectory omega) scale horizon)
    (hx : SuccessfulPoint (trajectory omega) scale horizon profileDelta x)
    (hy : SuccessfulPoint (trajectory omega) scale horizon profileDelta y)
    (hxbox : x ∈ candidateBox scale) (hybox : y ∈ candidateBox scale)
    (code : (Fin start → Direction) ×
      ((q : Fin (terminalCount scale profileDelta +
        terminalCount scale profileDelta)) →
        ExtractedLogicalPairMarkedTerminalBridge scale horizon profileDelta
          x y omega leftVisits rightVisits q)) :
    (extractedLogicalPairMarkedComplementarySkeletonAtom leftVisits rightVisits
      hscale hlevel hexit hx hy hxbox hybox).assemble code =
      (extractedLogicalPairComplementarySkeletonAtom
        hscale hlevel hexit hx hy hxbox hybox).assemble
          (eraseExtractedLogicalPairMarkedCode code) := rfl

@[simp] theorem extractedLogicalPairMarkedComplementarySkeletonAtom_bridgeWord
    {start scale horizon : ℕ} {profileDelta : ℝ} {x y : Point}
    {omega : StepPath}
    (leftVisits rightVisits : Fin (terminalCount scale profileDelta) → ℕ)
    (hscale : 1 ≤ scale)
    (hlevel : separationLevel scale x y ≤ scale)
    (hexit : IsOuterExitTime (trajectory omega) scale horizon)
    (hx : SuccessfulPoint (trajectory omega) scale horizon profileDelta x)
    (hy : SuccessfulPoint (trajectory omega) scale horizon profileDelta y)
    (hxbox : x ∈ candidateBox scale) (hybox : y ∈ candidateBox scale)
    (q : Fin (terminalCount scale profileDelta +
      terminalCount scale profileDelta))
    (bridge : ExtractedLogicalPairMarkedTerminalBridge scale horizon
      profileDelta x y omega leftVisits rightVisits q) :
    (extractedLogicalPairMarkedComplementarySkeletonAtom
      (start := start) leftVisits rightVisits hscale hlevel hexit hx hy
        hxbox hybox).bridgeWord q bridge = bridge.1 := rfl

/-- A logical bridge coordinate can only exist at scale at least two. -/
theorem two_le_scale_of_logicalPairCoordinate
    {scale : ℕ} {profileDelta : ℝ} (hscale : 1 ≤ scale)
    (q : Fin (terminalCount scale profileDelta +
      terminalCount scale profileDelta)) :
    2 ≤ scale := by
  by_contra hnot
  have hscaleEq : scale = 1 := by omega
  subst scale
  have hq := q.isLt
  simp [terminalCount] at hq

/-- Each marked coordinate's target centre is strictly inside its terminal
outer boundary, including the vacuous scale-one case. -/
theorem logicalPairCenter_not_mem_terminalOuterBoundary
    {scale : ℕ} {profileDelta : ℝ} {x y : Point}
    (hscale : 1 ≤ scale)
    (q : Fin (terminalCount scale profileDelta +
      terminalCount scale profileDelta)) :
    logicalPairCenter x y q ∉
      terminalOuterBoundary scale (logicalPairCenter x y q) :=
  center_not_mem_terminalOuterBoundary scale (logicalPairCenter x y q)
    (two_le_scale_of_logicalPairCoordinate hscale q)

/-- Every bridge kernel of the marked extracted atom is the canonical
joint visit-count/exit-point stopped kernel. -/
theorem extractedLogicalPairMarkedComplementarySkeletonAtom_kernel
    {start scale horizon : ℕ} {profileDelta : ℝ} {x y : Point}
    {omega : StepPath}
    (leftVisits rightVisits : Fin (terminalCount scale profileDelta) → ℕ)
    (hscale : 1 ≤ scale)
    (hlevel : separationLevel scale x y ≤ scale)
    (hexit : IsOuterExitTime (trajectory omega) scale horizon)
    (hx : SuccessfulPoint (trajectory omega) scale horizon profileDelta x)
    (hy : SuccessfulPoint (trajectory omega) scale horizon profileDelta y)
    (hxbox : x ∈ candidateBox scale) (hybox : y ∈ candidateBox scale)
    (q : Fin (terminalCount scale profileDelta +
      terminalCount scale profileDelta)) :
    (extractedLogicalPairMarkedComplementarySkeletonAtom
      (start := start) leftVisits rightVisits hscale hlevel hexit hx hy
        hxbox hybox).kernel q =
      terminalMarkedKernel
        (terminalOuterBoundary scale (logicalPairCenter x y q))
        (logicalPairCenter x y q)
        (pairEntrancePoint
          (extractTimedTerminalSkeleton scale horizon profileDelta x omega)
          (extractTimedTerminalSkeleton scale horizon profileDelta y omega) q)
        (logicalPairVisitVector leftVisits rightVisits q)
        (pairExitPoint
          (extractTimedTerminalSkeleton scale horizon profileDelta x omega)
          (extractTimedTerminalSkeleton scale horizon profileDelta y omega) q) := by
  unfold ComplementarySkeletonAtom.kernel terminalMarkedKernel
  symm
  exact (boundaryVisitExitStoppedEventCode
    (terminalOuterBoundary scale (logicalPairCenter x y q))
    (logicalPairCenter x y q)
    (pairEntrancePoint
      (extractTimedTerminalSkeleton scale horizon profileDelta x omega)
      (extractTimedTerminalSkeleton scale horizon profileDelta y omega) q)
    (logicalPairVisitVector leftVisits rightVisits q)
    (pairExitPoint
      (extractTimedTerminalSkeleton scale horizon profileDelta x omega)
      (extractTimedTerminalSkeleton scale horizon profileDelta y omega) q)
    (logicalPairCenter_not_mem_terminalOuterBoundary hscale q)).mass_eq

/-- The same bridge kernel in the explicit canonical
`boundaryVisitExitKernel` form. -/
theorem extractedLogicalPairMarkedComplementarySkeletonAtom_kernel_eq_boundaryVisitExitKernel
    {start scale horizon : ℕ} {profileDelta : ℝ} {x y : Point}
    {omega : StepPath}
    (leftVisits rightVisits : Fin (terminalCount scale profileDelta) → ℕ)
    (hscale : 1 ≤ scale)
    (hlevel : separationLevel scale x y ≤ scale)
    (hexit : IsOuterExitTime (trajectory omega) scale horizon)
    (hx : SuccessfulPoint (trajectory omega) scale horizon profileDelta x)
    (hy : SuccessfulPoint (trajectory omega) scale horizon profileDelta y)
    (hxbox : x ∈ candidateBox scale) (hybox : y ∈ candidateBox scale)
    (q : Fin (terminalCount scale profileDelta +
      terminalCount scale profileDelta)) :
    (extractedLogicalPairMarkedComplementarySkeletonAtom
      (start := start) leftVisits rightVisits hscale hlevel hexit hx hy
        hxbox hybox).kernel q =
      boundaryVisitExitKernel
        (terminalOuterBoundary scale (logicalPairCenter x y q))
        (logicalPairCenter x y q)
        (pairEntrancePoint
          (extractTimedTerminalSkeleton scale horizon profileDelta x omega)
          (extractTimedTerminalSkeleton scale horizon profileDelta y omega) q)
        (logicalPairVisitVector leftVisits rightVisits q)
        (pairExitPoint
          (extractTimedTerminalSkeleton scale horizon profileDelta x omega)
          (extractTimedTerminalSkeleton scale horizon profileDelta y omega) q) := by
  rw [extractedLogicalPairMarkedComplementarySkeletonAtom_kernel]
  exact terminalMarkedKernel_eq_boundaryVisitExitKernel
    (terminalOuterBoundary scale (logicalPairCenter x y q))
    (logicalPairCenter x y q)
    (pairEntrancePoint
      (extractTimedTerminalSkeleton scale horizon profileDelta x omega)
      (extractTimedTerminalSkeleton scale horizon profileDelta y omega) q)
    (pairExitPoint
      (extractTimedTerminalSkeleton scale horizon profileDelta x omega)
      (extractTimedTerminalSkeleton scale horizon profileDelta y omega) q)
    (logicalPairCenter_not_mem_terminalOuterBoundary hscale q)
    (logicalPairVisitVector leftVisits rightVisits q)

/-- Pair-factorization view: the common marked word is still stored once and
the prescribed visits remain split into left and right vectors. -/
def extractedLogicalPairMarkedSharedPrefixAtom
    {start scale horizon : ℕ} {profileDelta : ℝ} {x y : Point}
    {omega : StepPath}
    (leftVisits rightVisits : Fin (terminalCount scale profileDelta) → ℕ)
    (hscale : 1 ≤ scale)
    (hlevel : separationLevel scale x y ≤ scale)
    (hexit : IsOuterExitTime (trajectory omega) scale horizon)
    (hx : SuccessfulPoint (trajectory omega) scale horizon profileDelta x)
    (hy : SuccessfulPoint (trajectory omega) scale horizon profileDelta y)
    (hxbox : x ∈ candidateBox scale) (hybox : y ∈ candidateBox scale) :=
  SharedPrefixPairAtom.ofComplementarySkeletonAtom
    (mLeft := terminalCount scale profileDelta)
    (mRight := terminalCount scale profileDelta)
    (extractedLogicalPairMarkedComplementarySkeletonAtom
      (start := start) leftVisits rightVisits hscale hlevel hexit hx hy
        hxbox hybox)

end

end Erdos1165.SharedPrefixPairExtractedMarkedAtom
