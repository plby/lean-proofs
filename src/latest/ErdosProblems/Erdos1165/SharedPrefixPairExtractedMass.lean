/-
Copyright (c) 2026 The Erdos Problems Formalization Project.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Erdos Problems Formalization Project
-/
import ErdosProblems.Erdos1165.SharedPrefixPairExtractedMarkedAtom
import ErdosProblems.Erdos1165.MarkedBoundaryVisitKernel

/-!
# Exact mass of the extracted shared-prefix pair atom

This is the probability-facing endpoint of the mixed-splice construction.
The global-first-hit premise has already been discharged pathwise in
`SharedPrefixPairExtractedAtom`; here its literal stopped-word event is
factorized into one common retained weight and the two actual terminal
first-boundary kernel products.
-/

open MeasureTheory
open scoped BigOperators ENNReal

namespace Erdos1165.SharedPrefixPairExtractedMass

open AppendixPair Hitting
open MarkedBridgeFactorization SharedPrefixPairExtractedAtom
open SharedPrefixPairExtractedMarkedAtom
open SharedPrefixPairFactorization SharedPrefixPairMergedSkeleton
open TerminalExcursionPathwise TerminalSequentialVisitLaw
open ThickPoint

noncomputable section

/-- The no-`hfirst` extracted pair atom has exactly one retained common
weight.  The two products are indexed logically (left, then right), even
though the underlying erased intervals are reinserted chronologically. -/
theorem fairSteps_extractedLogicalPairSharedPrefixAtom_event_eq_commonWeight_mul
    {start scale horizon : ℕ} {profileDelta : ℝ} {x y : Point}
    {omega : StepPath}
    (hscale : 1 ≤ scale)
    (hlevel : AppendixPair.separationLevel scale x y ≤ scale)
    (hexit : IsOuterExitTime (trajectory omega) scale horizon)
    (hx : SuccessfulPoint (trajectory omega) scale horizon profileDelta x)
    (hy : SuccessfulPoint (trajectory omega) scale horizon profileDelta y)
    (hxbox : x ∈ candidateBox scale) (hybox : y ∈ candidateBox scale) :
    let left := TerminalSkeletonWords.extractTimedTerminalSkeleton
      scale horizon profileDelta x omega
    let right := TerminalSkeletonWords.extractTimedTerminalSkeleton
      scale horizon profileDelta y omega
    let atom := extractedLogicalPairSharedPrefixAtom (start := start)
      hscale hlevel hexit hx hy hxbox hybox
    fairSteps atom.event = atom.commonWeight *
      ((∏ i, MarkedBoundaryVisitKernel.terminalSkeletonKernel
          (terminalOuterBoundary scale
            (logicalPairCenter x y (Fin.castAdd
              (SharedPrefixPairExtraction.terminalCount scale profileDelta) i)))
          (pairEntrancePoint left right (Fin.castAdd
            (SharedPrefixPairExtraction.terminalCount scale profileDelta) i))
          (pairExitPoint left right (Fin.castAdd
            (SharedPrefixPairExtraction.terminalCount scale profileDelta) i))) *
        ∏ j, MarkedBoundaryVisitKernel.terminalSkeletonKernel
          (terminalOuterBoundary scale
            (logicalPairCenter x y (Fin.natAdd
              (SharedPrefixPairExtraction.terminalCount scale profileDelta) j)))
          (pairEntrancePoint left right (Fin.natAdd
            (SharedPrefixPairExtraction.terminalCount scale profileDelta) j))
          (pairExitPoint left right (Fin.natAdd
            (SharedPrefixPairExtraction.terminalCount scale profileDelta) j))) := by
  dsimp only
  let left := TerminalSkeletonWords.extractTimedTerminalSkeleton
    scale horizon profileDelta x omega
  let right := TerminalSkeletonWords.extractTimedTerminalSkeleton
    scale horizon profileDelta y omega
  let atom := extractedLogicalPairSharedPrefixAtom (start := start)
    hscale hlevel hexit hx hy hxbox hybox
  change fairSteps atom.event = atom.commonWeight *
    ((∏ i, MarkedBoundaryVisitKernel.terminalSkeletonKernel
        (terminalOuterBoundary scale
          (logicalPairCenter x y (Fin.castAdd
            (SharedPrefixPairExtraction.terminalCount scale profileDelta) i)))
        (pairEntrancePoint left right (Fin.castAdd
          (SharedPrefixPairExtraction.terminalCount scale profileDelta) i))
        (pairExitPoint left right (Fin.castAdd
          (SharedPrefixPairExtraction.terminalCount scale profileDelta) i))) *
      ∏ j, MarkedBoundaryVisitKernel.terminalSkeletonKernel
        (terminalOuterBoundary scale
          (logicalPairCenter x y (Fin.natAdd
            (SharedPrefixPairExtraction.terminalCount scale profileDelta) j)))
        (pairEntrancePoint left right (Fin.natAdd
          (SharedPrefixPairExtraction.terminalCount scale profileDelta) j))
        (pairExitPoint left right (Fin.natAdd
          (SharedPrefixPairExtraction.terminalCount scale profileDelta) j)))
  apply fairSteps_event_eq_commonWeight_mul_stoppedEvents atom
    (fun i ↦ boundaryExitEndpointSteps
      (terminalOuterBoundary scale
        (logicalPairCenter x y (Fin.castAdd
          (SharedPrefixPairExtraction.terminalCount scale profileDelta) i)))
      (pairEntrancePoint left right (Fin.castAdd
        (SharedPrefixPairExtraction.terminalCount scale profileDelta) i))
      (pairExitPoint left right (Fin.castAdd
        (SharedPrefixPairExtraction.terminalCount scale profileDelta) i)))
    (fun j ↦ boundaryExitEndpointSteps
      (terminalOuterBoundary scale
        (logicalPairCenter x y (Fin.natAdd
          (SharedPrefixPairExtraction.terminalCount scale profileDelta) j)))
      (pairEntrancePoint left right (Fin.natAdd
        (SharedPrefixPairExtraction.terminalCount scale profileDelta) j))
      (pairExitPoint left right (Fin.natAdd
        (SharedPrefixPairExtraction.terminalCount scale profileDelta) j)))
  · intro i
    rw [boundaryExitEndpointSteps_eq_stoppedWordEvent]
    have hword :
        (fun bridge : BoundaryExitWordCode
            (terminalOuterBoundary scale
              (logicalPairCenter x y (Fin.castAdd
                (SharedPrefixPairExtraction.terminalCount scale profileDelta) i)))
            (pairEntrancePoint left right (Fin.castAdd
              (SharedPrefixPairExtraction.terminalCount scale profileDelta) i))
            (pairExitPoint left right (Fin.castAdd
              (SharedPrefixPairExtraction.terminalCount scale profileDelta) i)) ↦
                bridge.1) =
          atom.leftBridgeWord i := by
      funext bridge
      rfl
    exact congrArg stoppedWordEvent hword
  · intro j
    rw [boundaryExitEndpointSteps_eq_stoppedWordEvent]
    have hword :
        (fun bridge : BoundaryExitWordCode
            (terminalOuterBoundary scale
              (logicalPairCenter x y (Fin.natAdd
                (SharedPrefixPairExtraction.terminalCount scale profileDelta) j)))
            (pairEntrancePoint left right (Fin.natAdd
              (SharedPrefixPairExtraction.terminalCount scale profileDelta) j))
            (pairExitPoint left right (Fin.natAdd
              (SharedPrefixPairExtraction.terminalCount scale profileDelta) j)) ↦
                bridge.1) =
          atom.rightBridgeWord j := by
      funext bridge
      rfl
    exact congrArg stoppedWordEvent hword

/-- Marked analogue: visit certificates alter only the two bridge products;
the common retained weight is literally the same as for the unmarked pair
atom. -/
theorem fairSteps_extractedLogicalPairMarkedSharedPrefixAtom_event_eq_commonWeight_mul
    {start scale horizon : ℕ} {profileDelta : ℝ} {x y : Point}
    {omega : StepPath}
    (leftVisits rightVisits :
      Fin (SharedPrefixPairExtraction.terminalCount scale profileDelta) → ℕ)
    (hscale : 1 ≤ scale)
    (hlevel : AppendixPair.separationLevel scale x y ≤ scale)
    (hexit : IsOuterExitTime (trajectory omega) scale horizon)
    (hx : SuccessfulPoint (trajectory omega) scale horizon profileDelta x)
    (hy : SuccessfulPoint (trajectory omega) scale horizon profileDelta y)
    (hxbox : x ∈ candidateBox scale) (hybox : y ∈ candidateBox scale) :
    let left := TerminalSkeletonWords.extractTimedTerminalSkeleton
      scale horizon profileDelta x omega
    let right := TerminalSkeletonWords.extractTimedTerminalSkeleton
      scale horizon profileDelta y omega
    let atom := extractedLogicalPairMarkedSharedPrefixAtom
      (start := start) leftVisits rightVisits
      hscale hlevel hexit hx hy hxbox hybox
    fairSteps atom.event = atom.commonWeight *
      ((∏ i, MarkedBoundaryVisitKernel.terminalMarkedKernel
          (terminalOuterBoundary scale
            (logicalPairCenter x y (Fin.castAdd
              (SharedPrefixPairExtraction.terminalCount scale profileDelta) i)))
          (logicalPairCenter x y (Fin.castAdd
            (SharedPrefixPairExtraction.terminalCount scale profileDelta) i))
          (pairEntrancePoint left right (Fin.castAdd
            (SharedPrefixPairExtraction.terminalCount scale profileDelta) i))
          (leftVisits i)
          (pairExitPoint left right (Fin.castAdd
            (SharedPrefixPairExtraction.terminalCount scale profileDelta) i))) *
        ∏ j, MarkedBoundaryVisitKernel.terminalMarkedKernel
          (terminalOuterBoundary scale
            (logicalPairCenter x y (Fin.natAdd
              (SharedPrefixPairExtraction.terminalCount scale profileDelta) j)))
          (logicalPairCenter x y (Fin.natAdd
            (SharedPrefixPairExtraction.terminalCount scale profileDelta) j))
          (pairEntrancePoint left right (Fin.natAdd
            (SharedPrefixPairExtraction.terminalCount scale profileDelta) j))
          (rightVisits j)
          (pairExitPoint left right (Fin.natAdd
            (SharedPrefixPairExtraction.terminalCount scale profileDelta) j))) := by
  dsimp only
  let atom := extractedLogicalPairMarkedSharedPrefixAtom
    (start := start) leftVisits rightVisits
    hscale hlevel hexit hx hy hxbox hybox
  rw [fairSteps_event_eq_commonWeight_mul_pairKernels atom]
  apply congrArg (atom.commonWeight * ·)
  apply congrArg₂ (fun left right ↦ left * right)
  · apply Finset.prod_congr rfl
    intro i _hi
    change (extractedLogicalPairMarkedComplementarySkeletonAtom
      (start := start) leftVisits rightVisits hscale hlevel hexit hx hy
        hxbox hybox).kernel
          (Fin.castAdd
            (SharedPrefixPairExtraction.terminalCount scale profileDelta) i) = _
    rw [extractedLogicalPairMarkedComplementarySkeletonAtom_kernel,
      logicalPairVisitVector_castAdd]
  · apply Finset.prod_congr rfl
    intro j _hj
    change (extractedLogicalPairMarkedComplementarySkeletonAtom
      (start := start) leftVisits rightVisits hscale hlevel hexit hx hy
        hxbox hybox).kernel
          (Fin.natAdd
            (SharedPrefixPairExtraction.terminalCount scale profileDelta) j) = _
    rw [extractedLogicalPairMarkedComplementarySkeletonAtom_kernel,
      logicalPairVisitVector_natAdd]

end

end Erdos1165.SharedPrefixPairExtractedMass
