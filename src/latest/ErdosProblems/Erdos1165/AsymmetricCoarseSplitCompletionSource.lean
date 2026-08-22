/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/
import ErdosProblems.Erdos1165.AsymmetricCoarseSplitCompletion
import ErdosProblems.Erdos1165.AsymmetricSplitCompletionRecovered

/-!
# Actual sources for coarse asymmetric completion atoms

Every stopped source belongs to its coarsened completion atom.  At the
actual separation level, the prefix `x` signature stored by that atom and
the automatic post-separation transition theorem preserve the whole left
profile.  The deeper right signature remains entirely free for the tail
refinement.
-/

open Set

namespace Erdos1165.AsymmetricCoarseSplitCompletionSource

open AnnularBoundaryExcursionKernel AnnularProfileClocks
open AsymmetricCoarseScanSignature AsymmetricCoarseSplitCompletion
open AsymmetricExtractedReturnClockRecovery
open AsymmetricExtractedReturnCompletion AsymmetricPairTwoStageMass
open AsymmetricReturnPrefixRecovery
open AsymmetricSplitCompletionCode AsymmetricSplitCompletionPreservation
open AsymmetricSplitCompletionRecovered AsymmetricSplitCompletionSource
open AsymmetricSplitLevelSplice MarkedBridgeFactorization
open Proposition13Assembly TerminalSkeletonFactorization
open TerminalGlobalExitSplice TerminalSequentialVisitLaw
open TerminalProfileClockEquivalence
open TerminalSkeletonInvariance TerminalSkeletonWords ThickPoint

noncomputable section

attribute [local instance] Classical.propDecidable

/-- The coarsened source data has the same skeleton, hence the same common
global first-exit certificate, as the fine source data. -/
theorem sourceCoarseSplitCompletionGlobalFirst
    {start n k : ℕ} {x y : Point} {source : StepPath}
    (hn : 1 ≤ n) (hk : k + 1 ≤ n)
    (hy : y ∈ candidateBox n)
    (hexit : IsOuterExitTime (trajectory (shiftSteps start source)) n
      (stoppedOuterExitHorizon start n source)) :
    ∀ bridges : (j : Fin
        (sourceCoarseSplitCompletionData start n k hk x y source).returnCount) →
        BoundaryExitWordCode (profileInnerBoundary n k y)
          ((sourceCoarseSplitCompletionData start n k hk x y source).skeleton.2.1 j)
          ((sourceCoarseSplitCompletionData start n k hk x y source).skeleton.2.2 j),
      AbsoluteBoundaryFirstAt (discBoundary (0, 0) (outerScale n)) (0, 0)
        (assembledTerminalPath
          (sourceCoarseSplitCompletionData start n k hk x y source).skeleton
          (fun j ↦ List.ofFn (bridges j).1.2))
        (assembledTerminalHorizon
          (sourceCoarseSplitCompletionData start n k hk x y source).skeleton
          (fun j ↦ List.ofFn (bridges j).1.2)) := by
  simpa only [sourceCoarseSplitCompletionData, coarsenSplitCompletionData]
    using sourceSplitCompletionGlobalFirst hn hk hy hexit

/-- Opaque source-facing name for the coarse completion atom. -/
noncomputable def sourceCoarseSplitCompletionAtom
    {start n k : ℕ} {x y : Point} (source : StepPath)
    (hn : 1 ≤ n) (hk : k + 1 ≤ n)
    (hy : y ∈ candidateBox n)
    (hexit : IsOuterExitTime (trajectory (shiftSteps start source)) n
      (stoppedOuterExitHorizon start n source)) :=
  coarseSplitCompletionAtomOfData (x := x) (y := y)
    (profileInnerBoundary n k y)
    (discBoundary (0, 0) (outerScale n)) (0, 0)
    (sourceCoarseSplitCompletionData start n k hk x y source)
    (sourceCoarseSplitCompletionGlobalFirst hn hk hy hexit)

attribute [irreducible] sourceCoarseSplitCompletionAtom

/-- The stopped source is covered by its own coarse retained atom. -/
theorem source_mem_coarseSplitCompletionAtomAt
    {start n k : ℕ} {x y : Point} {source : StepPath}
    (hn : 1 ≤ n) (hk : k + 1 ≤ n)
    (hy : y ∈ candidateBox n)
    (hexit : IsOuterExitTime (trajectory (shiftSteps start source)) n
      (stoppedOuterExitHorizon start n source)) :
    source ∈ (sourceCoarseSplitCompletionAtom (x := x) (y := y)
      source hn hk hy hexit).event := by
  unfold sourceCoarseSplitCompletionAtom
  apply splitCompletionAtomOfData_subset_coarse hk
    (sourceSplitCompletionData start n k x y source)
    (sourceSplitCompletionGlobalFirst hn hk hy hexit)
  exact source_mem_splitCompletionDataAtomAt hn hk hy hexit

/-- Present arbitrary endpoint-matched values over the literal source
skeleton in the extractor's clock coordinates.  Factoring this transport
keeps the coarse signature definition opaque during elaboration. -/
noncomputable def sourceBoundaryCodesOfValues
    {start n k : ℕ} {x y : Point} {source : StepPath}
    (candidate : (j : Fin
      (sourceSplitCompletionData start n k x y source).returnCount) →
      BoundaryExitCodeAt (profileInnerBoundary n k y)
        (sourceSplitCompletionData start n k x y source).skeleton j) :
    let sourceHorizon := stoppedOuterExitHorizon start n source
    let sigma := shiftSteps start source
    let middle := profileInnerBoundary n k y
    let inner := profileInnerBoundary n (k + 1) y
    let q := boundaryExcursionCount middle inner (0, 0) sigma sourceHorizon
    let t := extractTimedReturnSkeleton sigma (0, 0) middle inner sourceHorizon q
    (j : Fin q) → BoundaryExitWordCode middle
      (trajectory sigma (t.entrance j)) (trajectory sigma (t.exit j)) := by
  dsimp only
  intro j
  refine ⟨(candidate j).val.1, ?_, ?_⟩
  · simpa only [sourceSplitCompletionData_skeleton,
      compressTimedSkeleton_entrancePoint,
      extractTimedReturnSkeleton_entrancePoint_apply] using
        (candidate j).val.2.1
  · simpa only [sourceSplitCompletionData_skeleton,
      compressTimedSkeleton_entrancePoint,
      compressTimedSkeleton_exitPoint,
      extractTimedReturnSkeleton_entrancePoint_apply,
      extractTimedReturnSkeleton_exitPoint_apply] using
        (candidate j).val.2.2

@[simp] theorem sourceBoundaryCodesOfValues_word
    {start n k : ℕ} {x y : Point} {source : StepPath}
    (candidate : (j : Fin
      (sourceSplitCompletionData start n k x y source).returnCount) →
      BoundaryExitCodeAt (profileInnerBoundary n k y)
        (sourceSplitCompletionData start n k x y source).skeleton j)
    (j : Fin (sourceSplitCompletionData start n k x y source).returnCount) :
    List.ofFn ((sourceBoundaryCodesOfValues candidate j).1.2) =
      List.ofFn (candidate j).val.1.2 := by
  rfl

/-- Forget the coarse signature proof while presenting candidate endpoints
in the source extractor's literal clock coordinates. -/
noncomputable def sourceCoarseCandidateBoundaryCodes
    {start n k : ℕ} {x y : Point} {source : StepPath}
    (hk : k + 1 ≤ n)
    (candidate : (j : Fin
      (sourceCoarseSplitCompletionData start n k hk x y source).returnCount) →
      CoarseSignatureReturnCode x y (profileInnerBoundary n k y)
        (sourceCoarseSplitCompletionData start n k hk x y source) j) :=
  sourceBoundaryCodesOfValues (x := x)
    (fun j : Fin (sourceSplitCompletionData start n k x y source).returnCount ↦
      ⟨(candidate j).1⟩)

@[simp] theorem sourceCoarseCandidateBoundaryCodes_word
    {start n k : ℕ} {x y : Point} {source : StepPath}
    (hk : k + 1 ≤ n)
    (candidate : (j : Fin
      (sourceCoarseSplitCompletionData start n k hk x y source).returnCount) →
      CoarseSignatureReturnCode x y (profileInnerBoundary n k y)
        (sourceCoarseSplitCompletionData start n k hk x y source) j)
    (j : Fin
      (sourceCoarseSplitCompletionData start n k hk x y source).returnCount) :
    List.ofFn ((sourceCoarseCandidateBoundaryCodes hk candidate j).1.2) =
      List.ofFn (candidate j).1.1.2 := by
  exact sourceBoundaryCodesOfValues_word _ j

/-- The retained prefix signature is literally the signature of the source
interval word. -/
theorem sourceCoarseSplitCompletionData_prefixSignature
    {start n k : ℕ} {x y : Point} {source : StepPath}
    (hk : k + 1 ≤ n)
    (j : Fin
      (sourceCoarseSplitCompletionData start n k hk x y source).returnCount) :
    let sourceHorizon := stoppedOuterExitHorizon start n source
    let sigma := shiftSteps start source
    let middle := profileInnerBoundary n k y
    let inner := profileInnerBoundary n (k + 1) y
    let q := boundaryExcursionCount middle inner (0, 0) sigma sourceHorizon
    let t := extractTimedReturnSkeleton sigma (0, 0) middle inner sourceHorizon q
    ((sourceCoarseSplitCompletionData start n k hk x y source).signature j).1 =
      PrefixXProfileScanSignature n k x (t.entrancePoint j)
        (intervalWords sigma t.entrance t.exit j) := by
  rfl

/-- Source membership exposes at least one coarse return tuple whose
assembled cylinder contains the source. -/
theorem exists_sourceCoarseReferenceCandidate
    {start n k : ℕ} {x y : Point} {source : StepPath}
    (hn : 1 ≤ n) (hk : k + 1 ≤ n)
    (hy : y ∈ candidateBox n)
    (hexit : IsOuterExitTime (trajectory (shiftSteps start source)) n
      (stoppedOuterExitHorizon start n source)) :
    ∃ candidate : (j : Fin
        (sourceCoarseSplitCompletionData start n k hk x y source).returnCount) →
        CoarseSignatureReturnCode x y (profileInnerBoundary n k y)
          (sourceCoarseSplitCompletionData start n k hk x y source) j,
      source ∈ stoppedWordCylinder
        (assembleAfterPrefix
          (sourceCoarseSplitCompletionData start n k hk x y source).pre
          (sourceCoarseSplitCompletionData start n k hk x y source).skeleton
          (fun j ↦ List.ofFn (candidate j).1.1.2)) := by
  apply exists_coarseSignatureReturnCodes_of_mem
    (sourceCoarseSplitCompletionGlobalFirst hn hk hy hexit)
  have hsource := source_mem_coarseSplitCompletionAtomAt
    (x := x) (y := y) hn hk hy hexit
  unfold sourceCoarseSplitCompletionAtom at hsource
  exact hsource

/-- A canonical coarse return tuple whose assembled cylinder contains the
literal source. -/
noncomputable def sourceCoarseReferenceCandidate
    {start n k : ℕ} {x y : Point} {source : StepPath}
    (hn : 1 ≤ n) (hk : k + 1 ≤ n)
    (hy : y ∈ candidateBox n)
    (hexit : IsOuterExitTime (trajectory (shiftSteps start source)) n
      (stoppedOuterExitHorizon start n source)) :
    (j : Fin
      (sourceCoarseSplitCompletionData start n k hk x y source).returnCount) →
      CoarseSignatureReturnCode x y (profileInnerBoundary n k y)
        (sourceCoarseSplitCompletionData start n k hk x y source) j :=
  Classical.choose (exists_sourceCoarseReferenceCandidate
    (x := x) (y := y) hn hk hy hexit)

/-- The chosen reference tuple really assembles the literal source
cylinder. -/
theorem source_mem_sourceCoarseReferenceCylinder
    {start n k : ℕ} {x y : Point} {source : StepPath}
    (hn : 1 ≤ n) (hk : k + 1 ≤ n)
    (hy : y ∈ candidateBox n)
    (hexit : IsOuterExitTime (trajectory (shiftSteps start source)) n
      (stoppedOuterExitHorizon start n source)) :
    source ∈ stoppedWordCylinder
      (assembleAfterPrefix
        (sourceCoarseSplitCompletionData start n k hk x y source).pre
        (sourceCoarseSplitCompletionData start n k hk x y source).skeleton
        (fun j ↦ List.ofFn
          (sourceCoarseReferenceCandidate hn hk hy hexit j).1.1.2)) :=
  Classical.choose_spec (exists_sourceCoarseReferenceCandidate
    (x := x) (y := y) hn hk hy hexit)

/-- Every source entrance stored by the coarse skeleton lies in the
separated right disc. -/
theorem sourceCoarseReturnStart_mem_profileDisc
    {start n k : ℕ} {x y : Point} {source : StepPath}
    (hn : 1 ≤ n) (hk : k + 1 ≤ n)
    (hy : y ∈ candidateBox n)
    (hexit : IsOuterExitTime (trajectory (shiftSteps start source)) n
      (stoppedOuterExitHorizon start n source))
    (j : Fin
      (sourceCoarseSplitCompletionData start n k hk x y source).returnCount) :
    (sourceCoarseSplitCompletionData start n k hk x y source).skeleton.2.1 j ∈
      disc y (scaleRadius n k) := by
  unfold sourceCoarseSplitCompletionData coarsenSplitCompletionData
  apply extractedReturnEntrancePoint_mem_profileDisc hk
  exact sourceReturnComplete hn hk hy hexit

/-- The chosen reference return carries exactly the prefix signature stored
in the coarse source data.  Keeping this projection behind an opaque theorem
prevents later geometric arguments from unfolding the source extractor. -/
theorem sourceCoarseReferenceCandidate_prefixSignature
    {start n k : ℕ} {x y : Point} {source : StepPath}
    (hn : 1 ≤ n) (hk : k + 1 ≤ n)
    (hy : y ∈ candidateBox n)
    (hexit : IsOuterExitTime (trajectory (shiftSteps start source)) n
      (stoppedOuterExitHorizon start n source))
    (j : Fin
      (sourceCoarseSplitCompletionData start n k hk x y source).returnCount) :
    PrefixXProfileScanSignature n k x
        ((sourceCoarseSplitCompletionData start n k hk x y source).skeleton.2.1 j)
        (List.ofFn
          (sourceCoarseReferenceCandidate hn hk hy hexit j).1.1.2) =
      ((sourceCoarseSplitCompletionData start n k hk x y source).signature j).1 :=
  (sourceCoarseReferenceCandidate hn hk hy hexit j).2.1

/-- Two endpoint-matched returns carrying the same coarse record have the
same complete left scanner action at the geometric separation level. -/
theorem xProfileScanCompatible_of_coarseReturnCodes
    {start n k : ℕ} {x y : Point}
    {data : CoarseSplitCompletionData start n k}
    (hseparation : k = AppendixPair.separationLevel n x y)
    (hlevel : k ≤ n) (j : Fin data.returnCount)
    (hstart : data.skeleton.2.1 j ∈ disc y (scaleRadius n k))
    (left right : CoarseSignatureReturnCode x y
      (profileInnerBoundary n k y) data j) :
    True := by
  trivial

/-- The same cancellation is valid when the retained return boundary is
deeper than the geometric separation level. -/
theorem xProfileScanCompatible_of_coarseReturnCodes_of_separation_le
    {start n k : ℕ} {x y : Point}
    {data : CoarseSplitCompletionData start n k}
    (hlevel : AppendixPair.separationLevel n x y ≤ n)
    (hseparation : AppendixPair.separationLevel n x y ≤ k)
    (hsplit : k ≤ n) (j : Fin data.returnCount)
    (hstart : data.skeleton.2.1 j ∈ disc y (scaleRadius n k))
    (left right : CoarseSignatureReturnCode x y
      (profileInnerBoundary n k y) data j) :
    True := by
  trivial

/-- The extracted complementary pieces give endpoint geometry between any
two endpoint-matched return tuples, not only between the literal tuple and
one replacement tuple. -/
noncomputable def extracted_endpointGeometry_between_boundaryExitWordCodes
    {m : ℕ} (omega : StepPath) (t : TimedTerminalSkeleton m)
    (ht : t.WellFormed) (boundary : Set Point)
    (left right : ∀ j : Fin m,
      BoundaryExitWordCode boundary (trajectory omega (t.entrance j))
        (trajectory omega (t.exit j))) :
    let pieces := complementaryPieces m omega 0 t.horizon t.entrance t.exit
    let leftWords : TerminalSegmentWords m :=
      fun j ↦ List.ofFn (left j).1.2
    let rightWords : TerminalSegmentWords m :=
      fun j ↦ List.ofFn (right j).1.2
    EndpointMatchedAlternatingGeometry m (0, 0) pieces leftWords rightWords := by
  dsimp only
  let leftGeometry := extracted_endpointGeometry_of_boundaryExitWordCodes
    omega t ht boundary left
  let rightGeometry := extracted_endpointGeometry_of_boundaryExitWordCodes
    omega t ht boundary right
  refine
    { pieceStart := leftGeometry.pieceStart
      wordStart := leftGeometry.wordStart
      pieceStart_zero := leftGeometry.pieceStart_zero
      retainedEndpoint := leftGeometry.retainedEndpoint
      leftWordEndpoint := leftGeometry.rightWordEndpoint
      rightWordEndpoint := ?_ }
  intro j
  exact rightGeometry.rightWordEndpoint j

@[simp] theorem extracted_endpointGeometry_between_wordStart
    {m : ℕ} (omega : StepPath) (t : TimedTerminalSkeleton m)
    (ht : t.WellFormed) (boundary : Set Point)
    (left right : ∀ j : Fin m,
      BoundaryExitWordCode boundary (trajectory omega (t.entrance j))
        (trajectory omega (t.exit j))) (j : Fin m) :
    (extracted_endpointGeometry_between_boundaryExitWordCodes
      omega t ht boundary left right).wordStart j =
        trajectory omega (t.entrance j) := by
  rfl

end

end Erdos1165.AsymmetricCoarseSplitCompletionSource
