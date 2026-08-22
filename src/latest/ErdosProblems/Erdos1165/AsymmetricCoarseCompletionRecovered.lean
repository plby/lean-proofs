/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/
import ErdosProblems.Erdos1165.AsymmetricCoarseCompletionWitness

/-!
# Re-extraction of coarse asymmetric completion codes

The retained coarse scanner record fixes the split clock without fixing the
strictly deeper right-hand profile.  Consequently every path in one coarse
completion atom re-extracts the same coarse code.
-/

open Set

namespace Erdos1165.AsymmetricCoarseCompletionRecovered

open AnnularBoundaryExcursionKernel AnnularProfileClocks
open AsymmetricCoarseScanSignature
open AsymmetricCoarseCompletionSourceGeometry
open AsymmetricCoarseSplitCompletion AsymmetricCoarseSplitCompletionSource
open AsymmetricExtractedReturnClockRecovery AsymmetricReturnPrefixRecovery
open AsymmetricSplitCompletionCode AsymmetricSplitCompletionRecovered
open AsymmetricSplitCompletionSource AsymmetricSplitLevelSplice
open MarkedBridgeFactorization Proposition13Assembly
open TerminalSkeletonFactorization TerminalSkeletonInvariance
open TerminalSkeletonWords ThickPoint TerminalSequentialVisitLaw

noncomputable section

attribute [local instance] Classical.propDecidable

theorem coarseSplitCompletionData_eq_of_fields
    {start n k : ℕ}
    {left right : CoarseSplitCompletionData start n k}
    (hcount : left.returnCount = right.returnCount)
    (hpre : left.pre = right.pre)
    (hskeleton : HEq left.skeleton right.skeleton)
    (hsignature : HEq left.signature right.signature) :
    left = right := by
  cases left
  cases right
  simp only [CoarseSplitCompletionData.mk.injEq]
  exact ⟨hcount, hpre, hskeleton, hsignature⟩

/-- The data available from membership in a literal coarse completion atom.
The last field is the only place where the retained right scanner is used. -/
def SourceCoarseSplitCompletionMemberCore
    (start n k : ℕ) (x y : Point) (hk : k + 1 ≤ n)
    (data : CoarseSplitCompletionData start n k) (omega : StepPath) : Prop :=
  ∃ candidate : (j : Fin data.returnCount) →
      CoarseSignatureReturnCode x y (profileInnerBoundary n k y) data j,
    let words : TerminalSegmentWords data.returnCount :=
      fun j ↦ List.ofFn (candidate j).1.1.2
    omega ∈ stoppedWordCylinder
        (assembleAfterPrefix data.pre data.skeleton words) ∧
      IsOuterExitTime (trajectory (shiftSteps start omega)) n
        (assembledTerminalHorizon data.skeleton words) ∧
      stoppedOuterExitHorizon start n omega =
        assembledTerminalHorizon data.skeleton words ∧
      boundaryExcursionCount
        (profileInnerBoundary n k y) (profileInnerBoundary n (k + 1) y)
        (0, 0) (shiftSteps start omega)
        (assembledTerminalHorizon data.skeleton words) = data.returnCount

/-- The chosen reference and any candidate with the same coarse record have
the same split-clock count.  Cylinder membership transfers that equality to
the actual source and actual candidate paths. -/
theorem sourceCoarseSplitCompletionMemberCore
    {start n k : ℕ} {x y : Point} {source : StepPath}
    (hn : 2 ≤ n) (hk : k + 1 ≤ n)
    (hy : y ∈ candidateBox n)
    (hexit : IsOuterExitTime (trajectory (shiftSteps start source)) n
      (stoppedOuterExitHorizon start n source))
    (omega : StepPath)
    (homega : omega ∈ (sourceCoarseSplitCompletionAtom (x := x) (y := y)
      source (Nat.one_le_of_lt hn) hk hy hexit).event) :
    SourceCoarseSplitCompletionMemberCore start n k x y hk
      (sourceCoarseSplitCompletionData start n k hk x y source) omega := by
  unfold sourceCoarseSplitCompletionAtom at homega
  obtain ⟨candidate, hcylinder⟩ :=
    exists_coarseSignatureReturnCodes_of_mem
      (sourceCoarseSplitCompletionGlobalFirst
        (Nat.one_le_of_lt hn) hk hy hexit) homega
  let data := sourceCoarseSplitCompletionData start n k hk x y source
  let words : TerminalSegmentWords data.returnCount :=
    fun j ↦ List.ofFn (candidate j).1.1.2
  let horizon := assembledTerminalHorizon data.skeleton words
  have htail : shiftSteps start omega ∈
      stoppedWordCylinder (assembledTerminalWord data.skeleton words) :=
    TerminalSkeletonFactorization.shiftSteps_mem_assembledTerminalWordCylinder_of_mem_assembleAfterPrefix
      hcylinder
  have hcanonicalFirst : AbsoluteBoundaryFirstAt
      (discBoundary (0, 0) (outerScale n)) (0, 0)
      (assembledTerminalPath data.skeleton words) horizon :=
    sourceCoarseSplitCompletionGlobalFirst
      (Nat.one_le_of_lt hn) hk hy hexit (fun j ↦ (candidate j).1)
  have hactualFirst : AbsoluteBoundaryFirstAt
      (discBoundary (0, 0) (outerScale n)) (0, 0)
      (shiftSteps start omega) horizon :=
    absoluteBoundaryFirstAt_of_mem_stoppedWordCylinder htail hcanonicalFirst
  have hactualExit : IsOuterExitTime
      (trajectory (shiftSteps start omega)) n horizon := by
    simpa only [AbsoluteBoundaryFirstAt, IsOuterExitTime,
      trajectoryFrom_zero_eq_trajectory] using hactualFirst
  have hhorizon : stoppedOuterExitHorizon start n omega = horizon :=
    stoppedOuterExitHorizon_eq_of_isOuterExitTime hactualExit
  have hactualTrajectory : ∀ r ≤ horizon,
      trajectory (shiftSteps start omega) r =
        trajectory (assembledTerminalPath data.skeleton words) r := by
    intro r hr
    exact trajectory_eq_assembledTerminalPath_of_mem_stoppedWordCylinder
      htail hr
  let reference := sourceCoarseReferenceCandidate
    (x := x) (y := y) (Nat.one_le_of_lt hn) hk hy hexit
  let referenceWords : TerminalSegmentWords data.returnCount :=
    fun j ↦ List.ofFn (reference j).1.1.2
  let referenceHorizon :=
    assembledTerminalHorizon data.skeleton referenceWords
  have hsourceCylinder := source_mem_sourceCoarseReferenceCylinder
    (x := x) (y := y) (Nat.one_le_of_lt hn) hk hy hexit
  have hsourceTail : shiftSteps start source ∈
      stoppedWordCylinder
        (assembledTerminalWord data.skeleton referenceWords) :=
    TerminalSkeletonFactorization.shiftSteps_mem_assembledTerminalWordCylinder_of_mem_assembleAfterPrefix
      hsourceCylinder
  have hsourceTrajectory : ∀ r ≤ referenceHorizon,
      trajectory (shiftSteps start source) r =
        trajectory (assembledTerminalPath data.skeleton referenceWords) r := by
    intro r hr
    exact trajectory_eq_assembledTerminalPath_of_mem_stoppedWordCylinder
      hsourceTail hr
  have hcountReferenceCandidate :=
    sourceCoarseReferenceCandidate_completedCount_eq
      (x := x) (y := y) hn hk hy hexit candidate
  let middle := profileInnerBoundary n k y
  let inner := profileInnerBoundary n (k + 1) y
  let outer := profileOuterBoundary n (k + 1) y
  have houterMiddle : outer = middle := by
    simp only [outer, middle, profileOuterBoundary, profileInnerBoundary,
      Nat.add_sub_cancel]
  have hcount : boundaryExcursionCount middle inner (0, 0)
      (shiftSteps start omega) horizon = data.returnCount := by
    calc
      boundaryExcursionCount middle inner (0, 0)
          (shiftSteps start omega) horizon =
          completedExcursionCount (trajectory (shiftSteps start omega))
            outer inner horizon := by
        simp only [boundaryExcursionCount, completedExcursionCount,
          trajectoryFrom_zero_eq_trajectory, houterMiddle]
      _ = completedExcursionCount
          (trajectory (assembledTerminalPath data.skeleton words))
          outer inner horizon :=
        Proposition13Measurability.completedExcursionCount_congr_prefix
          hactualTrajectory outer inner
      _ = completedExcursionCount
          (trajectory (assembledTerminalPath data.skeleton referenceWords))
          outer inner referenceHorizon := by
        simpa only [data, words, horizon, reference, referenceWords,
          referenceHorizon, outer, inner] using hcountReferenceCandidate.symm
      _ = completedExcursionCount (trajectory (shiftSteps start source))
          outer inner referenceHorizon :=
        (Proposition13Measurability.completedExcursionCount_congr_prefix
          hsourceTrajectory outer inner).symm
      _ = boundaryExcursionCount middle inner (0, 0)
          (shiftSteps start source) referenceHorizon := by
        simp only [boundaryExcursionCount, completedExcursionCount,
          trajectoryFrom_zero_eq_trajectory, houterMiddle]
      _ = data.returnCount := by
        have hreferenceFirst : AbsoluteBoundaryFirstAt
            (discBoundary (0, 0) (outerScale n)) (0, 0)
            (assembledTerminalPath data.skeleton referenceWords)
            referenceHorizon :=
          sourceCoarseSplitCompletionGlobalFirst
            (Nat.one_le_of_lt hn) hk hy hexit (fun j ↦ (reference j).1)
        have hsourceFirst := absoluteBoundaryFirstAt_of_mem_stoppedWordCylinder
          hsourceTail hreferenceFirst
        have hsourceExit : IsOuterExitTime
            (trajectory (shiftSteps start source)) n referenceHorizon := by
          simpa only [referenceHorizon, assembledTerminalHorizon,
            assembledTerminalWord, AbsoluteBoundaryFirstAt, IsOuterExitTime,
            trajectoryFrom_zero_eq_trajectory] using hsourceFirst
        have href : referenceHorizon = stoppedOuterExitHorizon start n source :=
          isOuterExitTime_unique hsourceExit hexit
        rw [href]
        rfl
  refine ⟨candidate, hcylinder, hactualExit, hhorizon, ?_⟩
  simpa only [data, words, horizon, middle, inner] using hcount

/-- Reconstructing the compressed source packet with an arbitrary coarse
candidate recovers the same skeleton and the literal candidate words. -/
theorem sourceCoarseCandidateCanonicalReturnData
    {start n k : ℕ} {x y : Point} {source : StepPath}
    (hn : 1 ≤ n) (hk : k + 1 ≤ n)
    (hy : y ∈ candidateBox n)
    (hexit : IsOuterExitTime (trajectory (shiftSteps start source)) n
      (stoppedOuterExitHorizon start n source))
    (candidate : (j : Fin
      (sourceCoarseSplitCompletionData start n k hk x y source).returnCount) →
      CoarseSignatureReturnCode x y (profileInnerBoundary n k y)
        (sourceCoarseSplitCompletionData start n k hk x y source) j) :
    let data := sourceCoarseSplitCompletionData start n k hk x y source
    let middle := profileInnerBoundary n k y
    let inner := profileInnerBoundary n (k + 1) y
    let words : TerminalSegmentWords data.returnCount :=
      fun j ↦ List.ofFn (candidate j).1.1.2
    let newT := extractTimedReturnSkeleton
      (assembledTerminalPath data.skeleton words) (0, 0) middle inner
      (assembledTerminalHorizon data.skeleton words) data.returnCount
    compressTimedSkeleton (assembledTerminalPath data.skeleton words) newT =
        data.skeleton ∧
      intervalWords (assembledTerminalPath data.skeleton words)
        newT.entrance newT.exit = words := by
  dsimp only
  have h := compressedReturnData_assembled_of_boundaryExitWordCodes
    (sourceReturnComplete hn hk hy hexit)
    (sourceCoarseCandidateBoundaryCodes hk candidate)
  have hwords :
      (fun j ↦ List.ofFn
        ((sourceCoarseCandidateBoundaryCodes hk candidate j).1.2)) =
        (fun j ↦ List.ofFn (candidate j).1.1.2) := by
    funext j
    exact sourceCoarseCandidateBoundaryCodes_word hk candidate j
  rw [hwords] at h
  simpa only [sourceCoarseSplitCompletionData, coarsenSplitCompletionData,
    sourceSplitCompletionData, splitCompletionDataAt] using h

/-- Every path in the coarse retained atom re-extracts its literal coarse
source code. -/
theorem sourceCoarseSplitCompletionData_recovered
    {start n k : ℕ} {x y : Point} {source : StepPath}
    (hn : 2 ≤ n) (hk : k + 1 ≤ n)
    (hy : y ∈ candidateBox n)
    (hexit : IsOuterExitTime (trajectory (shiftSteps start source)) n
      (stoppedOuterExitHorizon start n source)) :
    (sourceCoarseSplitCompletionAtom (x := x) (y := y)
      source (Nat.one_le_of_lt hn) hk hy hexit).event ⊆
      {omega | sourceCoarseSplitCompletionData start n k hk x y omega =
        sourceCoarseSplitCompletionData start n k hk x y source} := by
  intro omega homega
  have hcore := sourceCoarseSplitCompletionMemberCore
    hn hk hy hexit omega homega
  unfold SourceCoarseSplitCompletionMemberCore at hcore
  obtain ⟨candidate, hcylinder, hactualExit, hhorizon, hcount⟩ := hcore
  let data := sourceCoarseSplitCompletionData start n k hk x y source
  let words : TerminalSegmentWords data.returnCount :=
    fun j ↦ List.ofFn (candidate j).1.1.2
  let horizon := assembledTerminalHorizon data.skeleton words
  let middle := profileInnerBoundary n k y
  let inner := profileInnerBoundary n (k + 1) y
  have hcompleteActual : ∀ j : Fin data.returnCount,
      excursionStart (trajectory (shiftSteps start omega)) middle inner
        horizon (j + 1) ≤ horizon := by
    have h := sourceReturnComplete (n := n) (k := k) (y := y)
      (omega := shiftSteps start omega) (horizon := horizon)
      (Nat.one_le_of_lt hn) hk hy hactualExit
    exact returnComplete_of_boundaryExcursionCount_eq hcount h
  have htail : shiftSteps start omega ∈
      stoppedWordCylinder (assembledTerminalWord data.skeleton words) :=
    TerminalSkeletonFactorization.shiftSteps_mem_assembledTerminalWordCylinder_of_mem_assembleAfterPrefix
      hcylinder
  have hpre : stepPrefix start omega = data.pre :=
    stepPrefix_eq_of_mem_assembleAfterPrefix hcylinder
  have hprefix : ∀ r < horizon,
      shiftSteps start omega r =
        assembledTerminalPath data.skeleton words r :=
    increment_eq_assembledTerminalPath_of_mem_stoppedWordCylinder htail
  have hcongr := compressedReturnData_congr_stoppedPrefix
    (middle := middle) (inner := inner) (horizon := horizon)
    (q := data.returnCount) hprefix hcompleteActual
  have hcanonicalSource := sourceCoarseCandidateCanonicalReturnData
    (x := x) (y := y) (Nat.one_le_of_lt hn) hk hy hexit candidate
  have hskel := hcongr.1.trans hcanonicalSource.1
  have hwords := hcongr.2.trans hcanonicalSource.2
  let actualT := extractTimedReturnSkeleton (shiftSteps start omega) (0, 0)
    middle inner horizon data.returnCount
  have hskelData :
      compressTimedSkeleton (shiftSteps start omega) actualT = data.skeleton :=
    hskel
  have hwordsData :
      intervalWords (shiftSteps start omega) actualT.entrance actualT.exit =
        words := by
    funext j
    exact congrFun hwords j
  have hentrancePoint : ∀ j : Fin data.returnCount,
      actualT.entrancePoint j = data.skeleton.2.1 j := by
    intro j
    exact congrArg (fun code : TerminalSkeletonCode data.returnCount ↦
      code.2.1 j) hskelData
  have hsignature :
      (fun j : Fin data.returnCount ↦
        (PrefixXProfileScanSignature n k x (actualT.entrancePoint j)
            (intervalWords (shiftSteps start omega)
              actualT.entrance actualT.exit j),
          SingleScanSignature
            (profileOuterBoundary n (k + 1) y)
            (profileInnerBoundary n (k + 1) y)
            (actualT.entrancePoint j)
            (intervalWords (shiftSteps start omega)
              actualT.entrance actualT.exit j))) = data.signature := by
    funext j
    apply Prod.ext
    · rw [hentrancePoint j, congrFun hwordsData j]
      exact (candidate j).2.1
    · rw [hentrancePoint j, congrFun hwordsData j]
      exact (candidate j).2.2
  let actualData : CoarseSplitCompletionData start n k :=
    { returnCount := data.returnCount
      pre := stepPrefix start omega
      skeleton := compressTimedSkeleton (shiftSteps start omega) actualT
      signature := fun j ↦
        (PrefixXProfileScanSignature n k x (actualT.entrancePoint j)
            (intervalWords (shiftSteps start omega)
              actualT.entrance actualT.exit j),
          SingleScanSignature
            (profileOuterBoundary n (k + 1) y)
            (profileInnerBoundary n (k + 1) y)
            (actualT.entrancePoint j)
            (intervalWords (shiftSteps start omega)
              actualT.entrance actualT.exit j)) }
  have hactualExtracted :
      sourceCoarseSplitCompletionData start n k hk x y omega = actualData := by
    unfold sourceCoarseSplitCompletionData coarsenSplitCompletionData
    unfold splitCompletionDataAt
    dsimp only
    rw [hhorizon, hcount]
    rfl
  have hactualData : actualData = data := by
    apply coarseSplitCompletionData_eq_of_fields
    · rfl
    · exact hpre
    · exact heq_of_eq_same_type hskelData
    · exact heq_of_eq_same_type hsignature
  exact hactualExtracted.trans hactualData

end

end Erdos1165.AsymmetricCoarseCompletionRecovered
