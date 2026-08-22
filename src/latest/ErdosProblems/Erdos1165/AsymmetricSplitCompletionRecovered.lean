/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/
import ErdosProblems.Erdos1165.AsymmetricSplitCompletionSource

/-!
# Re-extraction of asymmetric split-completion codes

Every path in a retained completion atom re-extracts the same fixed prefix,
return count, compressed skeleton, and pair of scanner signatures.
-/

open Set

namespace Erdos1165.AsymmetricSplitCompletionRecovered

open AnnularBoundaryExcursionKernel AnnularProfileClocks
open AsymmetricExtractedReturnClockRecovery
open AsymmetricReturnPrefixRecovery AsymmetricSplitCompletionCode
open AsymmetricSplitCompletionSource AsymmetricSplitLevelSplice
open AsymmetricSplitCompletionPreservation
open AsymmetricExtractedReturnCompletion AsymmetricPairTwoStageMass
open MarkedBridgeFactorization TerminalSkeletonFactorization
open TerminalSequentialVisitLaw TerminalSkeletonInvariance
open TerminalSkeletonWords ThickPoint

noncomputable section

attribute [local instance] Classical.propDecidable

theorem splitCompletionData_eq_of_fields
    {start n : ℕ} {left right : SplitCompletionData start n}
    (hcount : left.returnCount = right.returnCount)
    (hpre : left.pre = right.pre)
    (hskeleton : HEq left.skeleton right.skeleton)
    (hsignature : HEq left.signature right.signature) :
    left = right := by
  cases left with
  | mk leftCount leftPre leftSkeleton leftSignature =>
      cases right with
      | mk rightCount rightPre rightSkeleton rightSignature =>
          rw [SplitCompletionData.mk.injEq]
          exact ⟨hcount, hpre, hskeleton, hsignature⟩

theorem heq_of_eq_same_type {α : Sort*} {left right : α}
    (h : left = right) : HEq left right := by
  cases h
  rfl

theorem sourceSplitCompletionGlobalFirst
    {start n k : ℕ} {x y : Point} {omega : StepPath}
    (hn : 1 ≤ n) (hk : k + 1 ≤ n)
    (hy : y ∈ candidateBox n)
    (hexit : IsOuterExitTime
      (trajectory (shiftSteps start omega)) n
      (stoppedOuterExitHorizon start n omega)) :
    ∀ bridges : (j : Fin
        (sourceSplitCompletionData start n k x y omega).returnCount) →
        BoundaryExitWordCode (profileInnerBoundary n k y)
          ((sourceSplitCompletionData start n k x y omega).skeleton.2.1 j)
          ((sourceSplitCompletionData start n k x y omega).skeleton.2.2 j),
      AbsoluteBoundaryFirstAt (discBoundary (0, 0) (outerScale n)) (0, 0)
        (assembledTerminalPath
          (sourceSplitCompletionData start n k x y omega).skeleton
          (fun j ↦ List.ofFn (bridges j).1.2))
        (assembledTerminalHorizon
          (sourceSplitCompletionData start n k x y omega).skeleton
          (fun j ↦ List.ofFn (bridges j).1.2)) := by
  unfold sourceSplitCompletionData splitCompletionDataAt
  exact sourceGlobalFirst hn hk hy hexit

theorem source_mem_splitCompletionDataAtomAt
    {start n k : ℕ} {x y : Point} {omega : StepPath}
    (hn : 1 ≤ n) (hk : k + 1 ≤ n)
    (hy : y ∈ candidateBox n)
    (hexit : IsOuterExitTime
      (trajectory (shiftSteps start omega)) n
      (stoppedOuterExitHorizon start n omega)) :
    omega ∈ (splitCompletionAtomOfData (x := x) (y := y)
        (profileInnerBoundary n k y)
        (discBoundary (0, 0) (outerScale n)) (0, 0)
        (sourceSplitCompletionData start n k x y omega)
        (sourceSplitCompletionGlobalFirst hn hk hy hexit)).event := by
  have hsource := source_mem_pairedSignatureCompletionAt
    (x := x) (y := y) hn hk hy hexit
  dsimp only at hsource
  unfold sourceSplitCompletionData splitCompletionDataAt
  rw [ComplementarySkeletonAtom.event, stoppedWordEvent] at hsource ⊢
  obtain ⟨index, hcylinder⟩ := Set.mem_iUnion.mp hsource
  apply Set.mem_iUnion.mpr
  refine ⟨(Unit.unit, fun j ↦ ⟨(index.2 j).1, ?_⟩), ?_⟩
  · dsimp only
    simpa only [compressTimedSkeleton_entrancePoint] using (index.2 j).2
  · simpa only [splitCompletionAtomOfData, pairedSignatureFixedCompletionAtom,
      fixComplement, restrictBridges, boundaryReturnCompletionAtom,
      sourceSplitCompletionData, splitCompletionDataAt] using hcylinder

theorem stepPrefix_eq_of_mem_assembleAfterPrefix
    {start m : ℕ} {pre : Fin start → Direction}
    {code : TerminalSkeletonCode m} {words : TerminalSegmentWords m}
    {omega : StepPath}
    (homega : omega ∈ stoppedWordCylinder
      (assembleAfterPrefix pre code words)) :
    stepPrefix start omega = pre := by
  funext i
  let tail := reconstructTerminalPacket (code, words)
  have hi : (i : ℕ) < (List.ofFn pre ++ tail).length := by
    simp only [List.length_append, List.length_ofFn]
    omega
  have h := congrFun homega ⟨i, by
    simpa only [assembleAfterPrefix, stoppedWordOfList_length] using hi⟩
  change omega i = (List.ofFn pre ++ tail).get ⟨i, hi⟩ at h
  change omega i = pre i
  rw [h, List.get_eq_getElem]
  calc
    (List.ofFn pre ++ tail)[(i : ℕ)] =
        (List.ofFn pre)[(i : ℕ)] :=
      List.getElem_append_left (by simp only [List.length_ofFn]; exact i.2)
    _ = pre ⟨i, by simpa only [List.length_ofFn] using i.2⟩ :=
      List.getElem_ofFn _
    _ = pre i := by congr

theorem returnComplete_of_boundaryExcursionCount_eq
    {horizon q : ℕ} {middle inner : Set Point} {omega : StepPath}
    (hcount : boundaryExcursionCount middle inner (0, 0) omega horizon = q)
    (hcomplete : ∀ j : Fin (boundaryExcursionCount middle inner (0, 0)
      omega horizon),
      excursionStart (trajectory omega) middle inner horizon (j + 1) ≤
        horizon) :
    ∀ j : Fin q,
      excursionStart (trajectory omega) middle inner horizon (j + 1) ≤
        horizon := by
  subst q
  exact hcomplete

@[simp] theorem extractTimedReturnSkeleton_horizon
    (omega : StepPath) (start : Point) (middle inner : Set Point)
    (horizon q : ℕ) :
    (extractTimedReturnSkeleton omega start middle inner horizon q).horizon =
      horizon := rfl

theorem compressedReturnData_assembled_of_boundaryExitWordCodes
    {horizon q : ℕ} {middle inner : Set Point} {omega : StepPath}
    (hcomplete : ∀ j : Fin q,
      excursionStart (trajectory omega) middle inner horizon (j + 1) ≤ horizon)
    (bridges : ∀ j : Fin q,
      BoundaryExitWordCode middle
        (trajectory omega
          ((extractTimedReturnSkeleton omega (0, 0) middle inner
            horizon q).entrance j))
        (trajectory omega
          ((extractTimedReturnSkeleton omega (0, 0) middle inner
            horizon q).exit j))) :
    let t := extractTimedReturnSkeleton omega (0, 0) middle inner horizon q
    let code := compressTimedSkeleton omega t
    let words : TerminalSegmentWords q := fun j ↦ List.ofFn (bridges j).1.2
    let newT := extractTimedReturnSkeleton
      (assembledTerminalPath code words) (0, 0) middle inner
      (assembledTerminalHorizon code words) q
    compressTimedSkeleton (assembledTerminalPath code words) newT = code ∧
      intervalWords (assembledTerminalPath code words)
        newT.entrance newT.exit = words := by
  have h := compressedReturnSkeleton_reconstructed_of_boundaryExitWordCodes
    hcomplete bridges
  constructor
  · simpa only [assembledTerminalPath_eq_reconstructedTerminalStepPath,
      assembledTerminalHorizon_eq_alternatingConcat_length,
      compressTimedSkeleton, extractTimedReturnSkeleton_horizon] using h.1
  · funext j
    simpa only [assembledTerminalPath_eq_reconstructedTerminalStepPath,
      assembledTerminalHorizon_eq_alternatingConcat_length,
      compressTimedSkeleton, extractTimedReturnSkeleton_horizon] using h.2 j

def SourceSplitCompletionMemberCore
    (start n k : ℕ) (x y : Point) (data : SplitCompletionData start n)
    (omega : StepPath) : Prop :=
  ∃ candidate : (j : Fin data.returnCount) →
      SignatureCompatibleReturnCode x y (profileInnerBoundary n k y) data j,
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

/-- The finite `y` signature recovers the split-level count, while the
assembled cylinder recovers the common first global exit. -/
theorem sourceSplitCompletionMemberCore
    {start n k : ℕ} {x y : Point} {source : StepPath}
    (hn : 2 ≤ n) (hk : k + 1 ≤ n)
    (hy : y ∈ candidateBox n)
    (hexit : IsOuterExitTime
      (trajectory (shiftSteps start source)) n
      (stoppedOuterExitHorizon start n source))
    (omega : StepPath)
    (homega : omega ∈ (splitCompletionAtomOfData (x := x) (y := y)
      (profileInnerBoundary n k y)
      (discBoundary (0, 0) (outerScale n)) (0, 0)
      (sourceSplitCompletionData start n k x y source)
      (sourceSplitCompletionGlobalFirst (by omega) hk hy hexit)).event) :
    SourceSplitCompletionMemberCore start n k x y
      (sourceSplitCompletionData start n k x y source) omega := by
  obtain ⟨candidate, hcylinder⟩ :=
    exists_signatureCompatibleReturnCodes_of_mem_splitCompletionAtomOfData
      (sourceSplitCompletionGlobalFirst (by omega) hk hy hexit) homega
  let data := sourceSplitCompletionData start n k x y source
  let words : TerminalSegmentWords data.returnCount :=
    fun j ↦ List.ofFn (candidate j).1.1.2
  let horizon := assembledTerminalHorizon data.skeleton words
  have htail : shiftSteps start omega ∈
      stoppedWordCylinder (assembledTerminalWord data.skeleton words) := by
    exact
      TerminalSkeletonFactorization.shiftSteps_mem_assembledTerminalWordCylinder_of_mem_assembleAfterPrefix
        hcylinder
  have hcanonicalFirst : AbsoluteBoundaryFirstAt
      (discBoundary (0, 0) (outerScale n)) (0, 0)
      (assembledTerminalPath data.skeleton words) horizon := by
    exact sourceSplitCompletionGlobalFirst (by omega) hk hy hexit
      (fun j ↦ (candidate j).1)
  have hactualFirst : AbsoluteBoundaryFirstAt
      (discBoundary (0, 0) (outerScale n)) (0, 0)
      (shiftSteps start omega) horizon := by
    exact absoluteBoundaryFirstAt_of_mem_stoppedWordCylinder
      htail hcanonicalFirst
  have hactualExit : IsOuterExitTime
      (trajectory (shiftSteps start omega)) n horizon := by
    simpa only [AbsoluteBoundaryFirstAt, IsOuterExitTime,
      trajectoryFrom_zero_eq_trajectory] using hactualFirst
  have hhorizon : stoppedOuterExitHorizon start n omega = horizon :=
    stoppedOuterExitHorizon_eq_of_isOuterExitTime hactualExit
  let sourceHorizon := stoppedOuterExitHorizon start n source
  let sigma := shiftSteps start source
  let middle := profileInnerBoundary n k y
  let inner := profileInnerBoundary n (k + 1) y
  let q := boundaryExcursionCount middle inner (0, 0) sigma sourceHorizon
  let t := extractTimedReturnSkeleton sigma (0, 0) middle inner sourceHorizon q
  have hcomplete : ∀ j : Fin q,
      excursionStart (trajectory sigma) middle inner sourceHorizon (j + 1) ≤
        sourceHorizon := by
    exact sourceReturnComplete (by omega) hk hy hexit
  let yCandidate : (j : Fin q) →
      ExtractedCompatibleReturnCandidate n y sigma middle inner
        sourceHorizon q j := fun j ↦ ⟨(candidate j).1, by
    rw [xProfileScanCompatible_iff_signature_eq]
    have hsig := (candidate j).2.2.symm
    simpa only [data, sourceSplitCompletionData, splitCompletionDataAt,
      compressTimedSkeleton_entrancePoint] using hsig⟩
  have hprofileCanonicalSource :
      excursionProfile (trajectory (assembledTerminalPath data.skeleton words))
          n horizon y =
        excursionProfile (trajectory sigma) n sourceHorizon y := by
    simpa only [data, sourceSplitCompletionData, splitCompletionDataAt,
      words, horizon] using
      (sourceCandidateProfile_eq hn hcomplete yCandidate)
  have htrajectory : ∀ r ≤ horizon,
      trajectory (shiftSteps start omega) r =
        trajectory (assembledTerminalPath data.skeleton words) r := by
    intro r hr
    exact trajectory_eq_assembledTerminalPath_of_mem_stoppedWordCylinder
      htail hr
  have hprofileActualCanonical :
      excursionProfile (trajectory (shiftSteps start omega)) n horizon y =
        excursionProfile (trajectory (assembledTerminalPath data.skeleton words))
          n horizon y :=
    Proposition13Measurability.excursionProfile_congr_prefix htrajectory y
  let level : Fin (n + 2) := ⟨k + 1, by omega⟩
  have hcount : boundaryExcursionCount middle inner (0, 0)
      (shiftSteps start omega) horizon = q := by
    calc
      boundaryExcursionCount middle inner (0, 0)
          (shiftSteps start omega) horizon =
          profileCompletedCount (trajectory (shiftSteps start omega)) n
            horizon y (k + 1) := by
        simp only [boundaryExcursionCount, profileCompletedCount, middle, inner,
          profileOuterBoundary, profileInnerBoundary,
          trajectoryFrom_zero_eq_trajectory]
        simp only [Nat.add_sub_cancel]
      _ = excursionProfile (trajectory (shiftSteps start omega)) n horizon y
          level := by
        symm
        exact excursionProfile_eq_profileCompletedCount _ _ _ _
          (by omega) (by omega)
      _ = excursionProfile
          (trajectory (assembledTerminalPath data.skeleton words)) n horizon y
          level := congrFun hprofileActualCanonical level
      _ = excursionProfile (trajectory sigma) n sourceHorizon y level :=
        congrFun hprofileCanonicalSource level
      _ = profileCompletedCount (trajectory sigma) n sourceHorizon y
          (k + 1) := by
        exact excursionProfile_eq_profileCompletedCount _ _ _ _
          (by omega) (by omega)
      _ = boundaryExcursionCount middle inner (0, 0) sigma sourceHorizon := by
        simp only [boundaryExcursionCount, profileCompletedCount, middle, inner,
          profileOuterBoundary, profileInnerBoundary,
          trajectoryFrom_zero_eq_trajectory]
        simp only [Nat.add_sub_cancel]
      _ = q := rfl
  refine ⟨candidate, hcylinder, hactualExit, hhorizon, ?_⟩
  simpa only [data, sourceSplitCompletionData, splitCompletionDataAt,
    words, horizon, middle, inner, q] using hcount

/-- Re-extracting the canonical assembled packet associated with a source
candidate recovers the source's own compressed return data.  This is kept in
source-clock coordinates so later code recovery does not normalize the whole
dependent `SplitCompletionData` structure at once. -/
theorem sourceCandidateCanonicalReturnData
    {start n k : ℕ} {x y : Point} {source : StepPath}
    (hn : 1 ≤ n) (hk : k + 1 ≤ n)
    (hy : y ∈ candidateBox n)
    (hexit : IsOuterExitTime
      (trajectory (shiftSteps start source)) n
      (stoppedOuterExitHorizon start n source))
    (candidate : (j : Fin
      (sourceSplitCompletionData start n k x y source).returnCount) →
      SignatureCompatibleReturnCode x y (profileInnerBoundary n k y)
        (sourceSplitCompletionData start n k x y source) j) :
    let sourceHorizon := stoppedOuterExitHorizon start n source
    let sigma := shiftSteps start source
    let middle := profileInnerBoundary n k y
    let inner := profileInnerBoundary n (k + 1) y
    let q := boundaryExcursionCount middle inner (0, 0) sigma sourceHorizon
    let t := extractTimedReturnSkeleton sigma (0, 0) middle inner sourceHorizon q
    let code := compressTimedSkeleton sigma t
    let bridges := sourceCandidateBoundaryCodes candidate
    let words : TerminalSegmentWords q :=
      fun j ↦ List.ofFn (bridges j).1.2
    let newT := extractTimedReturnSkeleton
      (assembledTerminalPath code words) (0, 0) middle inner
      (assembledTerminalHorizon code words) q
    compressTimedSkeleton (assembledTerminalPath code words) newT = code ∧
      intervalWords (assembledTerminalPath code words)
        newT.entrance newT.exit = words := by
  exact compressedReturnData_assembled_of_boundaryExitWordCodes
    (sourceReturnComplete hn hk hy hexit)
    (sourceCandidateBoundaryCodes candidate)

/-- Every path in the retained completion atom re-extracts the literal
source code. -/
theorem sourceSplitCompletionData_recovered
    {start n k : ℕ} {x y : Point} {source : StepPath}
    (hn : 2 ≤ n) (hk : k + 1 ≤ n)
    (hy : y ∈ candidateBox n)
    (hexit : IsOuterExitTime
      (trajectory (shiftSteps start source)) n
      (stoppedOuterExitHorizon start n source)) :
    (splitCompletionAtomOfData (x := x) (y := y)
      (profileInnerBoundary n k y)
      (discBoundary (0, 0) (outerScale n)) (0, 0)
      (sourceSplitCompletionData start n k x y source)
      (sourceSplitCompletionGlobalFirst (by omega) hk hy hexit)).event ⊆
      {omega | splitCompletionDataAt start n k x y omega =
        sourceSplitCompletionData start n k x y source} := by
  intro omega homega
  change splitCompletionDataAt start n k x y omega =
    sourceSplitCompletionData start n k x y source
  have hcore := sourceSplitCompletionMemberCore hn hk hy hexit omega homega
  unfold SourceSplitCompletionMemberCore at hcore
  obtain ⟨candidate, hcylinder, hactualExit, hhorizon, hcount⟩ := hcore
  let data := sourceSplitCompletionData start n k x y source
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
      (by omega) hk hy hactualExit
    exact returnComplete_of_boundaryExcursionCount_eq hcount h
  have htail : shiftSteps start omega ∈
      stoppedWordCylinder (assembledTerminalWord data.skeleton words) := by
    exact
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
  let sourceHorizon := stoppedOuterExitHorizon start n source
  let sigma := shiftSteps start source
  let sourceQ := boundaryExcursionCount middle inner (0, 0) sigma sourceHorizon
  have hcompleteSource : ∀ j : Fin sourceQ,
      excursionStart (trajectory sigma) middle inner sourceHorizon (j + 1) ≤
        sourceHorizon := sourceReturnComplete (by omega) hk hy hexit
  have hcanonicalSource := sourceCandidateCanonicalReturnData
    (by omega) hk hy hexit candidate
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
        (XProfileScanSignature n x (actualT.entrancePoint j)
            (intervalWords (shiftSteps start omega)
              actualT.entrance actualT.exit j),
          XProfileScanSignature n y (actualT.entrancePoint j)
            (intervalWords (shiftSteps start omega)
              actualT.entrance actualT.exit j))) = data.signature := by
    funext j
    apply Prod.ext
    · rw [hentrancePoint j, congrFun hwordsData j]
      exact (candidate j).2.1
    · rw [hentrancePoint j, congrFun hwordsData j]
      exact (candidate j).2.2
  have hskelHeq := heq_of_eq_same_type hskelData
  have hsignatureHeq := heq_of_eq_same_type hsignature
  let actualData : SplitCompletionData start n :=
    { returnCount := data.returnCount
      pre := stepPrefix start omega
      skeleton := compressTimedSkeleton (shiftSteps start omega) actualT
      signature := fun j ↦
        (XProfileScanSignature n x (actualT.entrancePoint j)
            (intervalWords (shiftSteps start omega)
              actualT.entrance actualT.exit j),
          XProfileScanSignature n y (actualT.entrancePoint j)
            (intervalWords (shiftSteps start omega)
              actualT.entrance actualT.exit j)) }
  have hactualExtracted :
      splitCompletionDataAt start n k x y omega = actualData := by
    unfold splitCompletionDataAt
    dsimp only
    rw [hhorizon, hcount]
  have hactualData : actualData = data := by
    apply splitCompletionData_eq_of_fields
    · rfl
    · exact hpre
    · exact hskelHeq
    · exact hsignatureHeq
  exact hactualExtracted.trans hactualData

end

end Erdos1165.AsymmetricSplitCompletionRecovered
