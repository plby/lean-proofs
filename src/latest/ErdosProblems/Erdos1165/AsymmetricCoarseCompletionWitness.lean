/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/
import ErdosProblems.Erdos1165.AsymmetricCoarseCompletionSourceGeometry
import ErdosProblems.Erdos1165.BufferedStoppedSuccessfulPointEvent

/-!
# Valid coarse asymmetric completion witnesses

The coarse atom records exactly the left prefix signature through the
separation scale.  The extracted endpoint theorem therefore keeps the
whole atom inside the literal left successful event while leaving the
strictly deeper right coordinates free.
-/

open Set

namespace Erdos1165.AsymmetricCoarseCompletionWitness

open AnnularProfileClocks AppendixPair
open AsymmetricCoarseCompletionSourceGeometry
open AsymmetricCoarseSplitCompletion AsymmetricCoarseSplitCompletionSource
open AsymmetricExtractedReturnClockRecovery AsymmetricReturnPrefixRecovery
open AsymmetricSplitCompletionSource AsymmetricSplitLevelSplice
open AnnularProfileLiteralAtoms
open BufferedStoppedSuccessfulPointEvent BufferedSuccessfulProfile
open MarkedBridgeFactorization Proposition13Assembly
open TerminalGlobalExitSplice TerminalSkeletonFactorization
open TerminalSkeletonInvariance TerminalSkeletonWords ThickPoint
open TerminalSequentialVisitLaw

noncomputable section

attribute [local instance] Classical.propDecidable

/-- The actual source's coarse completion atom is contained in its left
successful event. -/
theorem sourceCoarseSplitCompletionAtom_subset_stoppedSuccessfulPointEvent_of_separation_le
    {start n k : ℕ} {profileDelta : ℝ} {x y : Point} {source : StepPath}
    (hn : 2 ≤ n) (hk : k + 1 ≤ n)
    (hy : y ∈ candidateBox n)
    (hexit : IsOuterExitTime (trajectory (shiftSteps start source)) n
      (stoppedOuterExitHorizon start n source))
    (hseparation : separationLevel n x y ≤ k) (hlevel : k ≤ n)
    (hseparationThree : 3 ≤ separationLevel n x y)
    (hsourceX : source ∈ stoppedSuccessfulPointEvent
      start n profileDelta x) :
    (sourceCoarseSplitCompletionAtom (x := x) (y := y)
      source (Nat.one_le_of_lt hn) hk hy hexit).event ⊆
      stoppedBufferedSuccessfulPointEvent start n
        (separationLevel n x y - 3) (separationLevel n x y + 1)
        profileDelta x := by
  intro omega homega
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
      (assembledTerminalPath data.skeleton words) horizon := by
    exact sourceCoarseSplitCompletionGlobalFirst
      (Nat.one_le_of_lt hn) hk hy hexit (fun j ↦ (candidate j).1)
  have hactualFirst : AbsoluteBoundaryFirstAt
      (discBoundary (0, 0) (outerScale n)) (0, 0)
      (shiftSteps start omega) horizon :=
    absoluteBoundaryFirstAt_of_mem_stoppedWordCylinder
      htail hcanonicalFirst
  have hactualExit : IsOuterExitTime
      (trajectory (shiftSteps start omega)) n horizon := by
    simpa only [AbsoluteBoundaryFirstAt, IsOuterExitTime,
      trajectoryFrom_zero_eq_trajectory] using hactualFirst
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
        (assembledTerminalWord data.skeleton referenceWords) := by
    exact TerminalSkeletonFactorization.shiftSteps_mem_assembledTerminalWordCylinder_of_mem_assembleAfterPrefix
      hsourceCylinder
  have hreferenceFirst : AbsoluteBoundaryFirstAt
      (discBoundary (0, 0) (outerScale n)) (0, 0)
      (assembledTerminalPath data.skeleton referenceWords)
      referenceHorizon := by
    exact sourceCoarseSplitCompletionGlobalFirst
      (Nat.one_le_of_lt hn) hk hy hexit (fun j ↦ (reference j).1)
  have hreferenceExit : IsOuterExitTime
      (trajectory (assembledTerminalPath data.skeleton referenceWords)) n
      referenceHorizon := by
    simpa only [AbsoluteBoundaryFirstAt, IsOuterExitTime,
      trajectoryFrom_zero_eq_trajectory] using hreferenceFirst
  have hsourceReferenceTrajectory : ∀ r ≤ referenceHorizon,
      trajectory (shiftSteps start source) r =
        trajectory (assembledTerminalPath data.skeleton referenceWords) r := by
    intro r hr
    exact trajectory_eq_assembledTerminalPath_of_mem_stoppedWordCylinder
      hsourceTail hr
  have hsourceExitAtReference : IsOuterExitTime
      (trajectory (shiftSteps start source)) n referenceHorizon := by
    have hfirst := absoluteBoundaryFirstAt_of_mem_stoppedWordCylinder
      hsourceTail hreferenceFirst
    simpa only [referenceHorizon, assembledTerminalHorizon,
      AbsoluteBoundaryFirstAt, IsOuterExitTime,
      trajectoryFrom_zero_eq_trajectory] using hfirst
  have hreferenceHorizon :
      referenceHorizon = stoppedOuterExitHorizon start n source :=
    isOuterExitTime_unique hsourceExitAtReference hexit
  have hreferenceProfileSource :
      excursionProfile
          (trajectory (assembledTerminalPath data.skeleton referenceWords)) n
          referenceHorizon x =
        excursionProfile (trajectory (shiftSteps start source)) n
          (stoppedOuterExitHorizon start n source) x := by
    rw [← hreferenceHorizon]
    exact (Proposition13Measurability.excursionProfile_congr_prefix
      hsourceReferenceTrajectory x).symm
  have hreferenceCandidateProfile : ∀ scale : Fin (n + 2),
      RetainedCoordinate
          (separationLevel n x y - 3) (separationLevel n x y + 1) scale.1 →
        excursionProfile
            (trajectory (assembledTerminalPath data.skeleton referenceWords)) n
            referenceHorizon x scale =
          excursionProfile
            (trajectory (assembledTerminalPath data.skeleton words)) n
            horizon x scale := by
    simpa only [data, words, horizon, reference, referenceWords,
      referenceHorizon] using
      (sourceCoarseReferenceCandidate_profile_eq_of_separation_le
        hn hk hy hexit hseparation hlevel candidate)
  have hreferenceCandidateProfileTwo : ∀ scale : Fin (n + 2),
      RetainedCoordinate
          (separationLevel n x y - 2) (separationLevel n x y + 1) scale.1 →
        excursionProfile
            (trajectory (assembledTerminalPath data.skeleton referenceWords)) n
            referenceHorizon x scale =
          excursionProfile
            (trajectory (assembledTerminalPath data.skeleton words)) n
            horizon x scale := by
    simpa only [data, words, horizon, reference, referenceWords,
      referenceHorizon] using
      (sourceCoarseReferenceCandidate_profile_eq_of_separation_le_twoBuffer
        hn hk hy hexit hseparation hlevel hseparationThree candidate)
  obtain ⟨sourceHorizon, hsourceExit, hsourceSuccessful⟩ := hsourceX
  have hsourceHorizon :
      sourceHorizon = stoppedOuterExitHorizon start n source :=
    isOuterExitTime_unique hsourceExit hexit
  subst sourceHorizon
  have hactualSourceProfile : ∀ scale : Fin (n + 2),
      RetainedCoordinate
          (separationLevel n x y - 3) (separationLevel n x y + 1) scale.1 →
        excursionProfile (trajectory (shiftSteps start omega)) n horizon x scale =
          excursionProfile (trajectory (shiftSteps start source)) n
            (stoppedOuterExitHorizon start n source) x scale := by
    intro scale hretained
    rw [Proposition13Measurability.excursionProfile_congr_prefix
      hactualTrajectory x]
    exact (hreferenceCandidateProfile scale hretained).symm.trans
      (congrFun hreferenceProfileSource scale)
  have hactualSourceProfileTwo : ∀ scale : Fin (n + 2),
      RetainedCoordinate
          (separationLevel n x y - 2) (separationLevel n x y + 1) scale.1 →
        excursionProfile (trajectory (shiftSteps start omega)) n horizon x scale =
          excursionProfile (trajectory (shiftSteps start source)) n
            (stoppedOuterExitHorizon start n source) x scale := by
    intro scale hretained
    rw [Proposition13Measurability.excursionProfile_congr_prefix
      hactualTrajectory x]
    exact (hreferenceCandidateProfileTwo scale hretained).symm.trans
      (congrFun hreferenceProfileSource scale)
  by_cases hseparationFour : 4 ≤ separationLevel n x y
  · rw [mem_stoppedBufferedSuccessfulPointEvent_iff (by omega)]
    refine ⟨horizon, hactualExit, hsourceSuccessful.1, ?_⟩
    refine congr_retained (by omega)
      (of_successfulProfile hsourceSuccessful.2) ?_
    exact hactualSourceProfile
  · have hseparationEq : separationLevel n x y = 3 := by omega
    let actualN := excursionProfile
      (trajectory (shiftSteps start omega)) n horizon x
    have hactualBuffered :
        IsBufferedSuccessfulProfile n 0 4 profileDelta actualN := by
      apply congr_retained (by omega)
        (of_successfulProfile hsourceSuccessful.2)
      intro scale hretained
      exact hactualSourceProfile scale (by simpa [hseparationEq] using hretained)
    have hactualOne : actualN ⟨1, by omega⟩ = 1 := by
      dsimp only [actualN]
      rw [hactualSourceProfileTwo ⟨1, by omega⟩ (by
        left
        simp [hseparationEq])]
      exact hsourceSuccessful.2.1
    suffices omega ∈ stoppedBufferedSuccessfulPointEvent
        start n 0 4 profileDelta x by
      simpa [hseparationEq] using this
    unfold stoppedBufferedSuccessfulPointEvent
    apply Set.mem_iUnion.mpr
    refine ⟨⟨internalProfile actualN,
      internalProfile_isBuffered hactualBuffered⟩, ?_⟩
    unfold stoppedFixedProfileEvent
    apply Set.mem_iUnion.mpr
    refine ⟨horizon, ?_⟩
    change IsOuterExitTime (trajectory (shiftSteps start omega)) n horizon ∧
      x ∈ candidateBox n ∧
      FixedSuccessfulProfile n profileDelta (internalProfile actualN) actualN
    exact ⟨hactualExit, hsourceSuccessful.1,
      hactualOne, (fun _ ↦ rfl), hactualBuffered.2.2⟩

/-- Equality-level wrapper for the original geometric split. -/
theorem sourceCoarseSplitCompletionAtom_subset_stoppedSuccessfulPointEvent
    {start n k : ℕ} {profileDelta : ℝ} {x y : Point} {source : StepPath}
    (hn : 2 ≤ n) (hk : k + 1 ≤ n)
    (hy : y ∈ candidateBox n)
    (hexit : IsOuterExitTime (trajectory (shiftSteps start source)) n
      (stoppedOuterExitHorizon start n source))
    (hseparation : k = separationLevel n x y) (hlevel : k ≤ n)
    (hseparationThree : 3 ≤ k)
    (hsourceX : source ∈ stoppedSuccessfulPointEvent
      start n profileDelta x) :
    (sourceCoarseSplitCompletionAtom (x := x) (y := y)
      source (Nat.one_le_of_lt hn) hk hy hexit).event ⊆
      stoppedBufferedSuccessfulPointEvent start n (k - 3) (k + 1)
        profileDelta x := by
  subst k
  apply
    sourceCoarseSplitCompletionAtom_subset_stoppedSuccessfulPointEvent_of_separation_le
      hn hk hy hexit (by omega) (by omega) hseparationThree hsourceX

end

end Erdos1165.AsymmetricCoarseCompletionWitness
