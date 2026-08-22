/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/
import ErdosProblems.Erdos1165.AsymmetricSplitCompletionRecovered

/-!
# Valid source witnesses for asymmetric split completion

An actual stopped successful pair indexes a valid retained completion atom.
The left profile is preserved by the recorded scanner transition, while the
right profile is used only to certify the literal source and the split return
count.
-/

open Set

namespace Erdos1165.AsymmetricSplitCompletionWitness

open AnnularBoundaryExcursionKernel AnnularProfileClocks
open AsymmetricReturnPrefixRecovery
open AsymmetricSplitCompletionCode AsymmetricSplitCompletionRecovered
open AsymmetricSplitCompletionSource AsymmetricSplitLevelSplice
open AsymmetricSplitCompletionPreservation
open Proposition13Assembly SharedPrefixPairExtraction
open MarkedBridgeFactorization
open TerminalSkeletonFactorization TerminalSkeletonInvariance
open TerminalSkeletonWords ThickPoint

noncomputable section

attribute [local instance] Classical.propDecidable

/-- The scanner-compatible completion atom extracted from a source in
`Γ_x` remains inside `Γ_x`. -/
theorem sourceSplitCompletionAtom_subset_stoppedSuccessfulPointEvent
    {start n k : ℕ} {profileDelta : ℝ} {x y : Point} {source : StepPath}
    (hn : 2 ≤ n) (hk : k + 1 ≤ n)
    (hy : y ∈ candidateBox n)
    (hexit : IsOuterExitTime (trajectory (shiftSteps start source)) n
      (stoppedOuterExitHorizon start n source))
    (hsourceX : source ∈ stoppedSuccessfulPointEvent
      start n profileDelta x) :
    (splitCompletionAtomOfData (x := x) (y := y)
      (profileInnerBoundary n k y)
      (discBoundary (0, 0) (outerScale n)) (0, 0)
      (sourceSplitCompletionData start n k x y source)
      (sourceSplitCompletionGlobalFirst (by omega) hk hy hexit)).event ⊆
      stoppedSuccessfulPointEvent start n profileDelta x := by
  intro omega homega
  have hcore := sourceSplitCompletionMemberCore hn hk hy hexit omega homega
  unfold SourceSplitCompletionMemberCore at hcore
  obtain ⟨candidate, hcylinder, hactualExit, _hhorizon, _hcount⟩ := hcore
  let data := sourceSplitCompletionData start n k x y source
  let words : TerminalSegmentWords data.returnCount :=
    fun j ↦ List.ofFn (candidate j).1.1.2
  let horizon := assembledTerminalHorizon data.skeleton words
  have htail : shiftSteps start omega ∈
      stoppedWordCylinder (assembledTerminalWord data.skeleton words) :=
    TerminalSkeletonFactorization.shiftSteps_mem_assembledTerminalWordCylinder_of_mem_assembleAfterPrefix
      hcylinder
  have htrajectory : ∀ r ≤ horizon,
      trajectory (shiftSteps start omega) r =
        trajectory (assembledTerminalPath data.skeleton words) r := by
    intro r hr
    exact trajectory_eq_assembledTerminalPath_of_mem_stoppedWordCylinder
      htail hr
  let sourceHorizon := stoppedOuterExitHorizon start n source
  let sigma := shiftSteps start source
  let middle := profileInnerBoundary n k y
  let inner := profileInnerBoundary n (k + 1) y
  let q := boundaryExcursionCount middle inner (0, 0) sigma sourceHorizon
  have hcompleteSource : ∀ j : Fin q,
      excursionStart (trajectory sigma) middle inner sourceHorizon (j + 1) ≤
        sourceHorizon := sourceReturnComplete (by omega) hk hy hexit
  let xCandidate : (j : Fin q) →
      ExtractedCompatibleReturnCandidate n x sigma middle inner
        sourceHorizon q j := fun j ↦ ⟨(candidate j).1, by
    rw [xProfileScanCompatible_iff_signature_eq]
    have hsig := (candidate j).2.1.symm
    simpa only [data, sourceSplitCompletionData, splitCompletionDataAt,
      compressTimedSkeleton_entrancePoint] using hsig⟩
  have hprofileCanonicalSource :
      excursionProfile
          (trajectory (assembledTerminalPath data.skeleton words)) n horizon x =
        excursionProfile (trajectory sigma) n sourceHorizon x := by
    simpa only [data, sourceSplitCompletionData, splitCompletionDataAt,
      words, horizon] using
      (sourceCandidateProfile_eq hn hcompleteSource xCandidate)
  obtain ⟨sourceHorizon', hsourceExit, hsourceSuccessful⟩ := hsourceX
  change IsOuterExitTime (trajectory (shiftSteps start source)) n
    sourceHorizon' at hsourceExit
  change SuccessfulPoint (trajectory (shiftSteps start source)) n
    sourceHorizon' profileDelta x at hsourceSuccessful
  have hsourceHorizon : sourceHorizon' = sourceHorizon := by
    exact isOuterExitTime_unique hsourceExit hexit
  subst sourceHorizon'
  refine ⟨horizon, hactualExit, ?_⟩
  refine ⟨hsourceSuccessful.1, ?_⟩
  change SuccessfulProfile n profileDelta
    (excursionProfile (trajectory (shiftSteps start omega)) n horizon x)
  rw [Proposition13Measurability.excursionProfile_congr_prefix htrajectory x]
  rw [hprofileCanonicalSource]
  simpa only [sigma] using hsourceSuccessful.2

/-- The literal source data carries all three validity fields required by a
countable split-completion code. -/
def sourceSplitCompletionWitness
    {start n k : ℕ} {profileDelta : ℝ} {x y : Point} {source : StepPath}
    (hn : 2 ≤ n) (hk : k + 1 ≤ n)
    (hy : y ∈ candidateBox n)
    (hexit : IsOuterExitTime (trajectory (shiftSteps start source)) n
      (stoppedOuterExitHorizon start n source))
    (hsourceX : source ∈ stoppedSuccessfulPointEvent
      start n profileDelta x) :
    SplitCompletionWitness (k := k) (profileDelta := profileDelta) x y
      (profileInnerBoundary n k y)
      (discBoundary (0, 0) (outerScale n)) (0, 0)
      (sourceSplitCompletionData start n k x y source) where
  globalFirst := sourceSplitCompletionGlobalFirst (by omega) hk hy hexit
  gammaX := sourceSplitCompletionAtom_subset_stoppedSuccessfulPointEvent
    hn hk hy hexit hsourceX
  recovered := sourceSplitCompletionData_recovered hn hk hy hexit

/-- The valid retained code canonically indexed by one stopped pair source. -/
def sourceSplitCompletionCode
    {start n k : ℕ} {profileDelta : ℝ} {x y : Point} {source : StepPath}
    (hn : 2 ≤ n) (hk : k + 1 ≤ n)
    (hy : y ∈ candidateBox n)
    (hexit : IsOuterExitTime (trajectory (shiftSteps start source)) n
      (stoppedOuterExitHorizon start n source))
    (hsourceX : source ∈ stoppedSuccessfulPointEvent
      start n profileDelta x) :
    SplitCompletionCode start n k profileDelta x y
      (profileInnerBoundary n k y)
      (discBoundary (0, 0) (outerScale n)) (0, 0) :=
  ⟨sourceSplitCompletionData start n k x y source,
    sourceSplitCompletionWitness hn hk hy hexit hsourceX⟩

/-- Every stopped successful pair is covered by its own valid retained
completion atom. -/
theorem stoppedSuccessfulPairEvent_subset_iUnion_retainedAtom
    {start n k : ℕ} {profileDelta : ℝ} {x y : Point}
    (hn : 2 ≤ n) (hk : k + 1 ≤ n) :
    stoppedSuccessfulPairEvent start n profileDelta x y ⊆
      ⋃ code : SplitCompletionCode start n k profileDelta x y
          (profileInnerBoundary n k y)
          (discBoundary (0, 0) (outerScale n)) (0, 0),
        retainedAtom code := by
  rintro source ⟨hsourceX, hsourceY⟩
  obtain ⟨horizon, hexit, hsuccessfulY⟩ := hsourceY
  have hhorizon : stoppedOuterExitHorizon start n source = horizon :=
    stoppedOuterExitHorizon_eq_of_isOuterExitTime hexit
  have hexitStopped : IsOuterExitTime
      (trajectory (shiftSteps start source)) n
      (stoppedOuterExitHorizon start n source) := by
    simpa only [Proposition13Measurability.shiftedWalk, hhorizon] using hexit
  let code := sourceSplitCompletionCode hn hk hsuccessfulY.1
    hexitStopped hsourceX
  apply Set.mem_iUnion.mpr
  refine ⟨code, ?_⟩
  unfold retainedAtom code sourceSplitCompletionCode
  exact source_mem_splitCompletionDataAtomAt (by omega) hk
    hsuccessfulY.1 hexitStopped

end

end Erdos1165.AsymmetricSplitCompletionWitness
