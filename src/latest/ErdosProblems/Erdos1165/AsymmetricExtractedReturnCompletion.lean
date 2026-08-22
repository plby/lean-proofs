/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/
import ErdosProblems.Erdos1165.AsymmetricSplitCompletionPreservation
import ErdosProblems.Erdos1165.TerminalSkeletonFactorization

/-!
# Genuine completion atoms for an extracted asymmetric return skeleton

The split-level extractor retains the complementary pieces of the actual
stopped word and varies only the deleted inner-to-middle return words.  This
file packages that literal reconstruction as a `ComplementarySkeletonAtom`.
Its compatible version uses the universal `x`-scanner transition predicate,
so compatibility is chronological and does not depend on a stored incoming
scanner state.

The complement word remains only a mass bookkeeping word.  The genuine
retained completion event is the insertion event itself; no identification
with the complement cylinder is made.
-/

open MeasureTheory Set
open scoped ENNReal

namespace Erdos1165.AsymmetricExtractedReturnCompletion

open AsymmetricSplitCompletionPreservation
open AsymmetricSplitLevelSplice MarkedBridgeFactorization
open AlternatingConcatPrefixFree ThickPoint
open TerminalExcursionPathwise TerminalSequentialVisitLaw
open TerminalGlobalExitSplice TerminalProfileClockEquivalence
open AnnularProfileClocks
open TerminalSkeletonFactorization TerminalSkeletonInvariance
open TerminalSkeletonWords

noncomputable section

attribute [local instance] Classical.propDecidable

/-- Arbitrary-boundary version of the terminal insertion atom.  The fixed
compressed skeleton stores all complementary pieces and both endpoints;
only canonical first-hit return words are variable. -/
def boundaryReturnCompletionAtom
    {start m : ℕ} (code : TerminalSkeletonCode m)
    (returnBoundary globalBoundary : Set Point) (globalStart : Point)
    (hfirst : ∀ bridges : (j : Fin m) →
        BoundaryExitWordCode returnBoundary (code.2.1 j) (code.2.2 j),
      AbsoluteBoundaryFirstAt globalBoundary globalStart
        (assembledTerminalPath code (fun j ↦ List.ofFn (bridges j).1.2))
        (assembledTerminalHorizon code
          (fun j ↦ List.ofFn (bridges j).1.2))) :
    ComplementarySkeletonAtom m (Fin start → Direction)
      (fun j ↦ BoundaryExitWordCode returnBoundary
        (code.2.1 j) (code.2.2 j)) where
  complementWord := fun pre ↦ retainedTerminalWord pre code
  bridgeWord := fun _ bridge ↦ bridge.1
  assemble := fun c ↦ assembleAfterPrefix c.1 code
    (fun j ↦ List.ofFn (c.2 j).1.2)
  prefixFree_assemble :=
    prefixFree_assembleAfterPrefix_of_tailFirstAt code
      (fun j ↦ BoundaryExitWordCode returnBoundary
        (code.2.1 j) (code.2.2 j))
      (fun _ bridge ↦ List.ofFn bridge.1.2)
      (fun j ↦ by
        simpa only [listStoppedWord_ofFn] using
          (prefixFree_boundaryExitWordCode returnBoundary
            (code.2.1 j) (code.2.2 j)))
      globalBoundary globalStart hfirst
  prefixFree_bridge := fun j ↦
    prefixFree_boundaryExitWordCode returnBoundary
      (code.2.1 j) (code.2.2 j)
  length_assemble := by
    rintro ⟨pre, bridges⟩
    rw [assembleAfterPrefix_length_eq]
    rw [retainedTerminalWord, assembleAfterPrefix_length_eq]
    simp only [emptyTerminalWords, List.length_nil, Finset.sum_const_zero,
      add_zero, List.length_ofFn]

/-- Restrict an extracted return completion by equality of the transition
on every `x` profile scanner. -/
def xCompatibleBoundaryReturnCompletionAtom
    {start m n : ℕ} {x : Point} (code : TerminalSkeletonCode m)
    (returnBoundary globalBoundary : Set Point) (globalStart : Point)
    (source : (j : Fin m) → BoundaryExitWordCode returnBoundary
      (code.2.1 j) (code.2.2 j))
    (hfirst : ∀ bridges : (j : Fin m) →
        BoundaryExitWordCode returnBoundary (code.2.1 j) (code.2.2 j),
      AbsoluteBoundaryFirstAt globalBoundary globalStart
        (assembledTerminalPath code (fun j ↦ List.ofFn (bridges j).1.2))
        (assembledTerminalHorizon code
          (fun j ↦ List.ofFn (bridges j).1.2))) :=
  restrictBridges
    (boundaryReturnCompletionAtom (start := start) code returnBoundary
      globalBoundary globalStart hfirst)
    (fun j candidate ↦ XProfileScanCompatible n x (code.2.1 j)
      (List.ofFn (source j).1.2) (List.ofFn candidate.1.2))

/-- The actual extracted return tuple belongs to its universal-compatible
completion atom.  This is the exact reconstruction/source-coverage step;
it uses the full stopped prefix rather than a synthetic retained cylinder. -/
theorem source_mem_xCompatible_extractedReturnCompletionAtom
    {start m n horizon : ℕ} {x pathStart : Point}
    {middle inner globalBoundary : Set Point} {globalStart : Point}
    {omega : StepPath}
    (hcomplete : ∀ j : Fin m,
      excursionStart (PlanarPotential.trajectoryFrom pathStart
          (shiftSteps start omega)) middle inner horizon (j + 1) ≤ horizon)
    (hfirst : ∀ bridges : (j : Fin m) →
        BoundaryExitWordCode middle
          ((compressTimedSkeleton (shiftSteps start omega)
            (extractTimedReturnSkeleton (shiftSteps start omega) pathStart
              middle inner horizon m)).2.1 j)
          ((compressTimedSkeleton (shiftSteps start omega)
            (extractTimedReturnSkeleton (shiftSteps start omega) pathStart
              middle inner horizon m)).2.2 j),
      AbsoluteBoundaryFirstAt globalBoundary globalStart
        (assembledTerminalPath
          (compressTimedSkeleton (shiftSteps start omega)
            (extractTimedReturnSkeleton (shiftSteps start omega) pathStart
              middle inner horizon m))
          (fun j ↦ List.ofFn (bridges j).1.2))
        (assembledTerminalHorizon
          (compressTimedSkeleton (shiftSteps start omega)
            (extractTimedReturnSkeleton (shiftSteps start omega) pathStart
              middle inner horizon m))
          (fun j ↦ List.ofFn (bridges j).1.2))) :
    omega ∈ (xCompatibleBoundaryReturnCompletionAtom
      (start := start) (n := n) (x := x)
      (compressTimedSkeleton (shiftSteps start omega)
        (extractTimedReturnSkeleton (shiftSteps start omega) pathStart
          middle inner horizon m))
      middle globalBoundary globalStart
      (extractedReturnCodes hcomplete) hfirst).event := by
  let t := extractTimedReturnSkeleton (shiftSteps start omega) pathStart
    middle inner horizon m
  let code := compressTimedSkeleton (shiftSteps start omega) t
  let source := extractedReturnCodes hcomplete
  have ht : t.WellFormed := extractTimedReturnSkeleton_wellFormed hcomplete
  have hcylinder : omega ∈ stoppedWordCylinder
      (assembleAfterPrefix (stepPrefix start omega) code
        (fun j ↦ List.ofFn (source j).1.2)) := by
    have hsourceWords : (fun j ↦ List.ofFn (source j).1.2) =
        intervalWords (shiftSteps start omega) t.entrance t.exit := by
      funext j
      exact extractedReturnCodes_toList hcomplete j
    rw [hsourceWords]
    exact mem_stoppedWordCylinder_assembleAfterPrefix_packetOfTimedSkeleton
      omega t ht
  rw [ComplementarySkeletonAtom.event, stoppedWordEvent]
  apply Set.mem_iUnion.mpr
  refine ⟨(stepPrefix start omega, fun j ↦
    ⟨source j, xProfileScanCompatible_self n x (code.2.1 j)
      (List.ofFn (source j).1.2)⟩), ?_⟩
  exact hcylinder

/-- The universal compatibility subtype is exactly the pathwise hypothesis
needed to preserve the complete `x` profile through the extracted
alternating reconstruction. -/
theorem excursionProfile_assembled_eq_of_xCompatibleReturnCodes
    {n m : ℕ} (hn : 2 ≤ n) {x : Point}
    {omega : StepPath} {t : TimedTerminalSkeleton m}
    (ht : t.WellFormed) (returnBoundary : Set Point)
    (source : (j : Fin m) → BoundaryExitWordCode returnBoundary
      (trajectory omega (t.entrance j))
      (trajectory omega (t.exit j)))
    (hsource : ∀ j, List.ofFn (source j).1.2 =
      intervalWords omega t.entrance t.exit j)
    (candidate : (j : Fin m) →
      {b : BoundaryExitWordCode returnBoundary
          (trajectory omega (t.entrance j))
          (trajectory omega (t.exit j)) //
        XProfileScanCompatible n x (trajectory omega (t.entrance j))
          (List.ofFn (source j).1.2) (List.ofFn b.1.2)}) :
    excursionProfile
        (wordWalk (0, 0)
          (alternatingConcat m
            (complementaryPieces m omega 0 t.horizon t.entrance t.exit)
            (fun j ↦ List.ofFn (source j).1.2))) n
        (alternatingConcat m
          (complementaryPieces m omega 0 t.horizon t.entrance t.exit)
          (fun j ↦ List.ofFn (source j).1.2)).length x =
      excursionProfile
        (wordWalk (0, 0)
          (alternatingConcat m
            (complementaryPieces m omega 0 t.horizon t.entrance t.exit)
            (fun j ↦ List.ofFn (candidate j).1.1.2))) n
        (alternatingConcat m
          (complementaryPieces m omega 0 t.horizon t.entrance t.exit)
          (fun j ↦ List.ofFn (candidate j).1.1.2)).length x := by
  let geometry := extracted_endpointGeometry_of_boundaryExitWordCodes
    omega t ht returnBoundary (fun j ↦ (candidate j).1)
  have hsourceWords : (fun j ↦ List.ofFn (source j).1.2) =
      intervalWords omega t.entrance t.exit := by
    funext j
    exact hsource j
  rw [hsourceWords]
  apply excursionProfile_alternatingConcat_eq_of_xProfileScanCompatible
    hn geometry
  intro j
  rw [extracted_endpointGeometry_of_boundaryExitWordCodes_wordStart,
    ← hsource j]
  exact (candidate j).2

/-- Canonical first-hit return codes in a profile disc automatically supply
the confinement and endpoint fields of the global-exit splice theorem. -/
theorem isOuterExitTime_assembled_profileReturnCodes
    {m n k : ℕ} {omega : StepPath} {y : Point}
    {t : TimedTerminalSkeleton m}
    (hn : 1 ≤ n) (hk : k ≤ n) (hy : y ∈ candidateBox n)
    (ht : t.WellFormed)
    (hexit : IsOuterExitTime (trajectory omega) n t.horizon)
    (hentrancePoint : ∀ j,
      t.entrancePoint j = trajectory omega (t.entrance j))
    (hexitPoint : ∀ j,
      t.exitPoint j = trajectory omega (t.exit j))
    (hstart : ∀ j, t.entrancePoint j ∈ disc y (scaleRadius n k))
    (bridges : (j : Fin m) → BoundaryExitWordCode
      (profileInnerBoundary n k y) (t.entrancePoint j) (t.exitPoint j)) :
    IsOuterExitTime
      (wordWalk (trajectory omega 0)
        (alternatingConcat m
          (complementaryPieces m omega 0 t.horizon t.entrance t.exit)
          (fun j ↦ List.ofFn (bridges j).1.2))) n
      (alternatingConcat m
        (complementaryPieces m omega 0 t.horizon t.entrance t.exit)
        (fun j ↦ List.ofFn (bridges j).1.2)).length := by
  apply isOuterExitTime_alternatingConcat_complementaryPieces_profileDisc
    hn hk hy ht hexit hentrancePoint hexitPoint
  · intro j
    simpa [profileInnerBoundary, discBoundary] using
      (boundaryExitWordCode_wordWithin_and_endpoint (hstart j)
        (bridges j)).1
  · intro j
    exact boundaryExitWordCode_wordEndpoint (bridges j)

/-- Cylinder/shift wrapper for the pathwise preservation lemmas.  Once each
compatible assembled tail has the source `x` success property, the complete
compatible insertion event is a subset of the stopped `Γ_x` event. -/
theorem xCompatibleBoundaryReturnCompletionAtom_subset_stoppedSuccessfulPointEvent
    {start m n : ℕ} {profileDelta : ℝ} {x : Point}
    (code : TerminalSkeletonCode m)
    (returnBoundary globalBoundary : Set Point) (globalStart : Point)
    (source : (j : Fin m) → BoundaryExitWordCode returnBoundary
      (code.2.1 j) (code.2.2 j))
    (hfirst : ∀ bridges : (j : Fin m) →
        BoundaryExitWordCode returnBoundary (code.2.1 j) (code.2.2 j),
      AbsoluteBoundaryFirstAt globalBoundary globalStart
        (assembledTerminalPath code (fun j ↦ List.ofFn (bridges j).1.2))
        (assembledTerminalHorizon code
          (fun j ↦ List.ofFn (bridges j).1.2)))
    (hsuccess : ∀ candidate : (j : Fin m) →
        {b : BoundaryExitWordCode returnBoundary
            (code.2.1 j) (code.2.2 j) //
          XProfileScanCompatible n x (code.2.1 j)
            (List.ofFn (source j).1.2) (List.ofFn b.1.2)},
      let words : TerminalSegmentWords m :=
        fun j ↦ List.ofFn (candidate j).1.1.2
      IsOuterExitTime (trajectory (assembledTerminalPath code words)) n
          (assembledTerminalHorizon code words) ∧
        SuccessfulPoint (trajectory (assembledTerminalPath code words)) n
          (assembledTerminalHorizon code words) profileDelta x) :
    (xCompatibleBoundaryReturnCompletionAtom
      (start := start) (n := n) (x := x) code returnBoundary
      globalBoundary globalStart source hfirst).event ⊆
      Proposition13Assembly.stoppedSuccessfulPointEvent
        start n profileDelta x := by
  intro omega homega
  change ∃ horizon,
    IsOuterExitTime (trajectory (shiftSteps start omega)) n horizon ∧
      SuccessfulPoint (trajectory (shiftSteps start omega)) n horizon
        profileDelta x
  rw [ComplementarySkeletonAtom.event, stoppedWordEvent] at homega
  obtain ⟨candidateCode, hcylinder⟩ := Set.mem_iUnion.mp homega
  let candidate := candidateCode.2
  let words : TerminalSegmentWords m :=
    fun j ↦ List.ofFn (candidate j).1.1.2
  let horizon := assembledTerminalHorizon code words
  have htail : shiftSteps start omega ∈
      stoppedWordCylinder (assembledTerminalWord code words) := by
    exact
      TerminalSkeletonFactorization.shiftSteps_mem_assembledTerminalWordCylinder_of_mem_assembleAfterPrefix
        hcylinder
  have hcanonical := hsuccess candidate
  have htrajectory : ∀ q ≤ horizon,
      trajectory (shiftSteps start omega) q =
        trajectory (assembledTerminalPath code words) q := by
    intro q hq
    exact trajectory_eq_assembledTerminalPath_of_mem_stoppedWordCylinder
      htail hq
  refine ⟨horizon, ?_, ?_⟩
  · constructor
    · rw [htrajectory horizon le_rfl]
      exact hcanonical.1.1
    · intro q hq
      rw [htrajectory q hq.le]
      exact hcanonical.1.2 q hq
  · refine ⟨hcanonical.2.1, ?_⟩
    rw [Proposition13Measurability.excursionProfile_congr_prefix
      htrajectory x]
    exact hcanonical.2.2

end

end Erdos1165.AsymmetricExtractedReturnCompletion
