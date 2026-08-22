/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/
import ErdosProblems.Erdos1165.AnnularRecursiveProfileSourceSegment
import ErdosProblems.Erdos1165.AnnularRecursiveProfileEndpointTail
import ErdosProblems.Erdos1165.AsymmetricCoarseSuccessfulTailAtoms

/-!
# Recursive source codes carried by successful coarse return tuples

A successful tuple over a genuine coarse completion atom is itself a
canonical stopped source.  The recovery field of the coarse code therefore
identifies its bridge count with the actual completed profile count at the
first free right-hand scale.  This is the index equality needed before each
literal bridge can be parsed by the recursive profile source parser.
-/

open Set

namespace Erdos1165.AsymmetricCoarseRecursiveSourceCode

open AnnularBoundaryExcursionKernel AnnularProfileClocks
open AnnularOffspringKernelRadial
open AnnularProfileChildWordIdentification AnnularProfileLevelSkeleton
open AnnularProfileGapAtoms AnnularProfileLiteralAtoms
open AnnularLiteralNestedProfileTailUpper
open AnnularRecursiveDecoratedProfileCode
open AnnularRecursiveProfileActualCode AnnularRecursiveProfileActualParser
open AnnularRecursiveProfileCodeAssembly AnnularRecursiveProfileShape
open AnnularRecursiveProfileEndpointTail AnnularRecursiveProfileSourceRecovery
open AnnularRecursiveProfileSourceSegment
open AlternatingConcatPrefixFree
open AppendixFirstMoment ProfileListExponent
open AsymmetricCoarseCompletionCode AsymmetricCoarseSplitCompletion
open AsymmetricCoarseSuccessfulTailAtoms
open AsymmetricExtractedReturnClockRecovery
open AsymmetricExtractedReturnCompletion AsymmetricPairTwoStageMass
open AsymmetricReturnPrefixRecovery
open AsymmetricSplitCompletionRecovered
open AsymmetricSplitCompletionSource AsymmetricSplitLevelSplice
open MarkedBridgeFactorization PlanarPotential Proposition13Assembly
open ProfileGapChain
open TerminalGlobalExitSplice TerminalSkeletonFactorization
open TerminalSequentialVisitLaw TerminalSkeletonInvariance
open TerminalSkeletonWords ThickPoint

noncomputable section

attribute [local instance] Classical.propDecidable

/-- The full canonical stopped source obtained by putting the fixed pre-prefix
back in front of a successful assembled terminal tail. -/
def coarseSuccessfulCanonicalSource
    {start n k : ℕ} {hk : k + 1 ≤ n} {profileDelta : ℝ}
    {x y : Point}
    (code : CoarseSplitCompletionCode start n k hk profileDelta x y
      (profileInnerBoundary n k y)
      (discBoundary (0, 0) (outerScale n)) (0, 0))
    (tail : CoarseSuccessfulReturnTuple code) : StepPath :=
  extendStoppedWord ((coarseAtom code).assemble (Unit.unit, tail.1))

/-- The canonical full source lies in the successful fine cylinder that
defined it. -/
theorem coarseSuccessfulCanonicalSource_mem_tailAtom
    {start n k : ℕ} {hk : k + 1 ≤ n} {profileDelta : ℝ}
    {x y : Point}
    (code : CoarseSplitCompletionCode start n k hk profileDelta x y
      (profileInnerBoundary n k y)
      (discBoundary (0, 0) (outerScale n)) (0, 0))
    (tail : CoarseSuccessfulReturnTuple code) :
    coarseSuccessfulCanonicalSource code tail ∈
      coarseSuccessfulTailAtom code tail := by
  unfold coarseSuccessfulCanonicalSource coarseSuccessfulTailAtom
  exact stepPrefix_extendStoppedWord _

/-- Removing the fixed pre-prefix from the canonical full source exposes the
same terminal stopped cylinder as the assembled successful tail. -/
theorem shift_coarseSuccessfulCanonicalSource_mem_terminalCylinder
    {start n k : ℕ} {hk : k + 1 ≤ n} {profileDelta : ℝ}
    {x y : Point}
    (code : CoarseSplitCompletionCode start n k hk profileDelta x y
      (profileInnerBoundary n k y)
      (discBoundary (0, 0) (outerScale n)) (0, 0))
    (tail : CoarseSuccessfulReturnTuple code) :
    shiftSteps start (coarseSuccessfulCanonicalSource code tail) ∈
      stoppedWordCylinder
        (assembledTerminalWord code.1.skeleton
          (coarseTupleWords code tail.1)) := by
  apply TerminalSkeletonFactorization.shiftSteps_mem_assembledTerminalWordCylinder_of_mem_assembleAfterPrefix
  change stepPrefix
      ((coarseAtom code).assemble (Unit.unit, tail.1)).1
        (coarseSuccessfulCanonicalSource code tail) =
      ((coarseAtom code).assemble (Unit.unit, tail.1)).2
  unfold coarseSuccessfulCanonicalSource
  exact stepPrefix_extendStoppedWord _

/-- The bridge-coordinate count of a successful coarse tuple is the actual
profile count at the first free right-hand scale. -/
theorem coarseSuccessfulReturnCount_eq_profileAtScale
    {start n k : ℕ} {hk : k + 1 ≤ n} {profileDelta : ℝ}
    {x y : Point} (hkTwo : 2 ≤ k + 1)
    (code : CoarseSplitCompletionCode start n k hk profileDelta x y
      (profileInnerBoundary n k y)
      (discBoundary (0, 0) (outerScale n)) (0, 0))
    (tail : CoarseSuccessfulReturnTuple code) :
    code.1.returnCount =
      profileAtScale
        (internalProfile (excursionProfile
          (trajectory (assembledTerminalPath code.1.skeleton
            (coarseTupleWords code tail.1))) n
          (assembledTerminalHorizon code.1.skeleton
            (coarseTupleWords code tail.1)) y)) (k + 1) := by
  let words : TerminalSegmentWords code.1.returnCount :=
    coarseTupleWords code tail.1
  let horizon := assembledTerminalHorizon code.1.skeleton words
  let assembled := assembledTerminalPath code.1.skeleton words
  let source := coarseSuccessfulCanonicalSource code tail
  have hsourceTail : shiftSteps start source ∈
      stoppedWordCylinder (assembledTerminalWord code.1.skeleton words) := by
    simpa only [source, words] using
      shift_coarseSuccessfulCanonicalSource_mem_terminalCylinder code tail
  have htrajectory : ∀ q ≤ horizon,
      trajectory (shiftSteps start source) q = trajectory assembled q := by
    intro q hq
    exact trajectory_eq_assembledTerminalPath_of_mem_stoppedWordCylinder
      hsourceTail hq
  have hfirst : AbsoluteBoundaryFirstAt
      (discBoundary (0, 0) (outerScale n)) (0, 0) assembled horizon := by
    exact code.2.globalFirst (fun j ↦ (tail.1 j).1)
  have hsourceFirst : AbsoluteBoundaryFirstAt
      (discBoundary (0, 0) (outerScale n)) (0, 0)
      (shiftSteps start source) horizon :=
    absoluteBoundaryFirstAt_of_mem_stoppedWordCylinder hsourceTail hfirst
  have hsourceExit : IsOuterExitTime
      (trajectory (shiftSteps start source)) n horizon := by
    simpa only [AbsoluteBoundaryFirstAt, IsOuterExitTime,
      trajectoryFrom_zero_eq_trajectory] using hsourceFirst
  have hhorizon : stoppedOuterExitHorizon start n source = horizon :=
    stoppedOuterExitHorizon_eq_of_isOuterExitTime hsourceExit
  have hsourceCoarse : source ∈ coarseRetainedAtom code :=
    coarseSuccessfulTailAtom_subset_coarseRetainedAtom code tail
      (coarseSuccessfulCanonicalSource_mem_tailAtom code tail)
  have hdata := code.2.recovered hsourceCoarse
  have hcountSource := congrArg
    (fun data : CoarseSplitCompletionData start n k ↦ data.returnCount) hdata
  have hcountSource' :
      boundaryExcursionCount
          (profileInnerBoundary n k y) (profileInnerBoundary n (k + 1) y)
          (0, 0) (shiftSteps start source) horizon = code.1.returnCount := by
    simpa only [sourceCoarseSplitCompletionData,
      coarsenSplitCompletionData, sourceSplitCompletionData_returnCount,
      hhorizon] using hcountSource
  have hcountCongr :
      completedExcursionCount (trajectory (shiftSteps start source))
          (profileOuterBoundary n (k + 1) y)
          (profileInnerBoundary n (k + 1) y) horizon =
        completedExcursionCount (trajectory assembled)
          (profileOuterBoundary n (k + 1) y)
          (profileInnerBoundary n (k + 1) y) horizon :=
    Proposition13Measurability.completedExcursionCount_congr_prefix
      htrajectory _ _
  have hcountAssembled :
      profileCompletedCount (trajectory assembled) n horizon y (k + 1) =
        code.1.returnCount := by
    rw [profileCompletedCount]
    rw [← hcountCongr]
    simpa only [boundaryExcursionCount, profileOuterBoundary,
      profileInnerBoundary, Nat.add_sub_cancel,
      trajectoryFrom_zero_eq_trajectory] using
        hcountSource'
  have hfixed : FixedSuccessfulProfile n profileDelta
      (internalProfile (excursionProfile (trajectory assembled) n horizon y))
      (excursionProfile (trajectory assembled) n horizon y) :=
    fixedSuccessfulProfile_internalProfile tail.2.2
  have hprofile := profileCompletedCount_eq_profileAtScale hkTwo hk hfixed
  have hresult := hcountAssembled.symm.trans hprofile
  simpa only [assembled, horizon, words] using hresult

/-- Re-extracting the split clock from the successful assembled tail recovers
both the coarse skeleton and the literal bridge word at every coordinate. -/
theorem coarseSuccessfulReturnData_recovered
    {start n k : ℕ} {hk : k + 1 ≤ n} {profileDelta : ℝ}
    {x y : Point} (hn : 2 ≤ n)
    (code : CoarseSplitCompletionCode start n k hk profileDelta x y
      (profileInnerBoundary n k y)
      (discBoundary (0, 0) (outerScale n)) (0, 0))
    (tail : CoarseSuccessfulReturnTuple code) :
    let words : TerminalSegmentWords code.1.returnCount :=
      coarseTupleWords code tail.1
    let horizon := assembledTerminalHorizon code.1.skeleton words
    let assembled := assembledTerminalPath code.1.skeleton words
    let actualT := extractTimedReturnSkeleton assembled (0, 0)
      (profileInnerBoundary n k y) (profileInnerBoundary n (k + 1) y)
      horizon code.1.returnCount
    compressTimedSkeleton assembled actualT = code.1.skeleton ∧
      intervalWords assembled actualT.entrance actualT.exit = words := by
  dsimp only
  let words : TerminalSegmentWords code.1.returnCount :=
    coarseTupleWords code tail.1
  let horizon := assembledTerminalHorizon code.1.skeleton words
  let assembled := assembledTerminalPath code.1.skeleton words
  let source := coarseSuccessfulCanonicalSource code tail
  have hsourceTail : shiftSteps start source ∈
      stoppedWordCylinder (assembledTerminalWord code.1.skeleton words) := by
    simpa only [source, words] using
      shift_coarseSuccessfulCanonicalSource_mem_terminalCylinder code tail
  have hfirst : AbsoluteBoundaryFirstAt
      (discBoundary (0, 0) (outerScale n)) (0, 0) assembled horizon := by
    exact code.2.globalFirst (fun j ↦ (tail.1 j).1)
  have hsourceFirst : AbsoluteBoundaryFirstAt
      (discBoundary (0, 0) (outerScale n)) (0, 0)
      (shiftSteps start source) horizon :=
    absoluteBoundaryFirstAt_of_mem_stoppedWordCylinder hsourceTail hfirst
  have hsourceExit : IsOuterExitTime
      (trajectory (shiftSteps start source)) n horizon := by
    simpa only [AbsoluteBoundaryFirstAt, IsOuterExitTime,
      trajectoryFrom_zero_eq_trajectory] using hsourceFirst
  have hhorizon : stoppedOuterExitHorizon start n source = horizon :=
    stoppedOuterExitHorizon_eq_of_isOuterExitTime hsourceExit
  have hsourceCoarse : source ∈ coarseRetainedAtom code :=
    coarseSuccessfulTailAtom_subset_coarseRetainedAtom code tail
      (coarseSuccessfulCanonicalSource_mem_tailAtom code tail)
  have hdata := code.2.recovered hsourceCoarse
  have hcountSource := congrArg
    (fun data : CoarseSplitCompletionData start n k ↦ data.returnCount) hdata
  have hcountSource' :
      boundaryExcursionCount
          (profileInnerBoundary n k y) (profileInnerBoundary n (k + 1) y)
          (0, 0) (shiftSteps start source) horizon = code.1.returnCount := by
    simpa only [sourceCoarseSplitCompletionData,
      coarsenSplitCompletionData, sourceSplitCompletionData_returnCount,
      hhorizon] using hcountSource
  have hcompleteActual : ∀ j : Fin code.1.returnCount,
      excursionStart (trajectory (shiftSteps start source))
        (profileInnerBoundary n k y) (profileInnerBoundary n (k + 1) y)
        horizon (j + 1) ≤ horizon := by
    apply returnComplete_of_boundaryExcursionCount_eq hcountSource'
    exact sourceReturnComplete (Nat.one_le_of_lt hn) hk tail.2.1 hsourceExit
  let sourceT := extractTimedReturnSkeleton (shiftSteps start source) (0, 0)
    (profileInnerBoundary n k y) (profileInnerBoundary n (k + 1) y)
    horizon code.1.returnCount
  have hdataPack := congrArg
    (fun data : CoarseSplitCompletionData start n k ↦
      (⟨data.returnCount, data.skeleton⟩ :
        Σ q : ℕ, TerminalSkeletonCode q)) hdata
  have hdataSkeleton : HEq
      (sourceCoarseSplitCompletionData start n k hk x y source).skeleton
        code.1.skeleton :=
    (Sigma.ext_iff.mp hdataPack).2
  have hsourcePack :
      (⟨(sourceCoarseSplitCompletionData start n k hk x y source).returnCount,
          (sourceCoarseSplitCompletionData start n k hk x y source).skeleton⟩ :
        Σ q : ℕ, TerminalSkeletonCode q) =
      ⟨code.1.returnCount,
        compressTimedSkeleton (shiftSteps start source) sourceT⟩ := by
    calc
      _ = ⟨boundaryExcursionCount
              (profileInnerBoundary n k y) (profileInnerBoundary n (k + 1) y)
              (0, 0) (shiftSteps start source) horizon,
            compressTimedSkeleton (shiftSteps start source)
              (extractTimedReturnSkeleton (shiftSteps start source) (0, 0)
                (profileInnerBoundary n k y) (profileInnerBoundary n (k + 1) y)
                horizon
                (boundaryExcursionCount
                  (profileInnerBoundary n k y) (profileInnerBoundary n (k + 1) y)
                  (0, 0) (shiftSteps start source) horizon))⟩ := by
          simp only [sourceCoarseSplitCompletionData,
            coarsenSplitCompletionData, sourceSplitCompletionData_returnCount,
            sourceSplitCompletionData_skeleton]
          rw [hhorizon]
      _ = _ := by
        simpa only [sourceT] using congrArg
          (fun q : ℕ ↦ (⟨q,
            compressTimedSkeleton (shiftSteps start source)
              (extractTimedReturnSkeleton (shiftSteps start source) (0, 0)
                (profileInnerBoundary n k y) (profileInnerBoundary n (k + 1) y)
                horizon q)⟩ : Σ r : ℕ, TerminalSkeletonCode r))
          hcountSource'
  have hskelSource :
      compressTimedSkeleton (shiftSteps start source) sourceT =
        code.1.skeleton := by
    exact eq_of_heq
      (Sigma.ext_iff.mp (hsourcePack.symm.trans hdataPack)).2
  let bridges : (j : Fin code.1.returnCount) →
      BoundaryExitWordCode (profileInnerBoundary n k y)
        (trajectory (shiftSteps start source) (sourceT.entrance j))
        (trajectory (shiftSteps start source) (sourceT.exit j)) := fun j ↦ by
    refine ⟨(tail.1 j).1.1, ?_, ?_⟩
    · have hentrance := congrArg
        (fun skeleton : TerminalSkeletonCode code.1.returnCount ↦
          skeleton.2.1 j) hskelSource
      simp only [compressTimedSkeleton_entrancePoint, sourceT,
        extractTimedReturnSkeleton_entrancePoint_apply] at hentrance
      rw [hentrance]
      exact (tail.1 j).1.2.1
    · have hexit := congrArg
        (fun skeleton : TerminalSkeletonCode code.1.returnCount ↦
          skeleton.2.2 j) hskelSource
      have hentrance := congrArg
        (fun skeleton : TerminalSkeletonCode code.1.returnCount ↦
          skeleton.2.1 j) hskelSource
      simp only [compressTimedSkeleton_entrancePoint,
        compressTimedSkeleton_exitPoint, sourceT,
        extractTimedReturnSkeleton_entrancePoint_apply,
        extractTimedReturnSkeleton_exitPoint_apply] at hentrance hexit
      rw [hentrance, hexit]
      exact (tail.1 j).1.2.2
  have hrecovered := compressedReturnData_assembled_of_boundaryExitWordCodes
    hcompleteActual bridges
  have hbridgeWords :
      (fun j : Fin code.1.returnCount ↦ List.ofFn (bridges j).1.2) = words := by
    funext j
    rfl
  dsimp only at hrecovered
  dsimp only [sourceT] at hskelSource
  rw [hbridgeWords, hskelSource] at hrecovered
  simpa only [assembled, horizon, words] using hrecovered

/-- The generic split-level extractor at the pair of consecutive profile
boundaries cuts out exactly the stopped profile-gap word at the deeper
scale. -/
theorem intervalWords_extractTimedReturnSkeleton_eq_profileGapStoppedWord
    (omega : StepPath) (n horizon : ℕ) (y : Point) (k q : ℕ)
    (j : Fin q) :
    let t := extractTimedReturnSkeleton omega (0, 0)
      (profileInnerBoundary n k y) (profileInnerBoundary n (k + 1) y)
      horizon q
    intervalWords omega t.entrance t.exit j =
      List.ofFn (profileGapStoppedWord omega n horizon y (k + 1) j).2 := by
  simp only [intervalWords, extractTimedReturnSkeleton,
    profileGapStoppedWord_toList, returnEntranceTime, returnExitTime,
    profileInnerHitTime, profileGapExitTime, profileOuterHitTime,
    profileOuterBoundary, profileInnerBoundary,
    trajectoryFrom_zero_eq_trajectory,
    Nat.add_sub_cancel]

/-- Every retained coarse bridge is literally the actual profile-gap list
of the canonically assembled successful path. -/
theorem coarseSuccessfulBridgeList_eq_profileGapStoppedWord
    {start n k : ℕ} {hk : k + 1 ≤ n} {profileDelta : ℝ}
    {x y : Point} (hn : 2 ≤ n)
    (code : CoarseSplitCompletionCode start n k hk profileDelta x y
      (profileInnerBoundary n k y)
      (discBoundary (0, 0) (outerScale n)) (0, 0))
    (tail : CoarseSuccessfulReturnTuple code)
    (j : Fin code.1.returnCount) :
    List.ofFn (tail.1 j).1.1.2 =
      List.ofFn
        (profileGapStoppedWord
          (assembledTerminalPath code.1.skeleton
            (coarseTupleWords code tail.1)) n
          (assembledTerminalHorizon code.1.skeleton
            (coarseTupleWords code tail.1)) y (k + 1) j).2 := by
  let words : TerminalSegmentWords code.1.returnCount :=
    coarseTupleWords code tail.1
  let horizon := assembledTerminalHorizon code.1.skeleton words
  let assembled := assembledTerminalPath code.1.skeleton words
  let actualT := extractTimedReturnSkeleton assembled (0, 0)
    (profileInnerBoundary n k y) (profileInnerBoundary n (k + 1) y)
    horizon code.1.returnCount
  have hrecovered := coarseSuccessfulReturnData_recovered hn code tail
  dsimp only at hrecovered
  have hj := congrFun hrecovered.2 j
  have hgap :=
    intervalWords_extractTimedReturnSkeleton_eq_profileGapStoppedWord
      assembled n horizon y k code.1.returnCount j
  have hwords : words j =
      List.ofFn (profileGapStoppedWord assembled n horizon y (k + 1) j).2 :=
    hj.symm.trans (by simpa only [actualT] using hgap)
  simpa only [assembled, horizon, words, coarseTupleWords] using hwords

/-- The preceding list identity determines the dependent stopped-word
package itself. -/
theorem coarseSuccessfulBridge_eq_profileGapStoppedWord
    {start n k : ℕ} {hk : k + 1 ≤ n} {profileDelta : ℝ}
    {x y : Point} (hn : 2 ≤ n)
    (code : CoarseSplitCompletionCode start n k hk profileDelta x y
      (profileInnerBoundary n k y)
      (discBoundary (0, 0) (outerScale n)) (0, 0))
    (tail : CoarseSuccessfulReturnTuple code)
    (j : Fin code.1.returnCount) :
    (tail.1 j).1.1 =
      profileGapStoppedWord
        (assembledTerminalPath code.1.skeleton
          (coarseTupleWords code tail.1)) n
        (assembledTerminalHorizon code.1.skeleton
          (coarseTupleWords code tail.1)) y (k + 1) j := by
  let left : StoppedWord := (tail.1 j).1.1
  let right : StoppedWord :=
    profileGapStoppedWord
      (assembledTerminalPath code.1.skeleton
        (coarseTupleWords code tail.1)) n
      (assembledTerminalHorizon code.1.skeleton
        (coarseTupleWords code tail.1)) y (k + 1) j
  have hlists : List.ofFn left.2 = List.ofFn right.2 := by
    simpa only [left, right] using
      coarseSuccessfulBridgeList_eq_profileGapStoppedWord hn code tail j
  calc
    left = listStoppedWord (List.ofFn left.2) :=
      (listStoppedWord_ofFn left).symm
    _ = listStoppedWord (List.ofFn right.2) := congrArg listStoppedWord hlists
    _ = right := listStoppedWord_ofFn right

/-! ## The canonical recursive parser attached to a successful tail -/

/-- The full constrained profile carried by a successful assembled tail. -/
def coarseSuccessfulProfile
    {start n k : ℕ} {hk : k + 1 ≤ n} {profileDelta : ℝ}
    {x y : Point}
    (code : CoarseSplitCompletionCode start n k hk profileDelta x y
      (profileInnerBoundary n k y)
      (discBoundary (0, 0) (outerScale n)) (0, 0))
    (tail : CoarseSuccessfulReturnTuple code) : Profile n :=
  internalProfile (excursionProfile
    (trajectory (assembledTerminalPath code.1.skeleton
      (coarseTupleWords code tail.1))) n
    (assembledTerminalHorizon code.1.skeleton
      (coarseTupleWords code tail.1)) y)

/-- The free recursive suffix after the first retained right-hand count. -/
def coarseSuccessfulProfileRest
    {start n k : ℕ} {hk : k + 1 ≤ n} {profileDelta : ℝ}
    {x y : Point}
    (code : CoarseSplitCompletionCode start n k hk profileDelta x y
      (profileInnerBoundary n k y)
      (discBoundary (0, 0) (outerScale n)) (0, 0))
    (tail : CoarseSuccessfulReturnTuple code) : List ℕ :=
  (profileSegmentValues (coarseSuccessfulProfile code tail) (k + 1)).tail

/-- The recursive segment begins with exactly the number of bridge
coordinates stored by the coarse skeleton. -/
theorem coarseSuccessfulProfileSegment_eq
    {start n k : ℕ} {hk : k + 1 ≤ n} {profileDelta : ℝ}
    {x y : Point} (hkTwo : 2 ≤ k + 1)
    (code : CoarseSplitCompletionCode start n k hk profileDelta x y
      (profileInnerBoundary n k y)
      (discBoundary (0, 0) (outerScale n)) (0, 0))
    (tail : CoarseSuccessfulReturnTuple code) :
    profileSegmentValues (coarseSuccessfulProfile code tail) (k + 1) =
      code.1.returnCount :: coarseSuccessfulProfileRest code tail := by
  rw [profileSegmentValues_eq_head_cons_tail hk]
  have hcount : code.1.returnCount =
      profileAtScale (coarseSuccessfulProfile code tail) (k + 1) := by
    simpa only [coarseSuccessfulProfile] using
      coarseSuccessfulReturnCount_eq_profileAtScale hkTwo code tail
  rw [← hcount]
  rfl

/-- The assembled successful tail has the common global outer-exit clock. -/
theorem coarseSuccessfulAssembled_isOuterExitTime
    {start n k : ℕ} {hk : k + 1 ≤ n} {profileDelta : ℝ}
    {x y : Point}
    (code : CoarseSplitCompletionCode start n k hk profileDelta x y
      (profileInnerBoundary n k y)
      (discBoundary (0, 0) (outerScale n)) (0, 0))
    (tail : CoarseSuccessfulReturnTuple code) :
    IsOuterExitTime
      (trajectory (assembledTerminalPath code.1.skeleton
        (coarseTupleWords code tail.1))) n
      (assembledTerminalHorizon code.1.skeleton
        (coarseTupleWords code tail.1)) := by
  have hfirst := code.2.globalFirst (fun j ↦ (tail.1 j).1)
  change AbsoluteBoundaryFirstAt
    (discBoundary (0, 0) (outerScale n)) (0, 0)
    (assembledTerminalPath code.1.skeleton (coarseTupleWords code tail.1))
    (assembledTerminalHorizon code.1.skeleton (coarseTupleWords code tail.1))
      at hfirst
  simpa only [AbsoluteBoundaryFirstAt, IsOuterExitTime,
    trajectoryFrom_zero_eq_trajectory] using hfirst

/-- Canonical actual recursive segment data for a successful coarse tail. -/
def coarseSuccessfulProfileSegmentData
    {start n k : ℕ} {hk : k + 1 ≤ n} {profileDelta : ℝ}
    {x y : Point} (hn : 2 ≤ n) (hkTwo : 2 ≤ k + 1)
    (hdelta : profileDelta ≤ 1)
    (code : CoarseSplitCompletionCode start n k hk profileDelta x y
      (profileInnerBoundary n k y)
      (discBoundary (0, 0) (outerScale n)) (0, 0))
    (tail : CoarseSuccessfulReturnTuple code) :
    ActualProfileSegmentData
      (assembledTerminalPath code.1.skeleton (coarseTupleWords code tail.1))
      n
      (assembledTerminalHorizon code.1.skeleton (coarseTupleWords code tail.1))
      y (k + 1)
      (code.1.returnCount :: coarseSuccessfulProfileRest code tail) := by
  let raw := actualProfileSegmentDataOfSuccessfulPoint hn hkTwo hk hdelta
    (coarseSuccessfulAssembled_isOuterExitTime code tail) tail.2
  rw [← coarseSuccessfulProfileSegment_eq hkTwo code tail]
  exact raw

/-- The remaining count list fits exactly in the physical depth below
`k+1`. -/
theorem coarseSuccessfulProfileRest_depth
    {start n k : ℕ} {hk : k + 1 ≤ n} {profileDelta : ℝ}
    {x y : Point} (hkTwo : 2 ≤ k + 1)
    (code : CoarseSplitCompletionCode start n k hk profileDelta x y
      (profileInnerBoundary n k y)
      (discBoundary (0, 0) (outerScale n)) (0, 0))
    (tail : CoarseSuccessfulReturnTuple code) :
    k + 1 + (coarseSuccessfulProfileRest code tail).length ≤ n := by
  have hlength := profileSegmentValues_length
    (coarseSuccessfulProfile code tail) (k + 1)
  rw [coarseSuccessfulProfileSegment_eq hkTwo code tail] at hlength
  simp only [List.length_cons] at hlength
  omega

/-- Actual top-level entrance vector for the recursive profile parser. -/
def coarseSuccessfulRecursiveEntrance
    {start n k : ℕ} {hk : k + 1 ≤ n} {profileDelta : ℝ}
    {x y : Point} (hn : 2 ≤ n) (hkTwo : 2 ≤ k + 1)
    (hdelta : profileDelta ≤ 1)
    (code : CoarseSplitCompletionCode start n k hk profileDelta x y
      (profileInnerBoundary n k y)
      (discBoundary (0, 0) (outerScale n)) (0, 0))
    (tail : CoarseSuccessfulReturnTuple code)
    (j : Fin code.1.returnCount) :
    ProfileCycleMiddlePoint n (k + 1) y := by
  let data := coarseSuccessfulProfileSegmentData hn hkTwo hdelta code tail
  exact ⟨profileGapStartPoint
      (assembledTerminalPath code.1.skeleton (coarseTupleWords code tail.1)) n
      (assembledTerminalHorizon code.1.skeleton (coarseTupleWords code tail.1))
      y (k + 1) j,
    RealDiscFinite.mem_discBoundaryFinset.mpr
      (profileGapStartPoint_mem_innerBoundary
        (data.headComplete j j.isLt))⟩

/-- Actual top-level retained endpoint vector for the recursive parser. -/
def coarseSuccessfulRecursiveEndpoint
    {start n k : ℕ} {hk : k + 1 ≤ n} {profileDelta : ℝ}
    {x y : Point} (hn : 2 ≤ n) (hkTwo : 2 ≤ k + 1)
    (hdelta : profileDelta ≤ 1)
    (code : CoarseSplitCompletionCode start n k hk profileDelta x y
      (profileInnerBoundary n k y)
      (discBoundary (0, 0) (outerScale n)) (0, 0))
    (tail : CoarseSuccessfulReturnTuple code)
    (j : Fin code.1.returnCount) :
    ProfileCycleOuterPoint n (k + 1) y := by
  let data := coarseSuccessfulProfileSegmentData hn hkTwo hdelta code tail
  exact ⟨profileGapExitPoint
      (assembledTerminalPath code.1.skeleton (coarseTupleWords code tail.1)) n
      (assembledTerminalHorizon code.1.skeleton (coarseTupleWords code tail.1))
      y (k + 1) j,
    RealDiscFinite.mem_discBoundaryFinset.mpr
      (profileGapExitPoint_mem_outerBoundary
        (data.headComplete j j.isLt))⟩

@[simp] theorem coarseSuccessfulRecursiveEntrance_val
    {start n k : ℕ} {hk : k + 1 ≤ n} {profileDelta : ℝ}
    {x y : Point} (hn : 2 ≤ n) (hkTwo : 2 ≤ k + 1)
    (hdelta : profileDelta ≤ 1)
    (code : CoarseSplitCompletionCode start n k hk profileDelta x y
      (profileInnerBoundary n k y)
      (discBoundary (0, 0) (outerScale n)) (0, 0))
    (tail : CoarseSuccessfulReturnTuple code)
    (j : Fin code.1.returnCount) :
    (coarseSuccessfulRecursiveEntrance hn hkTwo hdelta code tail j).1 =
      profileGapStartPoint
        (assembledTerminalPath code.1.skeleton (coarseTupleWords code tail.1)) n
        (assembledTerminalHorizon code.1.skeleton (coarseTupleWords code tail.1))
        y (k + 1) j := rfl

@[simp] theorem coarseSuccessfulRecursiveEndpoint_val
    {start n k : ℕ} {hk : k + 1 ≤ n} {profileDelta : ℝ}
    {x y : Point} (hn : 2 ≤ n) (hkTwo : 2 ≤ k + 1)
    (hdelta : profileDelta ≤ 1)
    (code : CoarseSplitCompletionCode start n k hk profileDelta x y
      (profileInnerBoundary n k y)
      (discBoundary (0, 0) (outerScale n)) (0, 0))
    (tail : CoarseSuccessfulReturnTuple code)
    (j : Fin code.1.returnCount) :
    (coarseSuccessfulRecursiveEndpoint hn hkTwo hdelta code tail j).1 =
      profileGapExitPoint
        (assembledTerminalPath code.1.skeleton (coarseTupleWords code tail.1)) n
        (assembledTerminalHorizon code.1.skeleton (coarseTupleWords code tail.1))
      y (k + 1) j := rfl

/-- The supported recursive entrance is already fixed by the retained coarse
skeleton. -/
theorem coarseSuccessfulRecursiveEntrance_eq_skeleton
    {start n k : ℕ} {hk : k + 1 ≤ n} {profileDelta : ℝ}
    {x y : Point} (hn : 2 ≤ n) (hkTwo : 2 ≤ k + 1)
    (hdelta : profileDelta ≤ 1)
    (code : CoarseSplitCompletionCode start n k hk profileDelta x y
      (profileInnerBoundary n k y)
      (discBoundary (0, 0) (outerScale n)) (0, 0))
    (tail : CoarseSuccessfulReturnTuple code)
    (j : Fin code.1.returnCount) :
    (coarseSuccessfulRecursiveEntrance hn hkTwo hdelta code tail j).1 =
      code.1.skeleton.2.1 j := by
  let words : TerminalSegmentWords code.1.returnCount :=
    coarseTupleWords code tail.1
  let horizon := assembledTerminalHorizon code.1.skeleton words
  let assembled := assembledTerminalPath code.1.skeleton words
  let actualT := extractTimedReturnSkeleton assembled (0, 0)
    (profileInnerBoundary n k y) (profileInnerBoundary n (k + 1) y)
    horizon code.1.returnCount
  have hskel : (compressTimedSkeleton assembled actualT).2.1 j =
      code.1.skeleton.2.1 j := congrArg
    (fun skeleton : TerminalSkeletonCode code.1.returnCount ↦
      skeleton.2.1 j)
    (coarseSuccessfulReturnData_recovered hn code tail).1
  change profileGapStartPoint assembled n horizon y (k + 1) j = _
  rw [show profileGapStartPoint assembled n horizon y (k + 1) j =
      actualT.entrancePoint j by
    simp only [actualT, profileGapStartPoint, profileInnerHitTime,
      extractTimedReturnSkeleton, returnEntrancePoint, returnEntranceTime,
      profileOuterBoundary, profileInnerBoundary,
      trajectoryFrom_zero_eq_trajectory, Nat.add_sub_cancel]]
  simpa only [compressTimedSkeleton_entrancePoint] using hskel

/-- The supported recursive endpoint is already fixed by the retained coarse
skeleton. -/
theorem coarseSuccessfulRecursiveEndpoint_eq_skeleton
    {start n k : ℕ} {hk : k + 1 ≤ n} {profileDelta : ℝ}
    {x y : Point} (hn : 2 ≤ n) (hkTwo : 2 ≤ k + 1)
    (hdelta : profileDelta ≤ 1)
    (code : CoarseSplitCompletionCode start n k hk profileDelta x y
      (profileInnerBoundary n k y)
      (discBoundary (0, 0) (outerScale n)) (0, 0))
    (tail : CoarseSuccessfulReturnTuple code)
    (j : Fin code.1.returnCount) :
    (coarseSuccessfulRecursiveEndpoint hn hkTwo hdelta code tail j).1 =
      code.1.skeleton.2.2 j := by
  let words : TerminalSegmentWords code.1.returnCount :=
    coarseTupleWords code tail.1
  let horizon := assembledTerminalHorizon code.1.skeleton words
  let assembled := assembledTerminalPath code.1.skeleton words
  let actualT := extractTimedReturnSkeleton assembled (0, 0)
    (profileInnerBoundary n k y) (profileInnerBoundary n (k + 1) y)
    horizon code.1.returnCount
  have hskel : (compressTimedSkeleton assembled actualT).2.2 j =
      code.1.skeleton.2.2 j := congrArg
    (fun skeleton : TerminalSkeletonCode code.1.returnCount ↦
      skeleton.2.2 j)
    (coarseSuccessfulReturnData_recovered hn code tail).1
  change profileGapExitPoint assembled n horizon y (k + 1) j = _
  rw [show profileGapExitPoint assembled n horizon y (k + 1) j =
      actualT.exitPoint j by
    simp only [actualT, profileGapExitPoint, profileGapExitTime,
      profileOuterHitTime, extractTimedReturnSkeleton, returnExitPoint,
      returnExitTime, profileOuterBoundary, profileInnerBoundary,
      trajectoryFrom_zero_eq_trajectory, Nat.add_sub_cancel]]
  simpa only [compressTimedSkeleton_exitPoint] using hskel

attribute [irreducible]
  coarseSuccessfulRecursiveEntrance coarseSuccessfulRecursiveEndpoint

/-- Canonical weak-composition genealogy read from the successful tail. -/
def coarseSuccessfulGapChain
    {start n k : ℕ} {hk : k + 1 ≤ n} {profileDelta : ℝ}
    {x y : Point} (hn : 2 ≤ n) (hkTwo : 2 ≤ k + 1)
    (hdelta : profileDelta ≤ 1)
    (code : CoarseSplitCompletionCode start n k hk profileDelta x y
      (profileInnerBoundary n k y)
      (discBoundary (0, 0) (outerScale n)) (0, 0))
    (tail : CoarseSuccessfulReturnTuple code) :
    GapChain (code.1.returnCount :: coarseSuccessfulProfileRest code tail) :=
  (coarseSuccessfulProfileSegmentData hn hkTwo hdelta code tail).gapChain
    hn tail.2.1 (by omega)
    (coarseSuccessfulProfileRest_depth hkTwo code tail)

/-- The literal recursive parser for one successful coarse bridge. -/
def coarseSuccessfulParsedProfileGap
    {start n k : ℕ} {hk : k + 1 ≤ n} {profileDelta : ℝ}
    {x y : Point} (hn : 2 ≤ n) (hkTwo : 2 ≤ k + 1)
    (hdelta : profileDelta ≤ 1)
    (code : CoarseSplitCompletionCode start n k hk profileDelta x y
      (profileInnerBoundary n k y)
      (discBoundary (0, 0) (outerScale n)) (0, 0))
    (tail : CoarseSuccessfulReturnTuple code)
    (j : Fin code.1.returnCount) :
    ActualParsedProfileGap n (k + 1) y
      (coarseSuccessfulRecursiveEntrance hn hkTwo hdelta code tail j)
      (coarseSuccessfulRecursiveEndpoint hn hkTwo hdelta code tail j) := by
  let data := coarseSuccessfulProfileSegmentData hn hkTwo hdelta code tail
  exact actualParsedProfileGap hn tail.2.1
    (coarseSuccessfulProfileRest code tail) (by omega)
    (coarseSuccessfulProfileRest_depth hkTwo code tail) data j
    (coarseSuccessfulRecursiveEntrance hn hkTwo hdelta code tail j)
    (coarseSuccessfulRecursiveEndpoint hn hkTwo hdelta code tail j)
    (coarseSuccessfulRecursiveEntrance_val hn hkTwo hdelta code tail j).symm
    (coarseSuccessfulRecursiveEndpoint_val hn hkTwo hdelta code tail j).symm

/-- The parsed tree is the canonical tree selected by the actual gap
chain. -/
theorem coarseSuccessfulParsedProfileGap_tree_eq
    {start n k : ℕ} {hk : k + 1 ≤ n} {profileDelta : ℝ}
    {x y : Point} (hn : 2 ≤ n) (hkTwo : 2 ≤ k + 1)
    (hdelta : profileDelta ≤ 1)
    (code : CoarseSplitCompletionCode start n k hk profileDelta x y
      (profileInnerBoundary n k y)
      (discBoundary (0, 0) (outerScale n)) (0, 0))
    (tail : CoarseSuccessfulReturnTuple code)
    (j : Fin code.1.returnCount) :
    (coarseSuccessfulParsedProfileGap hn hkTwo hdelta code tail j).tree =
      profileRefinementTrees code.1.returnCount
        (coarseSuccessfulProfileRest code tail)
        (coarseSuccessfulGapChain hn hkTwo hdelta code tail) j := by
  let data := coarseSuccessfulProfileSegmentData hn hkTwo hdelta code tail
  let entrance := coarseSuccessfulRecursiveEntrance
    hn hkTwo hdelta code tail j
  let endpoint := coarseSuccessfulRecursiveEndpoint
    hn hkTwo hdelta code tail j
  have htree := actualParsedProfileGap_tree hn tail.2.1
    (coarseSuccessfulProfileRest code tail) (by omega)
    (coarseSuccessfulProfileRest_depth hkTwo code tail) data j
    entrance endpoint
    (coarseSuccessfulRecursiveEntrance_val hn hkTwo hdelta code tail j).symm
    (coarseSuccessfulRecursiveEndpoint_val hn hkTwo hdelta code tail j).symm
  have hrefine := refinementTrees_eq_profileRefinementTrees hn tail.2.1
    (coarseSuccessfulProfileRest code tail) (by omega)
    (coarseSuccessfulProfileRest_depth hkTwo code tail) data j
  exact htree.trans (hrefine.trans (by rfl))

/-- The actual parsed tree satisfies the recursive assembler's physical
depth predicate. -/
theorem coarseSuccessfulParsedProfileGap_fits
    {start n k : ℕ} {hk : k + 1 ≤ n} {profileDelta : ℝ}
    {x y : Point} (hn : 2 ≤ n) (hkTwo : 2 ≤ k + 1)
    (hdelta : profileDelta ≤ 1)
    (code : CoarseSplitCompletionCode start n k hk profileDelta x y
      (profileInnerBoundary n k y)
      (discBoundary (0, 0) (outerScale n)) (0, 0))
    (tail : CoarseSuccessfulReturnTuple code)
    (j : Fin code.1.returnCount) :
    profileRefinementTreeFits n (k + 1)
      (coarseSuccessfulParsedProfileGap hn hkTwo hdelta code tail j).tree := by
  let data := coarseSuccessfulProfileSegmentData hn hkTwo hdelta code tail
  let entrance := coarseSuccessfulRecursiveEntrance
    hn hkTwo hdelta code tail j
  let endpoint := coarseSuccessfulRecursiveEndpoint
    hn hkTwo hdelta code tail j
  simpa only [coarseSuccessfulParsedProfileGap] using
    actualParsedProfileGap_fits hn tail.2.1
      (coarseSuccessfulProfileRest code tail) (by omega)
      (coarseSuccessfulProfileRest_depth hkTwo code tail) data j
      entrance endpoint
      (coarseSuccessfulRecursiveEntrance_val
        hn hkTwo hdelta code tail j).symm
      (coarseSuccessfulRecursiveEndpoint_val
        hn hkTwo hdelta code tail j).symm

/-- Reassembling the canonical recursive code gives exactly the retained
coarse bridge, not merely an event containing it. -/
theorem coarseSuccessfulRecursiveBoundaryCode_eq_bridge
    {start n k : ℕ} {hk : k + 1 ≤ n} {profileDelta : ℝ}
    {x y : Point} (hn : 2 ≤ n) (hkTwo : 2 ≤ k + 1)
    (hdelta : profileDelta ≤ 1)
    (code : CoarseSplitCompletionCode start n k hk profileDelta x y
      (profileInnerBoundary n k y)
      (discBoundary (0, 0) (outerScale n)) (0, 0))
    (tail : CoarseSuccessfulReturnTuple code)
    (j : Fin code.1.returnCount) :
    let parsed := coarseSuccessfulParsedProfileGap
      hn hkTwo hdelta code tail j
    (recursiveProfileGapBoundaryExitWordCode n (k + 1) y hn (by omega)
      parsed.tree
      (coarseSuccessfulParsedProfileGap_fits hn hkTwo hdelta code tail j)
      (coarseSuccessfulRecursiveEntrance hn hkTwo hdelta code tail j)
      (coarseSuccessfulRecursiveEndpoint hn hkTwo hdelta code tail j)
      parsed.code).1 = (tail.1 j).1.1 := by
  dsimp only
  let data := coarseSuccessfulProfileSegmentData hn hkTwo hdelta code tail
  let entrance := coarseSuccessfulRecursiveEntrance
    hn hkTwo hdelta code tail j
  let endpoint := coarseSuccessfulRecursiveEndpoint
    hn hkTwo hdelta code tail j
  have hsource := recursiveProfileGapBoundaryExitWordCode_actualParsed_eq
    hn tail.2.1 (coarseSuccessfulProfileRest code tail) (by omega)
    (coarseSuccessfulProfileRest_depth hkTwo code tail) data j
    entrance endpoint
    (coarseSuccessfulRecursiveEntrance_val hn hkTwo hdelta code tail j).symm
    (coarseSuccessfulRecursiveEndpoint_val hn hkTwo hdelta code tail j).symm
  exact hsource.trans
    (coarseSuccessfulBridge_eq_profileGapStoppedWord hn code tail j).symm

/-- Transport a recursive gap code along equality of its tree index. -/
def transportRecursiveProfileGapCode
    {n k : ℕ} {center : Point}
    {left right : ProfileRefinementTree}
    {u : ProfileCycleMiddlePoint n k center}
    {w : ProfileCycleOuterPoint n k center}
    (h : left = right)
    (code : RecursiveProfileGapCode n k center left u w) :
    RecursiveProfileGapCode n k center right u w :=
  h ▸ code

/-- Tree-index transport does not change the assembled boundary word. -/
theorem recursiveProfileGapBoundaryExitWordCode_transport
    {n k : ℕ} {center : Point} (hn : 2 ≤ n) (hk0 : 0 < k)
    {left right : ProfileRefinementTree}
    (h : left = right)
    (hleft : profileRefinementTreeFits n k left)
    (hright : profileRefinementTreeFits n k right)
    (u : ProfileCycleMiddlePoint n k center)
    (w : ProfileCycleOuterPoint n k center)
    (code : RecursiveProfileGapCode n k center left u w) :
    (recursiveProfileGapBoundaryExitWordCode n k center hn hk0 right hright
      u w (transportRecursiveProfileGapCode h code)).1 =
    (recursiveProfileGapBoundaryExitWordCode n k center hn hk0 left hleft
      u w code).1 := by
  subst right
  rfl

/-- The recursive product mass is likewise invariant under tree-index
transport. -/
theorem recursiveProfileGapCodeMass_transport
    {n k : ℕ} {center : Point}
    {left right : ProfileRefinementTree}
    (h : left = right)
    (u : ProfileCycleMiddlePoint n k center)
    (w : ProfileCycleOuterPoint n k center)
    (code : RecursiveProfileGapCode n k center left u w) :
    recursiveProfileGapCodeMass n k center right u w
        (transportRecursiveProfileGapCode h code) =
      recursiveProfileGapCodeMass n k center left u w code := by
  subst right
  rfl

/-- Transport the parser-produced code onto the canonical refinement tree
selected by the successful profile's weak-composition chain. -/
def coarseSuccessfulCanonicalRecursiveCode
    {start n k : ℕ} {hk : k + 1 ≤ n} {profileDelta : ℝ}
    {x y : Point} (hn : 2 ≤ n) (hkTwo : 2 ≤ k + 1)
    (hdelta : profileDelta ≤ 1)
    (code : CoarseSplitCompletionCode start n k hk profileDelta x y
      (profileInnerBoundary n k y)
      (discBoundary (0, 0) (outerScale n)) (0, 0))
    (tail : CoarseSuccessfulReturnTuple code)
    (j : Fin code.1.returnCount) :
    RecursiveProfileGapCode n (k + 1) y
      (profileRefinementTrees code.1.returnCount
        (coarseSuccessfulProfileRest code tail)
        (coarseSuccessfulGapChain hn hkTwo hdelta code tail) j)
      (coarseSuccessfulRecursiveEntrance hn hkTwo hdelta code tail j)
      (coarseSuccessfulRecursiveEndpoint hn hkTwo hdelta code tail j) := by
  let parsed := coarseSuccessfulParsedProfileGap
    hn hkTwo hdelta code tail j
  exact transportRecursiveProfileGapCode
    (coarseSuccessfulParsedProfileGap_tree_eq
      hn hkTwo hdelta code tail j) parsed.code

/-- The canonical tree itself satisfies the physical depth predicate. -/
theorem coarseSuccessfulCanonicalRecursiveTree_fits
    {start n k : ℕ} {hk : k + 1 ≤ n} {profileDelta : ℝ}
    {x y : Point} (hn : 2 ≤ n) (hkTwo : 2 ≤ k + 1)
    (hdelta : profileDelta ≤ 1)
    (code : CoarseSplitCompletionCode start n k hk profileDelta x y
      (profileInnerBoundary n k y)
      (discBoundary (0, 0) (outerScale n)) (0, 0))
    (tail : CoarseSuccessfulReturnTuple code)
    (j : Fin code.1.returnCount) :
    profileRefinementTreeFits n (k + 1)
      (profileRefinementTrees code.1.returnCount
        (coarseSuccessfulProfileRest code tail)
        (coarseSuccessfulGapChain hn hkTwo hdelta code tail) j) := by
  exact (coarseSuccessfulParsedProfileGap_tree_eq
    hn hkTwo hdelta code tail j) ▸
      coarseSuccessfulParsedProfileGap_fits
        hn hkTwo hdelta code tail j

/-- Assembling the transported canonical code still gives the exact coarse
bridge word. -/
theorem coarseSuccessfulCanonicalRecursiveBoundaryCode_eq_bridge
    {start n k : ℕ} {hk : k + 1 ≤ n} {profileDelta : ℝ}
    {x y : Point} (hn : 2 ≤ n) (hkTwo : 2 ≤ k + 1)
    (hdelta : profileDelta ≤ 1)
    (code : CoarseSplitCompletionCode start n k hk profileDelta x y
      (profileInnerBoundary n k y)
      (discBoundary (0, 0) (outerScale n)) (0, 0))
    (tail : CoarseSuccessfulReturnTuple code)
    (j : Fin code.1.returnCount) :
    (recursiveProfileGapBoundaryExitWordCode n (k + 1) y hn (by omega)
      (profileRefinementTrees code.1.returnCount
        (coarseSuccessfulProfileRest code tail)
        (coarseSuccessfulGapChain hn hkTwo hdelta code tail) j)
      (coarseSuccessfulCanonicalRecursiveTree_fits
        hn hkTwo hdelta code tail j)
      (coarseSuccessfulRecursiveEntrance hn hkTwo hdelta code tail j)
      (coarseSuccessfulRecursiveEndpoint hn hkTwo hdelta code tail j)
      (coarseSuccessfulCanonicalRecursiveCode
        hn hkTwo hdelta code tail j)).1 = (tail.1 j).1.1 := by
  let parsed := coarseSuccessfulParsedProfileGap
    hn hkTwo hdelta code tail j
  let htree := coarseSuccessfulParsedProfileGap_tree_eq
    hn hkTwo hdelta code tail j
  calc
    _ = (recursiveProfileGapBoundaryExitWordCode n (k + 1) y hn (by omega)
        parsed.tree
        (coarseSuccessfulParsedProfileGap_fits
          hn hkTwo hdelta code tail j)
        (coarseSuccessfulRecursiveEntrance hn hkTwo hdelta code tail j)
        (coarseSuccessfulRecursiveEndpoint hn hkTwo hdelta code tail j)
        parsed.code).1 := by
          exact recursiveProfileGapBoundaryExitWordCode_transport hn
            (by omega) htree
            (coarseSuccessfulParsedProfileGap_fits
              hn hkTwo hdelta code tail j)
            (coarseSuccessfulCanonicalRecursiveTree_fits
              hn hkTwo hdelta code tail j)
            (coarseSuccessfulRecursiveEntrance hn hkTwo hdelta code tail j)
            (coarseSuccessfulRecursiveEndpoint hn hkTwo hdelta code tail j)
            parsed.code
    _ = (tail.1 j).1.1 :=
      coarseSuccessfulRecursiveBoundaryCode_eq_bridge
        hn hkTwo hdelta code tail j

/-- The recursive product mass of the transported code is exactly the
literal stopped mass of the corresponding coarse bridge. -/
theorem coarseSuccessfulCanonicalRecursiveCodeMass_eq_bridge
    {start n k : ℕ} {hk : k + 1 ≤ n} {profileDelta : ℝ}
    {x y : Point} (hn : 2 ≤ n) (hkTwo : 2 ≤ k + 1)
    (hdelta : profileDelta ≤ 1)
    (code : CoarseSplitCompletionCode start n k hk profileDelta x y
      (profileInnerBoundary n k y)
      (discBoundary (0, 0) (outerScale n)) (0, 0))
    (tail : CoarseSuccessfulReturnTuple code)
    (j : Fin code.1.returnCount) :
    recursiveProfileGapCodeMass n (k + 1) y
        (profileRefinementTrees code.1.returnCount
          (coarseSuccessfulProfileRest code tail)
          (coarseSuccessfulGapChain hn hkTwo hdelta code tail) j)
        (coarseSuccessfulRecursiveEntrance hn hkTwo hdelta code tail j)
        (coarseSuccessfulRecursiveEndpoint hn hkTwo hdelta code tail j)
        (coarseSuccessfulCanonicalRecursiveCode
          hn hkTwo hdelta code tail j) =
      stoppedWordMass (tail.1 j).1.1 := by
  rw [← coarseSuccessfulCanonicalRecursiveBoundaryCode_eq_bridge
    hn hkTwo hdelta code tail j]
  rw [recursiveProfileGapBoundaryExitWordCode_val]
  exact (stoppedWordMass_recursiveProfileGapList n (k + 1) y
    (profileRefinementTrees code.1.returnCount
      (coarseSuccessfulProfileRest code tail)
      (coarseSuccessfulGapChain hn hkTwo hdelta code tail) j)
    (coarseSuccessfulRecursiveEntrance hn hkTwo hdelta code tail j)
    (coarseSuccessfulRecursiveEndpoint hn hkTwo hdelta code tail j)
    (coarseSuccessfulCanonicalRecursiveCode
      hn hkTwo hdelta code tail j)).symm

end

end Erdos1165.AsymmetricCoarseRecursiveSourceCode
