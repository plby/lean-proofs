/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/
import ErdosProblems.Erdos1165.AsymmetricCoarseRecursiveTailEncoding
import ErdosProblems.Erdos1165.AsymmetricPaddedPrefixMultiplicity

/-!
# A stopped upper bound from a constrained high profile tail

At the first two pair-separation levels the coarse replacement may alter the
forced level-one excursion.  It nevertheless preserves every sufficiently
high profile coordinate.  This file supplies the corresponding one-point
upper row without imposing any condition on the discarded low coordinates.

The main device is to split an arbitrary stopped path at a fixed profile
level.  The complementary coarse atoms have total mass at most one.  Inside
each atom, the consecutive high profile is parsed by the existing recursive
profile parser, so the usual endpoint-integrated tail estimate applies.
-/

open Filter MeasureTheory Set
open scoped BigOperators ENNReal

namespace Erdos1165.CoarseProfileTailUpper

open AnnularBoundaryExcursionKernel AnnularProfileClocks
open AnnularOffspringKernelRadial AnnularProfileGapAtoms
open AnnularProfileLiteralAtoms AnnularProfileLevelSkeleton
open AnnularRecursiveProfileActualCode
open AnnularRecursiveProfileActualParser
open AnnularRecursiveDecoratedProfileCode
open AnnularRecursiveProfileCodeAssembly AnnularRecursiveProfileShape
open AnnularRecursiveProfileEndpointTail
open AnnularRecursiveProfileSourceRecovery
open AnnularRecursiveProfileSourceSegment
open AnnularLiteralNestedProfileTailUpper
open AlternatingConcatPrefixFree
open AppendixFirstMoment ProfileListExponent ProfileWeightUpper
open ProfileConditionalTailUpper
open AsymmetricCoarseCompletionCode AsymmetricCoarseRecursiveSourceCode
open AsymmetricCoarseRecursiveTailEncoding
open AsymmetricPaddedPrefixMultiplicity
open AsymmetricCoarseSplitCompletion AsymmetricCoarseSuccessfulTailAtoms
open AsymmetricExtractedReturnClockRecovery AsymmetricReturnPrefixRecovery
open AsymmetricSplitCompletionRecovered AsymmetricSplitCompletionSource
open AsymmetricSplitLevelSplice
open MarkedBridgeFactorization PlanarPotential Proposition13Assembly
open ProfileGapChain TerminalGlobalExitSplice TerminalSkeletonFactorization
open TerminalSequentialVisitLaw TerminalSkeletonInvariance
open TerminalSkeletonWords ThickPoint

noncomputable section

attribute [local instance] Classical.propDecidable

/-! ## Recovery for an arbitrary coarse return tuple -/

/-- Put the fixed prefix back in front of an arbitrary tuple of admissible
coarse bridges. -/
def coarseReturnCanonicalSource
    {start n k : ℕ} {hk : k + 1 ≤ n} {profileDelta : ℝ}
    {x y : Point}
    (code : CoarseSplitCompletionCode start n k hk profileDelta x y
      (profileInnerBoundary n k y)
      (discBoundary (0, 0) (outerScale n)) (0, 0))
    (bridges : (j : Fin code.1.returnCount) →
      CoarseSignatureReturnCode x y (profileInnerBoundary n k y) code.1 j) :
    StepPath :=
  extendStoppedWord ((coarseAtom code).assemble (Unit.unit, bridges))

theorem coarseReturnCanonicalSource_mem_retained
    {start n k : ℕ} {hk : k + 1 ≤ n} {profileDelta : ℝ}
    {x y : Point}
    (code : CoarseSplitCompletionCode start n k hk profileDelta x y
      (profileInnerBoundary n k y)
      (discBoundary (0, 0) (outerScale n)) (0, 0))
    (bridges : (j : Fin code.1.returnCount) →
      CoarseSignatureReturnCode x y (profileInnerBoundary n k y) code.1 j) :
    coarseReturnCanonicalSource code bridges ∈ coarseRetainedAtom code := by
  unfold coarseRetainedAtom ComplementarySkeletonAtom.event stoppedWordEvent
  apply Set.mem_iUnion.mpr
  refine ⟨(Unit.unit, bridges), ?_⟩
  exact stepPrefix_extendStoppedWord _

theorem shift_coarseReturnCanonicalSource_mem_terminalCylinder
    {start n k : ℕ} {hk : k + 1 ≤ n} {profileDelta : ℝ}
    {x y : Point}
    (code : CoarseSplitCompletionCode start n k hk profileDelta x y
      (profileInnerBoundary n k y)
      (discBoundary (0, 0) (outerScale n)) (0, 0))
    (bridges : (j : Fin code.1.returnCount) →
      CoarseSignatureReturnCode x y (profileInnerBoundary n k y) code.1 j) :
    shiftSteps start (coarseReturnCanonicalSource code bridges) ∈
      stoppedWordCylinder
        (assembledTerminalWord code.1.skeleton
          (coarseTupleWords code bridges)) := by
  apply
    TerminalSkeletonFactorization.shiftSteps_mem_assembledTerminalWordCylinder_of_mem_assembleAfterPrefix
  change stepPrefix
      ((coarseAtom code).assemble (Unit.unit, bridges)).1
        (coarseReturnCanonicalSource code bridges) =
      ((coarseAtom code).assemble (Unit.unit, bridges)).2
  unfold coarseReturnCanonicalSource
  exact stepPrefix_extendStoppedWord _

/-- Re-extracting the split clock recovers the skeleton and all bridge words.
No successful-profile hypothesis is needed: candidate-box membership comes
from the validity witness of the coarse code, and global exit comes from its
boundary-first field. -/
theorem coarseReturnData_recovered
    {start n k : ℕ} {hk : k + 1 ≤ n} {profileDelta : ℝ}
    {x y : Point} (hn : 2 ≤ n)
    (code : CoarseSplitCompletionCode start n k hk profileDelta x y
      (profileInnerBoundary n k y)
      (discBoundary (0, 0) (outerScale n)) (0, 0))
    (bridges : (j : Fin code.1.returnCount) →
      CoarseSignatureReturnCode x y (profileInnerBoundary n k y) code.1 j) :
    let words : TerminalSegmentWords code.1.returnCount :=
      coarseTupleWords code bridges
    let horizon := assembledTerminalHorizon code.1.skeleton words
    let assembled := assembledTerminalPath code.1.skeleton words
    let actualT := extractTimedReturnSkeleton assembled (0, 0)
      (profileInnerBoundary n k y) (profileInnerBoundary n (k + 1) y)
      horizon code.1.returnCount
    compressTimedSkeleton assembled actualT = code.1.skeleton ∧
      intervalWords assembled actualT.entrance actualT.exit = words := by
  dsimp only
  let words : TerminalSegmentWords code.1.returnCount :=
    coarseTupleWords code bridges
  let horizon := assembledTerminalHorizon code.1.skeleton words
  let assembled := assembledTerminalPath code.1.skeleton words
  let source := coarseReturnCanonicalSource code bridges
  obtain ⟨origin, _hdataOrigin, hy, _hexitOrigin⟩ := code.2.origin_exists
  have hsourceTail : shiftSteps start source ∈
      stoppedWordCylinder (assembledTerminalWord code.1.skeleton words) := by
    simpa only [source, words] using
      shift_coarseReturnCanonicalSource_mem_terminalCylinder code bridges
  have hfirst : AbsoluteBoundaryFirstAt
      (discBoundary (0, 0) (outerScale n)) (0, 0) assembled horizon := by
    exact code.2.globalFirst (fun j ↦ (bridges j).1)
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
    coarseReturnCanonicalSource_mem_retained code bridges
  have hdata := code.2.recovered hsourceCoarse
  have hcountSource := congrArg
    (fun data : CoarseSplitCompletionData start n k ↦ data.returnCount) hdata
  have hcountSource' :
      boundaryExcursionCount
          (profileInnerBoundary n k y) (profileInnerBoundary n (k + 1) y)
          (0, 0) (shiftSteps start source) horizon = code.1.returnCount := by
    change (sourceSplitCompletionData start n k x y source).returnCount =
      code.1.returnCount at hcountSource
    simpa only [sourceSplitCompletionData_returnCount, hhorizon] using
      hcountSource
  have hcompleteActual : ∀ j : Fin code.1.returnCount,
      excursionStart (trajectory (shiftSteps start source))
        (profileInnerBoundary n k y) (profileInnerBoundary n (k + 1) y)
        horizon (j + 1) ≤ horizon := by
    apply returnComplete_of_boundaryExcursionCount_eq hcountSource'
    exact sourceReturnComplete (Nat.one_le_of_lt hn) hk hy hsourceExit
  let sourceT := extractTimedReturnSkeleton (shiftSteps start source) (0, 0)
    (profileInnerBoundary n k y) (profileInnerBoundary n (k + 1) y)
    horizon code.1.returnCount
  have hdataPack := congrArg
    (fun data : CoarseSplitCompletionData start n k ↦
      (⟨data.returnCount, data.skeleton⟩ :
        Σ q : ℕ, TerminalSkeletonCode q)) hdata
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
  let literalBridges : (j : Fin code.1.returnCount) →
      BoundaryExitWordCode (profileInnerBoundary n k y)
        (trajectory (shiftSteps start source) (sourceT.entrance j))
        (trajectory (shiftSteps start source) (sourceT.exit j)) := fun j ↦ by
    refine ⟨(bridges j).1.1, ?_, ?_⟩
    · have hentrance := congrArg
        (fun skeleton : TerminalSkeletonCode code.1.returnCount ↦
          skeleton.2.1 j) hskelSource
      simp only [compressTimedSkeleton_entrancePoint, sourceT,
        extractTimedReturnSkeleton_entrancePoint_apply] at hentrance
      rw [hentrance]
      exact (bridges j).1.2.1
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
      exact (bridges j).1.2.2
  have hrecovered := compressedReturnData_assembled_of_boundaryExitWordCodes
    hcompleteActual literalBridges
  have hbridgeWords :
      (fun j : Fin code.1.returnCount ↦
        List.ofFn (literalBridges j).1.2) = words := by
    funext j
    rfl
  dsimp only at hrecovered
  dsimp only [sourceT] at hskelSource
  rw [hbridgeWords, hskelSource] at hrecovered
  simpa only [assembled, horizon, words] using hrecovered

/-- Every admissible coarse bridge is the corresponding actual profile-gap
word in the assembled path. -/
theorem coarseReturnBridge_eq_profileGapStoppedWord
    {start n k : ℕ} {hk : k + 1 ≤ n} {profileDelta : ℝ}
    {x y : Point} (hn : 2 ≤ n)
    (code : CoarseSplitCompletionCode start n k hk profileDelta x y
      (profileInnerBoundary n k y)
      (discBoundary (0, 0) (outerScale n)) (0, 0))
    (bridges : (j : Fin code.1.returnCount) →
      CoarseSignatureReturnCode x y (profileInnerBoundary n k y) code.1 j)
    (j : Fin code.1.returnCount) :
    (bridges j).1.1 =
      profileGapStoppedWord
        (assembledTerminalPath code.1.skeleton
          (coarseTupleWords code bridges)) n
        (assembledTerminalHorizon code.1.skeleton
          (coarseTupleWords code bridges)) y (k + 1) j := by
  let words : TerminalSegmentWords code.1.returnCount :=
    coarseTupleWords code bridges
  let horizon := assembledTerminalHorizon code.1.skeleton words
  let assembled := assembledTerminalPath code.1.skeleton words
  let actualT := extractTimedReturnSkeleton assembled (0, 0)
    (profileInnerBoundary n k y) (profileInnerBoundary n (k + 1) y)
    horizon code.1.returnCount
  have hrecovered := coarseReturnData_recovered hn code bridges
  dsimp only at hrecovered
  have hj := congrFun hrecovered.2 j
  have hgap :=
    intervalWords_extractTimedReturnSkeleton_eq_profileGapStoppedWord
      assembled n horizon y k code.1.returnCount j
  have hlists : List.ofFn (bridges j).1.1.2 =
      List.ofFn
        (profileGapStoppedWord assembled n horizon y (k + 1) j).2 := by
    exact (show words j = _ from
      hj.symm.trans (by simpa only [actualT] using hgap))
  calc
    (bridges j).1.1 = listStoppedWord (List.ofFn (bridges j).1.1.2) :=
      (listStoppedWord_ofFn _).symm
    _ = listStoppedWord (List.ofFn
        (profileGapStoppedWord assembled n horizon y (k + 1) j).2) :=
      congrArg listStoppedWord hlists
    _ = profileGapStoppedWord assembled n horizon y (k + 1) j :=
      listStoppedWord_ofFn _

/-! ## A canonical constrained full profile extending the actual high tail -/

/-- Fill every discarded low profile coordinate by the exact parabolic
centre and retain the actual completed counts from scale `k+1` onward. -/
def coarseTailProfile
    {start n k : ℕ} {hk : k + 1 ≤ n} {profileDelta : ℝ}
    {x y : Point}
    (code : CoarseSplitCompletionCode start n k hk profileDelta x y
      (profileInnerBoundary n k y)
      (discBoundary (0, 0) (outerScale n)) (0, 0))
    (bridges : (j : Fin code.1.returnCount) →
      CoarseSignatureReturnCode x y (profileInnerBoundary n k y) code.1 j) :
    Profile n :=
  fun i ↦
    if k + 1 ≤ scaleIndex i then
      internalProfile
        (excursionProfile
          (trajectory (assembledTerminalPath code.1.skeleton
            (coarseTupleWords code bridges))) n
          (assembledTerminalHorizon code.1.skeleton
            (coarseTupleWords code bridges)) y) i
    else centerProfile n i

theorem profileAtScale_coarseTailProfile_of_le
    {start n k r : ℕ} {hk : k + 1 ≤ n} {profileDelta : ℝ}
    {x y : Point}
    (code : CoarseSplitCompletionCode start n k hk profileDelta x y
      (profileInnerBoundary n k y)
      (discBoundary (0, 0) (outerScale n)) (0, 0))
    (bridges : (j : Fin code.1.returnCount) →
      CoarseSignatureReturnCode x y (profileInnerBoundary n k y) code.1 j)
    (hrTwo : 2 ≤ r) (hrn : r ≤ n) (hkr : k + 1 ≤ r) :
    profileAtScale (coarseTailProfile code bridges) r =
      profileCompletedCount
        (trajectory (assembledTerminalPath code.1.skeleton
          (coarseTupleWords code bridges))) n
        (assembledTerminalHorizon code.1.skeleton
          (coarseTupleWords code bridges)) y r := by
  let i : Fin (n - 1) := ⟨r - 2, by omega⟩
  have hscale : scaleIndex i = r := by
    unfold scaleIndex
    dsimp only [i]
    omega
  rw [← hscale, profileAtScale_scaleIndex]
  unfold coarseTailProfile
  rw [if_pos (by simpa only [hscale] using hkr)]
  rw [internalProfile_apply]
  exact excursionProfile_eq_profileCompletedCount _ _ _ _ (by omega) (by omega)

/-- The number of coarse bridge coordinates is the actual completed count at
the first retained high scale. -/
theorem coarseReturnCount_eq_profileCompletedCount
    {start n k : ℕ} {hk : k + 1 ≤ n} {profileDelta : ℝ}
    {x y : Point} (hn : 2 ≤ n)
    (code : CoarseSplitCompletionCode start n k hk profileDelta x y
      (profileInnerBoundary n k y)
      (discBoundary (0, 0) (outerScale n)) (0, 0))
    (bridges : (j : Fin code.1.returnCount) →
      CoarseSignatureReturnCode x y (profileInnerBoundary n k y) code.1 j) :
    code.1.returnCount =
      profileCompletedCount
        (trajectory (assembledTerminalPath code.1.skeleton
          (coarseTupleWords code bridges))) n
        (assembledTerminalHorizon code.1.skeleton
          (coarseTupleWords code bridges)) y (k + 1) := by
  let words : TerminalSegmentWords code.1.returnCount :=
    coarseTupleWords code bridges
  let horizon := assembledTerminalHorizon code.1.skeleton words
  let assembled := assembledTerminalPath code.1.skeleton words
  let source := coarseReturnCanonicalSource code bridges
  have hsourceTail : shiftSteps start source ∈
      stoppedWordCylinder (assembledTerminalWord code.1.skeleton words) := by
    simpa only [source, words] using
      shift_coarseReturnCanonicalSource_mem_terminalCylinder code bridges
  have htrajectory : ∀ q ≤ horizon,
      trajectory (shiftSteps start source) q = trajectory assembled q := by
    intro q hq
    exact trajectory_eq_assembledTerminalPath_of_mem_stoppedWordCylinder
      hsourceTail hq
  have hfirst : AbsoluteBoundaryFirstAt
      (discBoundary (0, 0) (outerScale n)) (0, 0) assembled horizon := by
    exact code.2.globalFirst (fun j ↦ (bridges j).1)
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
  have hdata := code.2.recovered
    (coarseReturnCanonicalSource_mem_retained code bridges)
  have hcountSource := congrArg
    (fun data : CoarseSplitCompletionData start n k ↦ data.returnCount) hdata
  have hcountSource' :
      boundaryExcursionCount
          (profileInnerBoundary n k y) (profileInnerBoundary n (k + 1) y)
          (0, 0) (shiftSteps start source) horizon = code.1.returnCount := by
    change (sourceSplitCompletionData start n k x y source).returnCount =
      code.1.returnCount at hcountSource
    simpa only [sourceSplitCompletionData_returnCount, hhorizon] using
      hcountSource
  have hcountCongr :
      completedExcursionCount (trajectory (shiftSteps start source))
          (profileOuterBoundary n (k + 1) y)
          (profileInnerBoundary n (k + 1) y) horizon =
        completedExcursionCount (trajectory assembled)
          (profileOuterBoundary n (k + 1) y)
          (profileInnerBoundary n (k + 1) y) horizon :=
    Proposition13Measurability.completedExcursionCount_congr_prefix
      htrajectory _ _
  rw [profileCompletedCount, ← hcountCongr]
  simpa only [boundaryExcursionCount, profileOuterBoundary,
    profileInnerBoundary, Nat.add_sub_cancel,
    trajectoryFrom_zero_eq_trajectory, assembled, horizon, words] using
      hcountSource'.symm

theorem coarseReturnCount_eq_profileAtScale_coarseTailProfile
    {start n k : ℕ} {hk : k + 1 ≤ n} {profileDelta : ℝ}
    {x y : Point} (hn : 2 ≤ n) (hkTwo : 2 ≤ k + 1)
    (code : CoarseSplitCompletionCode start n k hk profileDelta x y
      (profileInnerBoundary n k y)
      (discBoundary (0, 0) (outerScale n)) (0, 0))
    (bridges : (j : Fin code.1.returnCount) →
      CoarseSignatureReturnCode x y (profileInnerBoundary n k y) code.1 j) :
    code.1.returnCount =
      profileAtScale (coarseTailProfile code bridges) (k + 1) := by
  rw [profileAtScale_coarseTailProfile_of_le code bridges hkTwo hk le_rfl]
  exact coarseReturnCount_eq_profileCompletedCount hn code bridges

/-- Coarse tuples whose canonical high-tail extension is constrained. -/
def CoarseConstrainedTailReturnTuple
    {start n k : ℕ} {hk : k + 1 ≤ n} {profileDelta : ℝ}
    {x y : Point}
    (code : CoarseSplitCompletionCode start n k hk profileDelta x y
      (profileInnerBoundary n k y)
      (discBoundary (0, 0) (outerScale n)) (0, 0)) :=
  {bridges : (j : Fin code.1.returnCount) →
      CoarseSignatureReturnCode x y (profileInnerBoundary n k y) code.1 j //
    IsConstrainedProfile profileDelta (coarseTailProfile code bridges)}

noncomputable instance coarseConstrainedTailReturnTupleCountable
    {start n k : ℕ} {hk : k + 1 ≤ n} {profileDelta : ℝ}
    {x y : Point}
    (code : CoarseSplitCompletionCode start n k hk profileDelta x y
      (profileInnerBoundary n k y)
      (discBoundary (0, 0) (outerScale n)) (0, 0)) :
    Countable (CoarseConstrainedTailReturnTuple code) :=
  Subtype.countable

theorem coarseAssembled_isOuterExitTime
    {start n k : ℕ} {hk : k + 1 ≤ n} {profileDelta : ℝ}
    {x y : Point}
    (code : CoarseSplitCompletionCode start n k hk profileDelta x y
      (profileInnerBoundary n k y)
      (discBoundary (0, 0) (outerScale n)) (0, 0))
    (bridges : (j : Fin code.1.returnCount) →
      CoarseSignatureReturnCode x y (profileInnerBoundary n k y) code.1 j) :
    IsOuterExitTime
      (trajectory (assembledTerminalPath code.1.skeleton
        (coarseTupleWords code bridges))) n
      (assembledTerminalHorizon code.1.skeleton
        (coarseTupleWords code bridges)) := by
  have hfirst := code.2.globalFirst (fun j ↦ (bridges j).1)
  change AbsoluteBoundaryFirstAt
    (discBoundary (0, 0) (outerScale n)) (0, 0)
    (assembledTerminalPath code.1.skeleton (coarseTupleWords code bridges))
    (assembledTerminalHorizon code.1.skeleton (coarseTupleWords code bridges))
      at hfirst
  simpa only [AbsoluteBoundaryFirstAt, IsOuterExitTime,
    trajectoryFrom_zero_eq_trajectory] using hfirst

def coarseConstrainedTailProfileRest
    {start n k : ℕ} {hk : k + 1 ≤ n} {profileDelta : ℝ}
    {x y : Point}
    {code : CoarseSplitCompletionCode start n k hk profileDelta x y
      (profileInnerBoundary n k y)
      (discBoundary (0, 0) (outerScale n)) (0, 0)}
    (tail : CoarseConstrainedTailReturnTuple code) : List ℕ :=
  (profileSegmentValues (coarseTailProfile code tail.1) (k + 1)).tail

theorem coarseConstrainedTailProfileSegment_eq
    {start n k : ℕ} {hk : k + 1 ≤ n} {profileDelta : ℝ}
    {x y : Point} (hn : 2 ≤ n) (hkTwo : 2 ≤ k + 1)
    (code : CoarseSplitCompletionCode start n k hk profileDelta x y
      (profileInnerBoundary n k y)
      (discBoundary (0, 0) (outerScale n)) (0, 0))
    (tail : CoarseConstrainedTailReturnTuple code) :
    profileSegmentValues (coarseTailProfile code tail.1) (k + 1) =
      code.1.returnCount :: coarseConstrainedTailProfileRest tail := by
  rw [profileSegmentValues_eq_head_cons_tail hk]
  rw [← coarseReturnCount_eq_profileAtScale_coarseTailProfile
    hn hkTwo code tail.1]
  rfl

def coarseConstrainedTailProfileSegmentData
    {start n k : ℕ} {hk : k + 1 ≤ n} {profileDelta : ℝ}
    {x y : Point} (hn : 2 ≤ n) (hkTwo : 2 ≤ k + 1)
    (hdelta : profileDelta ≤ 1) (hy : y ∈ candidateBox n)
    (code : CoarseSplitCompletionCode start n k hk profileDelta x y
      (profileInnerBoundary n k y)
      (discBoundary (0, 0) (outerScale n)) (0, 0))
    (tail : CoarseConstrainedTailReturnTuple code) :
    ActualProfileSegmentData
      (assembledTerminalPath code.1.skeleton (coarseTupleWords code tail.1))
      n
      (assembledTerminalHorizon code.1.skeleton (coarseTupleWords code tail.1))
      y (k + 1)
      (code.1.returnCount :: coarseConstrainedTailProfileRest tail) := by
  let raw := actualProfileSegmentDataOfTailCounts hn
    (coarseAssembled_isOuterExitTime code tail.1) hy tail.2 hdelta
    (k + 1) hkTwo hk (fun r hkr hrn ↦ by
      exact (profileAtScale_coarseTailProfile_of_le
        code tail.1 (by omega) hrn hkr).symm)
  rw [← coarseConstrainedTailProfileSegment_eq hn hkTwo code tail]
  exact raw

theorem coarseConstrainedTailProfileRest_depth
    {start n k : ℕ} {hk : k + 1 ≤ n} {profileDelta : ℝ}
    {x y : Point} (hkTwo : 2 ≤ k + 1)
    (code : CoarseSplitCompletionCode start n k hk profileDelta x y
      (profileInnerBoundary n k y)
      (discBoundary (0, 0) (outerScale n)) (0, 0))
    (tail : CoarseConstrainedTailReturnTuple code) :
    k + 1 + (coarseConstrainedTailProfileRest tail).length ≤ n := by
  have hlength := profileSegmentValues_length
    (coarseTailProfile code tail.1) (k + 1)
  rw [coarseConstrainedTailProfileSegment_eq (by omega) hkTwo code tail]
    at hlength
  simp only [List.length_cons] at hlength
  omega

/-! ## The recursive parser for a constrained coarse high tail -/

/-- Actual top-level entrance vector for the high-tail parser. -/
def coarseConstrainedTailRecursiveEntrance
    {start n k : ℕ} {hk : k + 1 ≤ n} {profileDelta : ℝ}
    {x y : Point} (hn : 2 ≤ n) (hkTwo : 2 ≤ k + 1)
    (hdelta : profileDelta ≤ 1) (hy : y ∈ candidateBox n)
    (code : CoarseSplitCompletionCode start n k hk profileDelta x y
      (profileInnerBoundary n k y)
      (discBoundary (0, 0) (outerScale n)) (0, 0))
    (tail : CoarseConstrainedTailReturnTuple code)
    (j : Fin code.1.returnCount) :
    ProfileCycleMiddlePoint n (k + 1) y := by
  let data := coarseConstrainedTailProfileSegmentData
    hn hkTwo hdelta hy code tail
  exact ⟨profileGapStartPoint
      (assembledTerminalPath code.1.skeleton (coarseTupleWords code tail.1)) n
      (assembledTerminalHorizon code.1.skeleton (coarseTupleWords code tail.1))
      y (k + 1) j,
    RealDiscFinite.mem_discBoundaryFinset.mpr
      (profileGapStartPoint_mem_innerBoundary
        (data.headComplete j j.isLt))⟩

/-- Actual top-level endpoint vector for the high-tail parser. -/
def coarseConstrainedTailRecursiveEndpoint
    {start n k : ℕ} {hk : k + 1 ≤ n} {profileDelta : ℝ}
    {x y : Point} (hn : 2 ≤ n) (hkTwo : 2 ≤ k + 1)
    (hdelta : profileDelta ≤ 1) (hy : y ∈ candidateBox n)
    (code : CoarseSplitCompletionCode start n k hk profileDelta x y
      (profileInnerBoundary n k y)
      (discBoundary (0, 0) (outerScale n)) (0, 0))
    (tail : CoarseConstrainedTailReturnTuple code)
    (j : Fin code.1.returnCount) :
    ProfileCycleOuterPoint n (k + 1) y := by
  let data := coarseConstrainedTailProfileSegmentData
    hn hkTwo hdelta hy code tail
  exact ⟨profileGapExitPoint
      (assembledTerminalPath code.1.skeleton (coarseTupleWords code tail.1)) n
      (assembledTerminalHorizon code.1.skeleton (coarseTupleWords code tail.1))
      y (k + 1) j,
    RealDiscFinite.mem_discBoundaryFinset.mpr
      (profileGapExitPoint_mem_outerBoundary
        (data.headComplete j j.isLt))⟩

@[simp] theorem coarseConstrainedTailRecursiveEntrance_val
    {start n k : ℕ} {hk : k + 1 ≤ n} {profileDelta : ℝ}
    {x y : Point} (hn : 2 ≤ n) (hkTwo : 2 ≤ k + 1)
    (hdelta : profileDelta ≤ 1) (hy : y ∈ candidateBox n)
    (code : CoarseSplitCompletionCode start n k hk profileDelta x y
      (profileInnerBoundary n k y)
      (discBoundary (0, 0) (outerScale n)) (0, 0))
    (tail : CoarseConstrainedTailReturnTuple code)
    (j : Fin code.1.returnCount) :
    (coarseConstrainedTailRecursiveEntrance
      hn hkTwo hdelta hy code tail j).1 =
      profileGapStartPoint
        (assembledTerminalPath code.1.skeleton (coarseTupleWords code tail.1)) n
        (assembledTerminalHorizon code.1.skeleton (coarseTupleWords code tail.1))
        y (k + 1) j := rfl

@[simp] theorem coarseConstrainedTailRecursiveEndpoint_val
    {start n k : ℕ} {hk : k + 1 ≤ n} {profileDelta : ℝ}
    {x y : Point} (hn : 2 ≤ n) (hkTwo : 2 ≤ k + 1)
    (hdelta : profileDelta ≤ 1) (hy : y ∈ candidateBox n)
    (code : CoarseSplitCompletionCode start n k hk profileDelta x y
      (profileInnerBoundary n k y)
      (discBoundary (0, 0) (outerScale n)) (0, 0))
    (tail : CoarseConstrainedTailReturnTuple code)
    (j : Fin code.1.returnCount) :
    (coarseConstrainedTailRecursiveEndpoint
      hn hkTwo hdelta hy code tail j).1 =
      profileGapExitPoint
        (assembledTerminalPath code.1.skeleton (coarseTupleWords code tail.1)) n
        (assembledTerminalHorizon code.1.skeleton (coarseTupleWords code tail.1))
        y (k + 1) j := rfl

/-- The parser entrance is the one stored in the complementary skeleton. -/
theorem coarseConstrainedTailRecursiveEntrance_eq_skeleton
    {start n k : ℕ} {hk : k + 1 ≤ n} {profileDelta : ℝ}
    {x y : Point} (hn : 2 ≤ n) (hkTwo : 2 ≤ k + 1)
    (hdelta : profileDelta ≤ 1) (hy : y ∈ candidateBox n)
    (code : CoarseSplitCompletionCode start n k hk profileDelta x y
      (profileInnerBoundary n k y)
      (discBoundary (0, 0) (outerScale n)) (0, 0))
    (tail : CoarseConstrainedTailReturnTuple code)
    (j : Fin code.1.returnCount) :
    (coarseConstrainedTailRecursiveEntrance
      hn hkTwo hdelta hy code tail j).1 = code.1.skeleton.2.1 j := by
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
    (coarseReturnData_recovered hn code tail.1).1
  change profileGapStartPoint assembled n horizon y (k + 1) j = _
  rw [show profileGapStartPoint assembled n horizon y (k + 1) j =
      actualT.entrancePoint j by
    simp only [actualT, profileGapStartPoint, profileInnerHitTime,
      extractTimedReturnSkeleton, returnEntrancePoint, returnEntranceTime,
      profileOuterBoundary, profileInnerBoundary,
      trajectoryFrom_zero_eq_trajectory, Nat.add_sub_cancel]]
  simpa only [compressTimedSkeleton_entrancePoint] using hskel

/-- The parser endpoint is the one stored in the complementary skeleton. -/
theorem coarseConstrainedTailRecursiveEndpoint_eq_skeleton
    {start n k : ℕ} {hk : k + 1 ≤ n} {profileDelta : ℝ}
    {x y : Point} (hn : 2 ≤ n) (hkTwo : 2 ≤ k + 1)
    (hdelta : profileDelta ≤ 1) (hy : y ∈ candidateBox n)
    (code : CoarseSplitCompletionCode start n k hk profileDelta x y
      (profileInnerBoundary n k y)
      (discBoundary (0, 0) (outerScale n)) (0, 0))
    (tail : CoarseConstrainedTailReturnTuple code)
    (j : Fin code.1.returnCount) :
    (coarseConstrainedTailRecursiveEndpoint
      hn hkTwo hdelta hy code tail j).1 = code.1.skeleton.2.2 j := by
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
    (coarseReturnData_recovered hn code tail.1).1
  change profileGapExitPoint assembled n horizon y (k + 1) j = _
  rw [show profileGapExitPoint assembled n horizon y (k + 1) j =
      actualT.exitPoint j by
    simp only [actualT, profileGapExitPoint, profileGapExitTime,
      profileOuterHitTime, extractTimedReturnSkeleton, returnExitPoint,
      returnExitTime, profileOuterBoundary, profileInnerBoundary,
      trajectoryFrom_zero_eq_trajectory, Nat.add_sub_cancel]]
  simpa only [compressTimedSkeleton_exitPoint] using hskel

attribute [irreducible]
  coarseConstrainedTailRecursiveEntrance
  coarseConstrainedTailRecursiveEndpoint

/-- Canonical weak-composition genealogy of the retained high tail. -/
def coarseConstrainedTailGapChain
    {start n k : ℕ} {hk : k + 1 ≤ n} {profileDelta : ℝ}
    {x y : Point} (hn : 2 ≤ n) (hkTwo : 2 ≤ k + 1)
    (hdelta : profileDelta ≤ 1) (hy : y ∈ candidateBox n)
    (code : CoarseSplitCompletionCode start n k hk profileDelta x y
      (profileInnerBoundary n k y)
      (discBoundary (0, 0) (outerScale n)) (0, 0))
    (tail : CoarseConstrainedTailReturnTuple code) :
    GapChain (code.1.returnCount :: coarseConstrainedTailProfileRest tail) :=
  (coarseConstrainedTailProfileSegmentData
      hn hkTwo hdelta hy code tail).gapChain
    hn hy (by omega) (coarseConstrainedTailProfileRest_depth hkTwo code tail)

/-- Literal recursive parser for one constrained coarse bridge. -/
def coarseConstrainedTailParsedProfileGap
    {start n k : ℕ} {hk : k + 1 ≤ n} {profileDelta : ℝ}
    {x y : Point} (hn : 2 ≤ n) (hkTwo : 2 ≤ k + 1)
    (hdelta : profileDelta ≤ 1) (hy : y ∈ candidateBox n)
    (code : CoarseSplitCompletionCode start n k hk profileDelta x y
      (profileInnerBoundary n k y)
      (discBoundary (0, 0) (outerScale n)) (0, 0))
    (tail : CoarseConstrainedTailReturnTuple code)
    (j : Fin code.1.returnCount) :
    ActualParsedProfileGap n (k + 1) y
      (coarseConstrainedTailRecursiveEntrance
        hn hkTwo hdelta hy code tail j)
      (coarseConstrainedTailRecursiveEndpoint
        hn hkTwo hdelta hy code tail j) := by
  let data := coarseConstrainedTailProfileSegmentData
    hn hkTwo hdelta hy code tail
  exact actualParsedProfileGap hn hy
    (coarseConstrainedTailProfileRest tail) (by omega)
    (coarseConstrainedTailProfileRest_depth hkTwo code tail) data j
    (coarseConstrainedTailRecursiveEntrance
      hn hkTwo hdelta hy code tail j)
    (coarseConstrainedTailRecursiveEndpoint
      hn hkTwo hdelta hy code tail j)
    (coarseConstrainedTailRecursiveEntrance_val
      hn hkTwo hdelta hy code tail j).symm
    (coarseConstrainedTailRecursiveEndpoint_val
      hn hkTwo hdelta hy code tail j).symm

/-- The parsed tree is the canonical tree selected by the high-tail chain. -/
theorem coarseConstrainedTailParsedProfileGap_tree_eq
    {start n k : ℕ} {hk : k + 1 ≤ n} {profileDelta : ℝ}
    {x y : Point} (hn : 2 ≤ n) (hkTwo : 2 ≤ k + 1)
    (hdelta : profileDelta ≤ 1) (hy : y ∈ candidateBox n)
    (code : CoarseSplitCompletionCode start n k hk profileDelta x y
      (profileInnerBoundary n k y)
      (discBoundary (0, 0) (outerScale n)) (0, 0))
    (tail : CoarseConstrainedTailReturnTuple code)
    (j : Fin code.1.returnCount) :
    (coarseConstrainedTailParsedProfileGap
      hn hkTwo hdelta hy code tail j).tree =
      profileRefinementTrees code.1.returnCount
        (coarseConstrainedTailProfileRest tail)
        (coarseConstrainedTailGapChain
          hn hkTwo hdelta hy code tail) j := by
  let data := coarseConstrainedTailProfileSegmentData
    hn hkTwo hdelta hy code tail
  let entrance := coarseConstrainedTailRecursiveEntrance
    hn hkTwo hdelta hy code tail j
  let endpoint := coarseConstrainedTailRecursiveEndpoint
    hn hkTwo hdelta hy code tail j
  have htree := actualParsedProfileGap_tree hn hy
    (coarseConstrainedTailProfileRest tail) (by omega)
    (coarseConstrainedTailProfileRest_depth hkTwo code tail) data j
    entrance endpoint
    (coarseConstrainedTailRecursiveEntrance_val
      hn hkTwo hdelta hy code tail j).symm
    (coarseConstrainedTailRecursiveEndpoint_val
      hn hkTwo hdelta hy code tail j).symm
  have hrefine := refinementTrees_eq_profileRefinementTrees hn hy
    (coarseConstrainedTailProfileRest tail) (by omega)
    (coarseConstrainedTailProfileRest_depth hkTwo code tail) data j
  exact htree.trans (hrefine.trans (by rfl))

/-- The actual parsed tree satisfies the physical depth predicate. -/
theorem coarseConstrainedTailParsedProfileGap_fits
    {start n k : ℕ} {hk : k + 1 ≤ n} {profileDelta : ℝ}
    {x y : Point} (hn : 2 ≤ n) (hkTwo : 2 ≤ k + 1)
    (hdelta : profileDelta ≤ 1) (hy : y ∈ candidateBox n)
    (code : CoarseSplitCompletionCode start n k hk profileDelta x y
      (profileInnerBoundary n k y)
      (discBoundary (0, 0) (outerScale n)) (0, 0))
    (tail : CoarseConstrainedTailReturnTuple code)
    (j : Fin code.1.returnCount) :
    profileRefinementTreeFits n (k + 1)
      (coarseConstrainedTailParsedProfileGap
        hn hkTwo hdelta hy code tail j).tree := by
  let data := coarseConstrainedTailProfileSegmentData
    hn hkTwo hdelta hy code tail
  let entrance := coarseConstrainedTailRecursiveEntrance
    hn hkTwo hdelta hy code tail j
  let endpoint := coarseConstrainedTailRecursiveEndpoint
    hn hkTwo hdelta hy code tail j
  simpa only [coarseConstrainedTailParsedProfileGap] using
    actualParsedProfileGap_fits hn hy
      (coarseConstrainedTailProfileRest tail) (by omega)
      (coarseConstrainedTailProfileRest_depth hkTwo code tail) data j
      entrance endpoint
      (coarseConstrainedTailRecursiveEntrance_val
        hn hkTwo hdelta hy code tail j).symm
      (coarseConstrainedTailRecursiveEndpoint_val
        hn hkTwo hdelta hy code tail j).symm

/-- Transport the parsed code onto the canonical refinement tree. -/
def coarseConstrainedTailCanonicalRecursiveCode
    {start n k : ℕ} {hk : k + 1 ≤ n} {profileDelta : ℝ}
    {x y : Point} (hn : 2 ≤ n) (hkTwo : 2 ≤ k + 1)
    (hdelta : profileDelta ≤ 1) (hy : y ∈ candidateBox n)
    (code : CoarseSplitCompletionCode start n k hk profileDelta x y
      (profileInnerBoundary n k y)
      (discBoundary (0, 0) (outerScale n)) (0, 0))
    (tail : CoarseConstrainedTailReturnTuple code)
    (j : Fin code.1.returnCount) :
    RecursiveProfileGapCode n (k + 1) y
      (profileRefinementTrees code.1.returnCount
        (coarseConstrainedTailProfileRest tail)
        (coarseConstrainedTailGapChain
          hn hkTwo hdelta hy code tail) j)
      (coarseConstrainedTailRecursiveEntrance
        hn hkTwo hdelta hy code tail j)
      (coarseConstrainedTailRecursiveEndpoint
        hn hkTwo hdelta hy code tail j) := by
  let parsed := coarseConstrainedTailParsedProfileGap
    hn hkTwo hdelta hy code tail j
  exact transportRecursiveProfileGapCode
    (coarseConstrainedTailParsedProfileGap_tree_eq
      hn hkTwo hdelta hy code tail j) parsed.code

/-- The transported canonical tree still satisfies the depth predicate. -/
theorem coarseConstrainedTailCanonicalRecursiveTree_fits
    {start n k : ℕ} {hk : k + 1 ≤ n} {profileDelta : ℝ}
    {x y : Point} (hn : 2 ≤ n) (hkTwo : 2 ≤ k + 1)
    (hdelta : profileDelta ≤ 1) (hy : y ∈ candidateBox n)
    (code : CoarseSplitCompletionCode start n k hk profileDelta x y
      (profileInnerBoundary n k y)
      (discBoundary (0, 0) (outerScale n)) (0, 0))
    (tail : CoarseConstrainedTailReturnTuple code)
    (j : Fin code.1.returnCount) :
    profileRefinementTreeFits n (k + 1)
      (profileRefinementTrees code.1.returnCount
        (coarseConstrainedTailProfileRest tail)
        (coarseConstrainedTailGapChain
          hn hkTwo hdelta hy code tail) j) := by
  exact (coarseConstrainedTailParsedProfileGap_tree_eq
    hn hkTwo hdelta hy code tail j) ▸
      coarseConstrainedTailParsedProfileGap_fits
        hn hkTwo hdelta hy code tail j

/-- Reassembling the canonical code gives the original coarse bridge. -/
theorem coarseConstrainedTailCanonicalRecursiveBoundaryCode_eq_bridge
    {start n k : ℕ} {hk : k + 1 ≤ n} {profileDelta : ℝ}
    {x y : Point} (hn : 2 ≤ n) (hkTwo : 2 ≤ k + 1)
    (hdelta : profileDelta ≤ 1) (hy : y ∈ candidateBox n)
    (code : CoarseSplitCompletionCode start n k hk profileDelta x y
      (profileInnerBoundary n k y)
      (discBoundary (0, 0) (outerScale n)) (0, 0))
    (tail : CoarseConstrainedTailReturnTuple code)
    (j : Fin code.1.returnCount) :
    (recursiveProfileGapBoundaryExitWordCode n (k + 1) y hn (by omega)
      (profileRefinementTrees code.1.returnCount
        (coarseConstrainedTailProfileRest tail)
        (coarseConstrainedTailGapChain
          hn hkTwo hdelta hy code tail) j)
      (coarseConstrainedTailCanonicalRecursiveTree_fits
        hn hkTwo hdelta hy code tail j)
      (coarseConstrainedTailRecursiveEntrance
        hn hkTwo hdelta hy code tail j)
      (coarseConstrainedTailRecursiveEndpoint
        hn hkTwo hdelta hy code tail j)
      (coarseConstrainedTailCanonicalRecursiveCode
        hn hkTwo hdelta hy code tail j)).1 = (tail.1 j).1.1 := by
  let parsed := coarseConstrainedTailParsedProfileGap
    hn hkTwo hdelta hy code tail j
  let htree := coarseConstrainedTailParsedProfileGap_tree_eq
    hn hkTwo hdelta hy code tail j
  calc
    _ = (recursiveProfileGapBoundaryExitWordCode n (k + 1) y hn (by omega)
        parsed.tree
        (coarseConstrainedTailParsedProfileGap_fits
          hn hkTwo hdelta hy code tail j)
        (coarseConstrainedTailRecursiveEntrance
          hn hkTwo hdelta hy code tail j)
        (coarseConstrainedTailRecursiveEndpoint
          hn hkTwo hdelta hy code tail j)
        parsed.code).1 := by
          exact recursiveProfileGapBoundaryExitWordCode_transport hn
            (by omega) htree
            (coarseConstrainedTailParsedProfileGap_fits
              hn hkTwo hdelta hy code tail j)
            (coarseConstrainedTailCanonicalRecursiveTree_fits
              hn hkTwo hdelta hy code tail j)
            (coarseConstrainedTailRecursiveEntrance
              hn hkTwo hdelta hy code tail j)
            (coarseConstrainedTailRecursiveEndpoint
              hn hkTwo hdelta hy code tail j)
            parsed.code
    _ = (tail.1 j).1.1 := by
      let data := coarseConstrainedTailProfileSegmentData
        hn hkTwo hdelta hy code tail
      let entrance := coarseConstrainedTailRecursiveEntrance
        hn hkTwo hdelta hy code tail j
      let endpoint := coarseConstrainedTailRecursiveEndpoint
        hn hkTwo hdelta hy code tail j
      have hsource := recursiveProfileGapBoundaryExitWordCode_actualParsed_eq
        hn hy (coarseConstrainedTailProfileRest tail) (by omega)
        (coarseConstrainedTailProfileRest_depth hkTwo code tail) data j
        entrance endpoint
        (coarseConstrainedTailRecursiveEntrance_val
          hn hkTwo hdelta hy code tail j).symm
        (coarseConstrainedTailRecursiveEndpoint_val
          hn hkTwo hdelta hy code tail j).symm
      exact hsource.trans
        (coarseReturnBridge_eq_profileGapStoppedWord
          hn code tail.1 j).symm

/-- The recursive mass of a canonical code is the literal bridge mass. -/
theorem coarseConstrainedTailCanonicalRecursiveCodeMass_eq_bridge
    {start n k : ℕ} {hk : k + 1 ≤ n} {profileDelta : ℝ}
    {x y : Point} (hn : 2 ≤ n) (hkTwo : 2 ≤ k + 1)
    (hdelta : profileDelta ≤ 1) (hy : y ∈ candidateBox n)
    (code : CoarseSplitCompletionCode start n k hk profileDelta x y
      (profileInnerBoundary n k y)
      (discBoundary (0, 0) (outerScale n)) (0, 0))
    (tail : CoarseConstrainedTailReturnTuple code)
    (j : Fin code.1.returnCount) :
    recursiveProfileGapCodeMass n (k + 1) y
        (profileRefinementTrees code.1.returnCount
          (coarseConstrainedTailProfileRest tail)
          (coarseConstrainedTailGapChain
            hn hkTwo hdelta hy code tail) j)
        (coarseConstrainedTailRecursiveEntrance
          hn hkTwo hdelta hy code tail j)
        (coarseConstrainedTailRecursiveEndpoint
          hn hkTwo hdelta hy code tail j)
        (coarseConstrainedTailCanonicalRecursiveCode
          hn hkTwo hdelta hy code tail j) =
      stoppedWordMass (tail.1 j).1.1 := by
  rw [← coarseConstrainedTailCanonicalRecursiveBoundaryCode_eq_bridge
    hn hkTwo hdelta hy code tail j]
  rw [recursiveProfileGapBoundaryExitWordCode_val]
  exact (stoppedWordMass_recursiveProfileGapList n (k + 1) y
    (profileRefinementTrees code.1.returnCount
      (coarseConstrainedTailProfileRest tail)
      (coarseConstrainedTailGapChain
        hn hkTwo hdelta hy code tail) j)
    (coarseConstrainedTailRecursiveEntrance
      hn hkTwo hdelta hy code tail j)
    (coarseConstrainedTailRecursiveEndpoint
      hn hkTwo hdelta hy code tail j)
    (coarseConstrainedTailCanonicalRecursiveCode
      hn hkTwo hdelta hy code tail j)).symm

/-- Complete recursive encoding of a constrained coarse high tail. -/
def encodeConstrainedCoarseTail
    {start n k : ℕ} {hk : k + 1 ≤ n} {profileDelta : ℝ}
    {x y : Point} (hn : 2 ≤ n) (hkTwo : 2 ≤ k + 1)
    (hdelta : profileDelta ≤ 1) (hy : y ∈ candidateBox n)
    (code : CoarseSplitCompletionCode start n k hk profileDelta x y
      (profileInnerBoundary n k y)
      (discBoundary (0, 0) (outerScale n)) (0, 0))
    (tail : CoarseConstrainedTailReturnTuple code) :
    CoarseRecursiveTailEncoding code where
  profile := coarseTailProfile code tail.1
  constrained := tail.2
  count_eq := (coarseReturnCount_eq_profileAtScale_coarseTailProfile
    hn hkTwo code tail.1).symm
  chain := coarseConstrainedTailGapChain hn hkTwo hdelta hy code tail
  entrance := coarseConstrainedTailRecursiveEntrance
    hn hkTwo hdelta hy code tail
  endpoint := coarseConstrainedTailRecursiveEndpoint
    hn hkTwo hdelta hy code tail
  entrance_eq := coarseConstrainedTailRecursiveEntrance_eq_skeleton
    hn hkTwo hdelta hy code tail
  endpoint_eq := coarseConstrainedTailRecursiveEndpoint_eq_skeleton
    hn hkTwo hdelta hy code tail
  fits := coarseConstrainedTailCanonicalRecursiveTree_fits
    hn hkTwo hdelta hy code tail
  gapCode := coarseConstrainedTailCanonicalRecursiveCode
    hn hkTwo hdelta hy code tail

theorem bridgeWord_encodeConstrainedCoarseTail
    {start n k : ℕ} {hk : k + 1 ≤ n} {profileDelta : ℝ}
    {x y : Point} (hn : 2 ≤ n) (hkTwo : 2 ≤ k + 1)
    (hdelta : profileDelta ≤ 1) (hy : y ∈ candidateBox n)
    (code : CoarseSplitCompletionCode start n k hk profileDelta x y
      (profileInnerBoundary n k y)
      (discBoundary (0, 0) (outerScale n)) (0, 0))
    (tail : CoarseConstrainedTailReturnTuple code)
    (j : Fin code.1.returnCount) :
    (encodeConstrainedCoarseTail
      hn hkTwo hdelta hy code tail).bridgeWord hn hkTwo j =
      (tail.1 j).1.1 := by
  exact coarseConstrainedTailCanonicalRecursiveBoundaryCode_eq_bridge
    hn hkTwo hdelta hy code tail j

theorem encodeConstrainedCoarseTail_injective
    {start n k : ℕ} {hk : k + 1 ≤ n} {profileDelta : ℝ}
    {x y : Point} (hn : 2 ≤ n) (hkTwo : 2 ≤ k + 1)
    (hdelta : profileDelta ≤ 1) (hy : y ∈ candidateBox n)
    (code : CoarseSplitCompletionCode start n k hk profileDelta x y
      (profileInnerBoundary n k y)
      (discBoundary (0, 0) (outerScale n)) (0, 0)) :
    Function.Injective
      (encodeConstrainedCoarseTail hn hkTwo hdelta hy code) := by
  intro left right hencoding
  apply Subtype.ext
  funext j
  apply Subtype.ext
  apply Subtype.ext
  have hwords := congrArg
    (fun encoding : CoarseRecursiveTailEncoding code ↦
      encoding.bridgeWord hn hkTwo j) hencoding
  rw [bridgeWord_encodeConstrainedCoarseTail
      hn hkTwo hdelta hy code left j,
    bridgeWord_encodeConstrainedCoarseTail
      hn hkTwo hdelta hy code right j] at hwords
  exact hwords

theorem mass_encodeConstrainedCoarseTail
    {start n k : ℕ} {hk : k + 1 ≤ n} {profileDelta : ℝ}
    {x y : Point} (hn : 2 ≤ n) (hkTwo : 2 ≤ k + 1)
    (hdelta : profileDelta ≤ 1) (hy : y ∈ candidateBox n)
    (code : CoarseSplitCompletionCode start n k hk profileDelta x y
      (profileInnerBoundary n k y)
      (discBoundary (0, 0) (outerScale n)) (0, 0))
    (tail : CoarseConstrainedTailReturnTuple code) :
    (encodeConstrainedCoarseTail
      hn hkTwo hdelta hy code tail).mass =
      ∏ j, stoppedWordMass (tail.1 j).1.1 := by
  apply Finset.prod_congr rfl
  intro j _
  exact coarseConstrainedTailCanonicalRecursiveCodeMass_eq_bridge
    hn hkTwo hdelta hy code tail j

/-! ## Fixed-prefix summation of the high-tail encodings -/

/-- The canonical prefix has centred discarded coordinates and the coarse
return population in its final coordinate. -/
def coarseConstrainedTailPrefix
    {start n k : ℕ} {hk : k + 1 ≤ n} {profileDelta : ℝ}
    {x y : Point}
    (code : CoarseSplitCompletionCode start n k hk profileDelta x y
      (profileInnerBoundary n k y)
      (discBoundary (0, 0) (outerScale n)) (0, 0)) : Profile (k + 1) :=
  fun i ↦ if scaleIndex i = k + 1 then code.1.returnCount
    else centerProfile (k + 1) i

@[simp] theorem profileAtScale_coarseConstrainedTailPrefix
    {start n k : ℕ} {hk : k + 1 ≤ n} {profileDelta : ℝ}
    {x y : Point} (hkTwo : 2 ≤ k + 1)
    (code : CoarseSplitCompletionCode start n k hk profileDelta x y
      (profileInnerBoundary n k y)
      (discBoundary (0, 0) (outerScale n)) (0, 0)) :
    profileAtScale (coarseConstrainedTailPrefix code) (k + 1) =
      code.1.returnCount := by
  unfold profileAtScale
  rw [dif_pos ⟨hkTwo, le_rfl⟩]
  unfold coarseConstrainedTailPrefix
  rw [if_pos]
  change k + 1 - 2 + 2 = k + 1
  omega

theorem profilePrefix_coarseTailProfile_eq
    {start n k : ℕ} {hk : k + 1 ≤ n} {profileDelta : ℝ}
    {x y : Point} (hn : 2 ≤ n) (hkTwo : 2 ≤ k + 1)
    (code : CoarseSplitCompletionCode start n k hk profileDelta x y
      (profileInnerBoundary n k y)
      (discBoundary (0, 0) (outerScale n)) (0, 0))
    (bridges : (j : Fin code.1.returnCount) →
      CoarseSignatureReturnCode x y (profileInnerBoundary n k y) code.1 j) :
    profilePrefix hkTwo hk (coarseTailProfile code bridges) =
      coarseConstrainedTailPrefix code := by
  funext i
  unfold profilePrefix
  by_cases hi : scaleIndex i = k + 1
  · rw [coarseConstrainedTailPrefix, if_pos hi]
    have hindex : k + 1 ≤ scaleIndex
        (⟨i.1, by have := i.2; omega⟩ : Fin (n - 1)) := by
      simpa only [scaleIndex] using le_of_eq hi.symm
    have hcount := coarseReturnCount_eq_profileAtScale_coarseTailProfile
      hn hkTwo code bridges
    calc
      coarseTailProfile code bridges
          (⟨i.1, by have := i.2; omega⟩ : Fin (n - 1)) =
          profileAtScale (coarseTailProfile code bridges)
            (scaleIndex (⟨i.1, by have := i.2; omega⟩ : Fin (n - 1))) :=
        (profileAtScale_scaleIndex _ _).symm
      _ = profileAtScale (coarseTailProfile code bridges) (k + 1) := by
        rw [show scaleIndex
            (⟨i.1, by have := i.2; omega⟩ : Fin (n - 1)) = k + 1 by
          simpa only [scaleIndex] using hi]
      _ = code.1.returnCount := hcount.symm
  · rw [coarseConstrainedTailPrefix, if_neg hi]
    have hindex : ¬ k + 1 ≤ scaleIndex
        (⟨i.1, by have := i.2; omega⟩ : Fin (n - 1)) := by
      intro hle
      have hupp : scaleIndex i ≤ k + 1 := by
        unfold scaleIndex
        have := i.2
        omega
      exact hi (le_antisymm hupp (by simpa only [scaleIndex] using hle))
    unfold coarseTailProfile
    rw [if_neg hindex]
    rfl

/-- Proof-free recursive key restricted to a specified exact prefix. -/
def CoarseRecursiveSpecifiedPrefixKey
    {start n k : ℕ} {hk : k + 1 ≤ n} {profileDelta : ℝ}
    {x y : Point}
    (code : CoarseSplitCompletionCode start n k hk profileDelta x y
      (profileInnerBoundary n k y)
      (discBoundary (0, 0) (outerScale n)) (0, 0))
    (hkTwo : 2 ≤ k + 1) (pref : Profile (k + 1)) :=
  Σ profile : {m : Profile n //
      IsConstrainedProfile profileDelta m ∧
        profileAtScale m (k + 1) = code.1.returnCount ∧
        profilePrefix hkTwo hk m = pref},
    Σ chain : GapChain
        (code.1.returnCount :: (profileSegmentValues profile.1 (k + 1)).tail),
      Σ entrance : {e : Fin code.1.returnCount →
          ProfileCycleMiddlePoint n (k + 1) y //
          ∀ j, (e j).1 = code.1.skeleton.2.1 j},
        Σ endpoint : Fin code.1.returnCount →
            ProfileCycleOuterPoint n (k + 1) y,
          ∀ j, RecursiveProfileGapCode n (k + 1) y
            (profileRefinementTrees code.1.returnCount
              (profileSegmentValues profile.1 (k + 1)).tail chain j)
            (entrance.1 j) (endpoint j)

def CoarseRecursiveSpecifiedPrefixKey.mass
    {start n k : ℕ} {hk : k + 1 ≤ n} {profileDelta : ℝ}
    {x y : Point}
    {code : CoarseSplitCompletionCode start n k hk profileDelta x y
      (profileInnerBoundary n k y)
      (discBoundary (0, 0) (outerScale n)) (0, 0)}
    {hkTwo : 2 ≤ k + 1} {pref : Profile (k + 1)}
    (key : CoarseRecursiveSpecifiedPrefixKey code hkTwo pref) : ℝ≥0∞ :=
  ∏ j, recursiveProfileGapCodeMass n (k + 1) y
    (profileRefinementTrees code.1.returnCount
      (profileSegmentValues key.1.1 (k + 1)).tail key.2.1 j)
    (key.2.2.1.1 j) (key.2.2.2.1 j) (key.2.2.2.2 j)

/-- Forget only the specified-prefix certificate. -/
def CoarseRecursiveSpecifiedPrefixKey.toAmbient
    {start n k : ℕ} {hk : k + 1 ≤ n} {profileDelta : ℝ}
    {x y : Point}
    {code : CoarseSplitCompletionCode start n k hk profileDelta x y
      (profileInnerBoundary n k y)
      (discBoundary (0, 0) (outerScale n)) (0, 0)}
    {hkTwo : 2 ≤ k + 1} {pref : Profile (k + 1)}
    (key : CoarseRecursiveSpecifiedPrefixKey code hkTwo pref) :
    CoarseRecursiveTailKey code :=
  ⟨⟨key.1.1, key.1.2.1, key.1.2.2.1⟩,
    key.2.1, key.2.2.1, key.2.2.2.1, key.2.2.2.2⟩

/-- Canonical specified-prefix key of a constrained high-tail tuple. -/
def specifiedPrefixKeyOfConstrainedTail
    {start n k : ℕ} {hk : k + 1 ≤ n} {profileDelta : ℝ}
    {x y : Point} (hn : 2 ≤ n) (hkTwo : 2 ≤ k + 1)
    (hdelta : profileDelta ≤ 1) (hy : y ∈ candidateBox n)
    (code : CoarseSplitCompletionCode start n k hk profileDelta x y
      (profileInnerBoundary n k y)
      (discBoundary (0, 0) (outerScale n)) (0, 0))
    (tail : CoarseConstrainedTailReturnTuple code) :
    CoarseRecursiveSpecifiedPrefixKey code hkTwo
      (coarseConstrainedTailPrefix code) :=
  let encoding := encodeConstrainedCoarseTail
    hn hkTwo hdelta hy code tail
  ⟨⟨encoding.profile, encoding.constrained, encoding.count_eq,
      profilePrefix_coarseTailProfile_eq hn hkTwo code tail.1⟩,
    encoding.chain, ⟨encoding.entrance, encoding.entrance_eq⟩,
    encoding.endpoint, encoding.gapCode⟩

@[simp] theorem mass_specifiedPrefixKeyOfConstrainedTail
    {start n k : ℕ} {hk : k + 1 ≤ n} {profileDelta : ℝ}
    {x y : Point} (hn : 2 ≤ n) (hkTwo : 2 ≤ k + 1)
    (hdelta : profileDelta ≤ 1) (hy : y ∈ candidateBox n)
    (code : CoarseSplitCompletionCode start n k hk profileDelta x y
      (profileInnerBoundary n k y)
      (discBoundary (0, 0) (outerScale n)) (0, 0))
    (tail : CoarseConstrainedTailReturnTuple code) :
    (specifiedPrefixKeyOfConstrainedTail
      hn hkTwo hdelta hy code tail).mass =
      ∏ j, stoppedWordMass (tail.1 j).1.1 := by
  exact mass_encodeConstrainedCoarseTail hn hkTwo hdelta hy code tail

theorem specifiedPrefixKeyOfConstrainedTail_injective
    {start n k : ℕ} {hk : k + 1 ≤ n} {profileDelta : ℝ}
    {x y : Point} (hn : 2 ≤ n) (hkTwo : 2 ≤ k + 1)
    (hdelta : profileDelta ≤ 1) (hy : y ∈ candidateBox n)
    (code : CoarseSplitCompletionCode start n k hk profileDelta x y
      (profileInnerBoundary n k y)
      (discBoundary (0, 0) (outerScale n)) (0, 0)) :
    Function.Injective
      (specifiedPrefixKeyOfConstrainedTail
        hn hkTwo hdelta hy code) := by
  intro left right hkey
  apply encodeConstrainedCoarseTail_injective hn hkTwo hdelta hy code
  apply CoarseRecursiveTailEncoding.toKey_injective
  exact congrArg CoarseRecursiveSpecifiedPrefixKey.toAmbient hkey

theorem tsum_constrainedBridgeMass_le_specifiedPrefixKeyMass
    {start n k : ℕ} {hk : k + 1 ≤ n} {profileDelta : ℝ}
    {x y : Point} (hn : 2 ≤ n) (hkTwo : 2 ≤ k + 1)
    (hdelta : profileDelta ≤ 1) (hy : y ∈ candidateBox n)
    (code : CoarseSplitCompletionCode start n k hk profileDelta x y
      (profileInnerBoundary n k y)
      (discBoundary (0, 0) (outerScale n)) (0, 0)) :
    (∑' tail : CoarseConstrainedTailReturnTuple code,
        ∏ j, stoppedWordMass (tail.1 j).1.1) ≤
      ∑' key : CoarseRecursiveSpecifiedPrefixKey code hkTwo
          (coarseConstrainedTailPrefix code), key.mass := by
  simpa only [mass_specifiedPrefixKeyOfConstrainedTail
      hn hkTwo hdelta hy code] using
    ENNReal.tsum_comp_le_tsum_of_injective
      (specifiedPrefixKeyOfConstrainedTail_injective
        hn hkTwo hdelta hy code)
      CoarseRecursiveSpecifiedPrefixKey.mass

private theorem tsum_pi_prod_specified
    {q : ℕ} {Code : Fin q → Type*} [∀ j, Countable (Code j)]
    (weight : (j : Fin q) → Code j → ℝ≥0∞) :
    (∑' code : (j : Fin q) → Code j,
        ∏ j, weight j (code j)) =
      ∏ j, ∑' value, weight j value := by
  classical
  induction q with
  | zero => simp
  | succ q ih =>
      calc
        (∑' code : (j : Fin (q + 1)) → Code j,
            ∏ j, weight j (code j)) =
            ∑' pair : Code 0 × ((j : Fin q) → Code j.succ),
              ∏ j, weight j ((Fin.consEquiv Code) pair j) := by
                exact (Equiv.tsum_eq (Fin.consEquiv Code)
                  (fun code ↦ ∏ j, weight j (code j))).symm
        _ = ∑' pair : Code 0 × ((j : Fin q) → Code j.succ),
              weight 0 pair.1 * ∏ j, weight j.succ (pair.2 j) := by
                apply tsum_congr
                intro pair
                rw [Fin.prod_univ_succ]
                simp only [Fin.consEquiv_apply, Fin.cons_zero, Fin.cons_succ]
        _ = ∑' head : Code 0, ∑' tail : (j : Fin q) → Code j.succ,
              weight 0 head * ∏ j, weight j.succ (tail j) :=
                @ENNReal.tsum_prod (Code 0)
                  ((j : Fin q) → Code j.succ)
                  (fun head tail ↦
                    weight 0 head * ∏ j, weight j.succ (tail j))
        _ = ∑' head : Code 0, weight 0 head *
              ∑' tail : (j : Fin q) → Code j.succ,
                ∏ j, weight j.succ (tail j) := by
                  congr 1
                  funext head
                  exact ENNReal.tsum_mul_left
        _ = ∑' head : Code 0, weight 0 head *
              ∏ j : Fin q, ∑' value, weight j.succ value := by
                rw [ih (Code := fun j : Fin q ↦ Code j.succ)
                  (fun j value ↦ weight j.succ value)]
        _ = (∑' head : Code 0, weight 0 head) *
              ∏ j : Fin q, ∑' value, weight j.succ value :=
                ENNReal.tsum_mul_right
        _ = ∏ j : Fin (q + 1), ∑' value, weight j value := by
              rw [Fin.prod_univ_succ]

/-- A count restriction can only decrease the finite fixed-prefix profile
sum. -/
private theorem tsum_constrained_count_prefix_le_sum_prefix
    {n p count : ℕ} (hpTwo : 2 ≤ p) (hpn : p ≤ n)
    (delta : ℝ) (pref : Profile p) (f : Profile n → ℝ≥0∞) :
    (∑' m : {m : Profile n //
        IsConstrainedProfile delta m ∧
          profileAtScale m p = count ∧
          profilePrefix hpTwo hpn m = pref}, f m.1) ≤
      ∑ m ∈ (constrainedProfiles n delta).filter
          (fun m ↦ profilePrefix hpTwo hpn m = pref), f m := by
  let P : Set (Profile n) := {m |
    IsConstrainedProfile delta m ∧
      profileAtScale m p = count ∧
      profilePrefix hpTwo hpn m = pref}
  let F : Finset (Profile n) := (constrainedProfiles n delta).filter
    (fun m ↦ profilePrefix hpTwo hpn m = pref)
  change (∑' m : P, f m.1) ≤ ∑ m ∈ F, f m
  rw [tsum_subtype P f]
  rw [tsum_eq_sum (s := F)]
  · apply Finset.sum_le_sum
    intro m hm
    by_cases hP : m ∈ P
    · rw [Set.indicator_of_mem hP]
    · simp only [Set.indicator, Pi.zero_apply, if_neg hP]
      exact bot_le
  · intro m hm
    have hnot : m ∉ P := by
      intro hP
      apply hm
      rw [Finset.mem_filter]
      exact ⟨mem_constrainedProfiles.mpr hP.1, hP.2.2⟩
    simp only [Set.indicator, Pi.zero_apply, if_neg hnot]

private theorem tsum_constrained_count_prefix_eq_sum
    {n p count : ℕ} (hpTwo : 2 ≤ p) (hpn : p ≤ n)
    (delta : ℝ) (pref : Profile p) (f : Profile n → ℝ≥0∞) :
    (∑' m : {m : Profile n //
        IsConstrainedProfile delta m ∧
          profileAtScale m p = count ∧
          profilePrefix hpTwo hpn m = pref}, f m.1) =
      ∑ m ∈ (constrainedProfiles n delta).filter (fun m ↦
          profileAtScale m p = count ∧
            profilePrefix hpTwo hpn m = pref), f m := by
  let P : Set (Profile n) := {m |
    IsConstrainedProfile delta m ∧
      profileAtScale m p = count ∧
      profilePrefix hpTwo hpn m = pref}
  let F : Finset (Profile n) := (constrainedProfiles n delta).filter
    (fun m ↦ profileAtScale m p = count ∧
      profilePrefix hpTwo hpn m = pref)
  change (∑' m : P, f m.1) = ∑ m ∈ F, f m
  rw [tsum_subtype P f]
  rw [tsum_eq_sum (s := F)]
  · apply Finset.sum_congr rfl
    intro m hm
    apply Set.indicator_of_mem
    rw [Finset.mem_filter] at hm
    exact ⟨mem_constrainedProfiles.mp hm.1, hm.2.1, hm.2.2⟩
  · intro m hm
    have hnot : m ∉ P := by
      intro hP
      apply hm
      rw [Finset.mem_filter]
      exact ⟨mem_constrainedProfiles.mpr hP.1, hP.2.1, hP.2.2⟩
    simp only [Set.indicator, if_neg hnot]

/-- Tonelli expansion of specified-prefix keys into endpoint rows. -/
theorem tsum_specifiedPrefixKeyMass_eq_endpointRows
    {start n k : ℕ} {hk : k + 1 ≤ n} {profileDelta : ℝ}
    {x y : Point} (hkTwo : 2 ≤ k + 1)
    (code : CoarseSplitCompletionCode start n k hk profileDelta x y
      (profileInnerBoundary n k y)
      (discBoundary (0, 0) (outerScale n)) (0, 0))
    (pref : Profile (k + 1)) :
    (∑' key : CoarseRecursiveSpecifiedPrefixKey code hkTwo pref,
        key.mass) =
      ∑' profile : {m : Profile n //
          IsConstrainedProfile profileDelta m ∧
            profileAtScale m (k + 1) = code.1.returnCount ∧
            profilePrefix hkTwo hk m = pref},
        ∑ entrance : {e : Fin code.1.returnCount →
            ProfileCycleMiddlePoint n (k + 1) y //
            ∀ j, (e j).1 = code.1.skeleton.2.1 j},
          ∑ endpoint : Fin code.1.returnCount →
              ProfileCycleOuterPoint n (k + 1) y,
            recursiveProfileEndpointRow n (k + 1) y
              code.1.returnCount
              (profileSegmentValues profile.1 (k + 1)).tail
              entrance.1 endpoint := by
  classical
  unfold CoarseRecursiveSpecifiedPrefixKey
    CoarseRecursiveSpecifiedPrefixKey.mass
  rw [ENNReal.tsum_sigma']
  apply tsum_congr
  intro profile
  simp_rw [ENNReal.tsum_sigma']
  simp_rw [tsum_fintype]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro entrance _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro endpoint _
  unfold recursiveProfileEndpointRow
  apply Finset.sum_congr rfl
  intro chain _
  let (j : Fin code.1.returnCount) : Countable
      (RecursiveProfileGapCode n (k + 1) y
        (profileRefinementTrees code.1.returnCount
          (profileSegmentValues profile.1 (k + 1)).tail chain j)
        (entrance.1 j) (endpoint j)) :=
    recursiveProfileGapCodeCountable n (k + 1) y
      (profileRefinementTrees code.1.returnCount
        (profileSegmentValues profile.1 (k + 1)).tail chain j)
      (entrance.1 j) (endpoint j)
  rw [tsum_pi_prod_specified]
  apply Finset.prod_congr rfl
  intro j _
  exact tsum_recursiveProfileGapCodeMass n (k + 1) y
    (profileRefinementTrees code.1.returnCount
      (profileSegmentValues profile.1 (k + 1)).tail chain j)
    (entrance.1 j) (endpoint j)

/-- At a split beyond the Taylor cutoff, every complementary coarse code
has an exponentially small total constrained high-tail row. -/
theorem eventually_tsum_specifiedPrefixKeyMass_le_coreEnvelope :
    ∀ᶠ n : ℕ in atTop,
      ∀ (k : ℕ) (hk : k + 1 ≤ n) (hkTwo : 2 ≤ k + 1),
        profileUpperTailStart ≤ k + 1 →
      ∀ (start : ℕ) (x y : Point),
      ∀ code : CoarseSplitCompletionCode start n k hk
          profileUpperDelta x y (profileInnerBoundary n k y)
          (discBoundary (0, 0) (outerScale n)) (0, 0),
        (∑' key : CoarseRecursiveSpecifiedPrefixKey code hkTwo
            (coarseConstrainedTailPrefix code), key.mass) ≤
          ENNReal.ofReal (Real.exp (1 / 2 : ℝ) *
            Real.exp (-(2 * (n - (k + 1) : ℕ) : ℝ) +
              profileUpperCoreConstant * (n : ℝ) ^ (3 / 5 : ℝ))) := by
  filter_upwards [eventually_sum_recursiveProfileEndpointRow_le_expHalf]
      with n hrow
  intro k hk hkTwo htail start x y code
  let pref : Profile (k + 1) := coarseConstrainedTailPrefix code
  let E := {e : Fin code.1.returnCount →
      ProfileCycleMiddlePoint n (k + 1) y //
      ∀ j, (e j).1 = code.1.skeleton.2.1 j}
  let : Subsingleton E := ⟨by
    intro left right
    apply Subtype.ext
    funext j
    apply Subtype.ext
    exact (left.2 j).trans (right.2 j).symm⟩
  rcases isEmpty_or_nonempty E with hE | hE
  · let : IsEmpty E := hE
    rw [tsum_specifiedPrefixKeyMass_eq_endpointRows hkTwo code pref]
    simp
  · let : Unique E :=
      { default := Classical.choice hE
        uniq := fun value ↦ Subsingleton.elim value (Classical.choice hE) }
    let F : Finset (Profile n) :=
      (constrainedProfiles n profileUpperDelta).filter (fun m ↦
        profileAtScale m (k + 1) = code.1.returnCount ∧
          profilePrefix hkTwo hk m = pref)
    have hprofile :
        (∑' profile : {m : Profile n //
            IsConstrainedProfile profileUpperDelta m ∧
              profileAtScale m (k + 1) = code.1.returnCount ∧
              profilePrefix hkTwo hk m = pref},
          ∑ entrance : E,
            ∑ endpoint : Fin code.1.returnCount →
                ProfileCycleOuterPoint n (k + 1) y,
              recursiveProfileEndpointRow n (k + 1) y
                code.1.returnCount
                (profileSegmentValues profile.1 (k + 1)).tail
                entrance.1 endpoint) ≤
        ∑ m ∈ F,
          ∑ endpoint : Fin code.1.returnCount →
              ProfileCycleOuterPoint n (k + 1) y,
            recursiveProfileEndpointRow n (k + 1) y
              code.1.returnCount
              (profileSegmentValues m (k + 1)).tail
              (default : E).1 endpoint := by
      simp_rw [Fintype.sum_unique]
      simpa only [F] using le_of_eq
        (tsum_constrained_count_prefix_eq_sum
          (count := code.1.returnCount) hkTwo hk profileUpperDelta pref
          (fun m ↦ ∑ endpoint : Fin code.1.returnCount →
              ProfileCycleOuterPoint n (k + 1) y,
            recursiveProfileEndpointRow n (k + 1) y
              code.1.returnCount
              (profileSegmentValues m (k + 1)).tail
              (default : E).1 endpoint))
    have hpoint : ∀ m ∈ F,
        (∑ endpoint : Fin code.1.returnCount →
            ProfileCycleOuterPoint n (k + 1) y,
          recursiveProfileEndpointRow n (k + 1) y
            code.1.returnCount
            (profileSegmentValues m (k + 1)).tail
            (default : E).1 endpoint) ≤
          ENNReal.ofReal (Real.exp (1 / 2 : ℝ) *
            transitionSegmentProduct (k + 1) (n - (k + 1))
              (profileAtScale m)) := by
      intro m hm
      have hm' := Finset.mem_filter.mp hm
      have hmConstrained : IsConstrainedProfile profileUpperDelta m :=
        mem_constrainedProfiles.mp hm'.1
      have hvalues : profileSegmentValues m (k + 1) =
          code.1.returnCount :: (profileSegmentValues m (k + 1)).tail := by
        calc
          profileSegmentValues m (k + 1) =
              profileAtScale m (k + 1) ::
                (profileSegmentValues m (k + 1)).tail :=
            profileSegmentValues_eq_head_cons_tail hk m
          _ = _ := by rw [hm'.2.1]
      exact hrow y profileUpperDelta m hmConstrained
        (by norm_num [profileUpperDelta]) (k + 1) hkTwo hk
        code.1.returnCount (profileSegmentValues m (k + 1)).tail
        hvalues (default : E).1
    have hfinite :
        (∑ m ∈ F,
          ∑ endpoint : Fin code.1.returnCount →
              ProfileCycleOuterPoint n (k + 1) y,
            recursiveProfileEndpointRow n (k + 1) y
              code.1.returnCount
              (profileSegmentValues m (k + 1)).tail
              (default : E).1 endpoint) ≤
          ∑ m ∈ F, ENNReal.ofReal (Real.exp (1 / 2 : ℝ) *
            transitionSegmentProduct (k + 1) (n - (k + 1))
              (profileAtScale m)) := by
      exact Finset.sum_le_sum fun m hm ↦ hpoint m hm
    have htransition :
        (∑ m ∈ F, transitionSegmentProduct (k + 1) (n - (k + 1))
            (profileAtScale m)) ≤
          constrainedProfileTailWeight n (k + 1) hkTwo hk pref
            profileUpperDelta := by
      unfold constrainedProfileTailWeight
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro m hm
        rw [Finset.mem_filter] at hm ⊢
        exact ⟨hm.1, hm.2.2⟩
      · intro m _hm _hnot
        exact transitionSegmentProduct_nonneg
          (k + 1) (n - (k + 1)) (profileAtScale m)
    have hfiniteTail :
        (∑ m ∈ F, ENNReal.ofReal (Real.exp (1 / 2 : ℝ) *
            transitionSegmentProduct (k + 1) (n - (k + 1))
              (profileAtScale m))) ≤
          ENNReal.ofReal (Real.exp (1 / 2 : ℝ) *
            constrainedProfileTailWeight n (k + 1) hkTwo hk pref
              profileUpperDelta) := by
      calc
        _ = ENNReal.ofReal
            (∑ m ∈ F, Real.exp (1 / 2 : ℝ) *
              transitionSegmentProduct (k + 1) (n - (k + 1))
                (profileAtScale m)) := by
              exact (ENNReal.ofReal_sum_of_nonneg (fun m _ ↦
                mul_nonneg (Real.exp_nonneg _)
                  (transitionSegmentProduct_nonneg
                    (k + 1) (n - (k + 1)) (profileAtScale m)))).symm
        _ = ENNReal.ofReal (Real.exp (1 / 2 : ℝ) *
              ∑ m ∈ F, transitionSegmentProduct
                (k + 1) (n - (k + 1)) (profileAtScale m)) := by
              congr 1
              rw [Finset.mul_sum]
        _ ≤ _ := ENNReal.ofReal_le_ofReal
          (mul_le_mul_of_nonneg_left htransition (Real.exp_nonneg _))
    have htailWeight := constrainedProfileTailWeight_le_coreEnvelope
      htail hk pref
    calc
      (∑' key : CoarseRecursiveSpecifiedPrefixKey code hkTwo
          (coarseConstrainedTailPrefix code), key.mass) =
          ∑' profile : {m : Profile n //
              IsConstrainedProfile profileUpperDelta m ∧
                profileAtScale m (k + 1) = code.1.returnCount ∧
                profilePrefix hkTwo hk m = pref},
            ∑ entrance : E,
              ∑ endpoint : Fin code.1.returnCount →
                  ProfileCycleOuterPoint n (k + 1) y,
                recursiveProfileEndpointRow n (k + 1) y
                  code.1.returnCount
                  (profileSegmentValues profile.1 (k + 1)).tail
                  entrance.1 endpoint := by
            simpa only [pref, E] using
              tsum_specifiedPrefixKeyMass_eq_endpointRows
                hkTwo code (coarseConstrainedTailPrefix code)
      _ ≤ ∑ m ∈ F,
          ∑ endpoint : Fin code.1.returnCount →
              ProfileCycleOuterPoint n (k + 1) y,
            recursiveProfileEndpointRow n (k + 1) y
              code.1.returnCount
              (profileSegmentValues m (k + 1)).tail
              (default : E).1 endpoint := hprofile
      _ ≤ ∑ m ∈ F, ENNReal.ofReal (Real.exp (1 / 2 : ℝ) *
            transitionSegmentProduct (k + 1) (n - (k + 1))
              (profileAtScale m)) := hfinite
      _ ≤ ENNReal.ofReal (Real.exp (1 / 2 : ℝ) *
            constrainedProfileTailWeight n (k + 1) hkTwo hk pref
              profileUpperDelta) := hfiniteTail
      _ ≤ ENNReal.ofReal (Real.exp (1 / 2 : ℝ) *
            Real.exp (-(2 * (n - (k + 1) : ℕ) : ℝ) +
              profileUpperCoreConstant * (n : ℝ) ^ (3 / 5 : ℝ))) := by
        apply ENNReal.ofReal_le_ofReal
        exact mul_le_mul_of_nonneg_left htailWeight (Real.exp_nonneg _)

/-- Source-facing bridge-product form of the high-tail row. -/
theorem eventually_tsum_constrainedCoarseTailBridgeMass_le_coreEnvelope :
    ∀ᶠ n : ℕ in atTop,
      ∀ (k : ℕ) (hk : k + 1 ≤ n) (hkTwo : 2 ≤ k + 1),
        profileUpperTailStart ≤ k + 1 →
      ∀ (start : ℕ) (x y : Point),
      ∀ code : CoarseSplitCompletionCode start n k hk
          profileUpperDelta x y (profileInnerBoundary n k y)
          (discBoundary (0, 0) (outerScale n)) (0, 0),
        (∑' tail : CoarseConstrainedTailReturnTuple code,
            ∏ j, stoppedWordMass (tail.1 j).1.1) ≤
          ENNReal.ofReal (Real.exp (1 / 2 : ℝ) *
            Real.exp (-(2 * (n - (k + 1) : ℕ) : ℝ) +
              profileUpperCoreConstant * (n : ℝ) ^ (3 / 5 : ℝ))) := by
  filter_upwards [eventually_tsum_specifiedPrefixKeyMass_le_coreEnvelope]
      with n hkey
  intro k hk hkTwo htail start x y code
  obtain ⟨_origin, _hdata, hy, _hexit⟩ := code.2.origin_exists
  exact (tsum_constrainedBridgeMass_le_specifiedPrefixKeyMass
    (hkTwo.trans hk) hkTwo (by norm_num [profileUpperDelta]) hy code).trans
      (hkey k hk hkTwo htail start x y code)

end

end Erdos1165.CoarseProfileTailUpper
