/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/
import ErdosProblems.Erdos1165.AsymmetricCoarseNormalizedCompletionRows

/-!
# Successful refinements of a coarse asymmetric completion atom

For one valid coarse completion code, a fine code is the complete tuple of
endpoint-matched return words whose reassembled stopped path has the required
right-hand profile.  Its atom is the corresponding literal stopped-prefix
cylinder.  Thus source coverage and nesting are pathwise, while the measure
calculation exposes exactly the bridge-word sum which the recursive profile
estimate has to bound.
-/

open MeasureTheory Set
open scoped BigOperators ENNReal

namespace Erdos1165.AsymmetricCoarseSuccessfulTailAtoms

open AnnularProfileClocks AsymmetricCoarseCompletionCode
open AsymmetricCoarseNormalizedCompletionRows
open AsymmetricCoarseScanSignature
open AsymmetricCoarseSplitCompletion AsymmetricCoarseSplitCompletionSource
open AsymmetricExtractedReturnCompletion AsymmetricPairTwoStageMass
open AsymmetricExtractedReturnClockRecovery
open AsymmetricSplitLevelSplice
open MarkedBridgeFactorization Proposition13Assembly
open PlanarPotential
open SharedPrefixPairExtraction TerminalSkeletonFactorization
open TerminalGlobalExitSplice TerminalSkeletonInvariance
open TerminalSequentialVisitLaw TerminalSkeletonWords ThickPoint

noncomputable section

/-- The fixed coarse insertion atom attached to a valid retained code. -/
abbrev coarseAtom
    {start n k : ℕ} {hk : k + 1 ≤ n} {profileDelta : ℝ}
    {x y : Point} {returnBoundary globalBoundary : Set Point}
    {globalStart : Point}
    (code : CoarseSplitCompletionCode start n k hk profileDelta x y
      returnBoundary globalBoundary globalStart) :=
  coarseSplitCompletionAtomOfData (x := x) (y := y)
    returnBoundary globalBoundary globalStart code.1 code.2.globalFirst

/-- Words inserted into the fixed complementary skeleton by one return
tuple. -/
def coarseTupleWords
    {start n k : ℕ} {hk : k + 1 ≤ n} {profileDelta : ℝ}
    {x y : Point} {returnBoundary globalBoundary : Set Point}
    {globalStart : Point}
    (code : CoarseSplitCompletionCode start n k hk profileDelta x y
      returnBoundary globalBoundary globalStart)
    (bridges : (j : Fin code.1.returnCount) →
      CoarseSignatureReturnCode x y returnBoundary code.1 j) :
    TerminalSegmentWords code.1.returnCount :=
  fun j ↦ List.ofFn (bridges j).1.1.2

/-- Complete return tuples for which the canonically assembled stopped path
has a successful profile at the right-hand centre. -/
def CoarseSuccessfulReturnTuple
    {start n k : ℕ} {hk : k + 1 ≤ n} {profileDelta : ℝ}
    {x y : Point} {returnBoundary globalBoundary : Set Point}
    {globalStart : Point}
    (code : CoarseSplitCompletionCode start n k hk profileDelta x y
      returnBoundary globalBoundary globalStart) :=
  {bridges : (j : Fin code.1.returnCount) →
      CoarseSignatureReturnCode x y returnBoundary code.1 j //
    SuccessfulPoint
      (trajectory (assembledTerminalPath code.1.skeleton
        (coarseTupleWords code bridges))) n
      (assembledTerminalHorizon code.1.skeleton
        (coarseTupleWords code bridges)) profileDelta y}

noncomputable instance coarseSuccessfulReturnTupleCountable
    {start n k : ℕ} {hk : k + 1 ≤ n} {profileDelta : ℝ}
    {x y : Point} {returnBoundary globalBoundary : Set Point}
    {globalStart : Point}
    (code : CoarseSplitCompletionCode start n k hk profileDelta x y
      returnBoundary globalBoundary globalStart) :
    Countable (CoarseSuccessfulReturnTuple code) := by
  exact Subtype.countable

/-- Literal stopped-prefix cylinder of one successful fine return tuple. -/
def coarseSuccessfulTailAtom
    {start n k : ℕ} {hk : k + 1 ≤ n} {profileDelta : ℝ}
    {x y : Point} {returnBoundary globalBoundary : Set Point}
    {globalStart : Point}
    (code : CoarseSplitCompletionCode start n k hk profileDelta x y
      returnBoundary globalBoundary globalStart)
    (tail : CoarseSuccessfulReturnTuple code) : Set StepPath :=
  stoppedWordCylinder ((coarseAtom code).assemble (Unit.unit, tail.1))

/-- Every successful fine cylinder is contained in its coarse completion
atom. -/
theorem coarseSuccessfulTailAtom_subset_coarseRetainedAtom
    {start n k : ℕ} {hk : k + 1 ≤ n} {profileDelta : ℝ}
    {x y : Point} {returnBoundary globalBoundary : Set Point}
    {globalStart : Point}
    (code : CoarseSplitCompletionCode start n k hk profileDelta x y
      returnBoundary globalBoundary globalStart)
    (tail : CoarseSuccessfulReturnTuple code) :
    coarseSuccessfulTailAtom code tail ⊆ coarseRetainedAtom code := by
  intro omega homega
  exact Set.mem_iUnion.mpr ⟨(Unit.unit, tail.1), homega⟩

/-- A source path in a successful pair event produces a successful fine
tuple over its canonical valid coarse code. -/
theorem stoppedSuccessfulPairEvent_subset_successfulCoarseTailAtoms_of_separation_le
    {start n k : ℕ} {profileDelta : ℝ} {x y : Point}
    (hn : 2 ≤ n) (hk : k + 1 ≤ n)
    (hseparation : AppendixPair.separationLevel n x y ≤ k)
    (hlevel : k ≤ n) :
    stoppedSuccessfulPairEvent start n profileDelta x y ⊆
      ⋃ rooted : SuccessfullyRootedCoarseSplitCompletionCode
          start n k hk profileDelta x y
          (profileInnerBoundary n k y)
          (discBoundary (0, 0) (outerScale n)) (0, 0),
        ⋃ tail : CoarseSuccessfulReturnTuple rooted.1,
          coarseSuccessfulTailAtom rooted.1 tail := by
  rintro source ⟨hsourceX, hsourceY⟩
  obtain ⟨sourceHorizon, hsourceExit, hsourceSuccessful⟩ := hsourceY
  have hstopped : stoppedOuterExitHorizon start n source = sourceHorizon :=
    stoppedOuterExitHorizon_eq_of_isOuterExitTime hsourceExit
  have hsourceExitStopped : IsOuterExitTime
      (trajectory (shiftSteps start source)) n
      (stoppedOuterExitHorizon start n source) := by
    simpa only [Proposition13Measurability.shiftedWalk, hstopped] using
      hsourceExit
  let rooted := sourceSuccessfullyRootedCoarseSplitCompletionCode_of_separation_le
    hn hk hsourceSuccessful.1 hsourceExitStopped hsourceX
  let code := rooted.1
  have hsourceMem : source ∈ coarseRetainedAtom code := by
    unfold coarseRetainedAtom code rooted
      sourceSuccessfullyRootedCoarseSplitCompletionCode_of_separation_le
      sourceCoarseSplitCompletionCode_of_separation_le
    simpa only [sourceCoarseSplitCompletionAtom] using
      (source_mem_coarseSplitCompletionAtomAt
        (x := x) (y := y) (Nat.one_le_of_lt hn) hk
          hsourceSuccessful.1 hsourceExitStopped)
  obtain ⟨bridges, hcylinder⟩ :=
    exists_coarseSignatureReturnCodes_of_mem code.2.globalFirst hsourceMem
  let words : TerminalSegmentWords code.1.returnCount :=
    coarseTupleWords code bridges
  let horizon := assembledTerminalHorizon code.1.skeleton words
  have htailCylinder : shiftSteps start source ∈
      stoppedWordCylinder (assembledTerminalWord code.1.skeleton words) :=
    TerminalSkeletonFactorization.shiftSteps_mem_assembledTerminalWordCylinder_of_mem_assembleAfterPrefix
      hcylinder
  have hfirst : AbsoluteBoundaryFirstAt
      (discBoundary (0, 0) (outerScale n)) (0, 0)
      (assembledTerminalPath code.1.skeleton words) horizon := by
    exact code.2.globalFirst (fun j ↦ (bridges j).1)
  have hsourceExitAt : IsOuterExitTime
      (trajectory (shiftSteps start source)) n horizon := by
    have hactualFirst := absoluteBoundaryFirstAt_of_mem_stoppedWordCylinder
      htailCylinder hfirst
    simpa only [horizon, assembledTerminalHorizon, AbsoluteBoundaryFirstAt, IsOuterExitTime,
      trajectoryFrom_zero_eq_trajectory] using hactualFirst
  have hhorizon : horizon = sourceHorizon :=
    isOuterExitTime_unique hsourceExitAt hsourceExit
  have htrajectory : ∀ q ≤ horizon,
      trajectory (shiftSteps start source) q =
        trajectory (assembledTerminalPath code.1.skeleton words) q := by
    intro q hq
    exact trajectory_eq_assembledTerminalPath_of_mem_stoppedWordCylinder
      htailCylinder hq
  have hsuccessful : SuccessfulPoint
      (trajectory (assembledTerminalPath code.1.skeleton words)) n horizon
        profileDelta y := by
    refine ⟨hsourceSuccessful.1, ?_⟩
    change SuccessfulProfile n profileDelta
      (excursionProfile
        (trajectory (assembledTerminalPath code.1.skeleton words)) n
          horizon y)
    rw [← Proposition13Measurability.excursionProfile_congr_prefix
      htrajectory y, hhorizon]
    exact hsourceSuccessful.2
  let tail : CoarseSuccessfulReturnTuple code := ⟨bridges, by
    simpa only [words, horizon] using hsuccessful⟩
  exact Set.mem_iUnion.mpr ⟨rooted,
    Set.mem_iUnion.mpr ⟨tail, by
      simpa only [coarseSuccessfulTailAtom, coarseAtom, tail,
        words, coarseTupleWords, coarseSplitCompletionAtomOfData,
        fixComplement, restrictBridges, boundaryReturnCompletionAtom]
        using hcylinder⟩⟩

/-- Equality-level wrapper for the original coarse split. -/
theorem stoppedSuccessfulPairEvent_subset_successfulCoarseTailAtoms
    {start n k : ℕ} {profileDelta : ℝ} {x y : Point}
    (hn : 2 ≤ n) (hk : k + 1 ≤ n)
    (hseparation : k = AppendixPair.separationLevel n x y)
    (hlevel : k ≤ n) :
    stoppedSuccessfulPairEvent start n profileDelta x y ⊆
      ⋃ rooted : SuccessfullyRootedCoarseSplitCompletionCode
          start n k hk profileDelta x y
          (profileInnerBoundary n k y)
          (discBoundary (0, 0) (outerScale n)) (0, 0),
        ⋃ tail : CoarseSuccessfulReturnTuple rooted.1,
          coarseSuccessfulTailAtom rooted.1 tail := by
  apply
    stoppedSuccessfulPairEvent_subset_successfulCoarseTailAtoms_of_separation_le
      hn hk (by omega) hlevel

/-- A bridge-product upper bound for every retained coarse code produces the
exact normalized completion rows.  This is the measure-theoretic cancellation
step; the remaining input is purely the recursive profile word-sum estimate. -/
def coarseCompletionTailRowsOfBridgeProduct_of_separation_le
    {start n k : ℕ} {hk : k + 1 ≤ n} {profileDelta radialTail : ℝ}
    {x y : Point} (hn : 2 ≤ n)
    (hseparation : AppendixPair.separationLevel n x y ≤ k)
    (hlevel : k ≤ n)
    (hrow : ∀ code : CoarseSplitCompletionCode start n k hk profileDelta x y
        (profileInnerBoundary n k y)
        (discBoundary (0, 0) (outerScale n)) (0, 0),
      (∑' tail : CoarseSuccessfulReturnTuple code,
        ∏ j, stoppedWordMass ((coarseAtom code).bridgeWord j (tail.1 j))) ≤
        ENNReal.ofReal radialTail * ∏ j, (coarseAtom code).kernel j) :
    CoarseCompletionTailRows (start := start) hk profileDelta x y
      (profileInnerBoundary n k y)
      (discBoundary (0, 0) (outerScale n)) (0, 0)
      (stoppedSuccessfulPairEvent start n profileDelta x y) radialTail where
  TailCode := fun rooted ↦ CoarseSuccessfulReturnTuple rooted.1
  tailCode_countable := fun code ↦
    coarseSuccessfulReturnTupleCountable code.1
  tailAtom := fun code ↦ coarseSuccessfulTailAtom code.1
  successful_subset :=
    stoppedSuccessfulPairEvent_subset_successfulCoarseTailAtoms_of_separation_le
      hn hk hseparation hlevel
  tail_subset := fun code ↦
    coarseSuccessfulTailAtom_subset_coarseRetainedAtom code.1
  tail_sum_le := by
    intro rooted
    let code := rooted.1
    let atom := coarseAtom code
    change (∑' tail : CoarseSuccessfulReturnTuple code,
        fairSteps (coarseSuccessfulTailAtom code tail)) ≤
      ENNReal.ofReal radialTail * fairSteps (coarseRetainedAtom code)
    have hmass (tail : CoarseSuccessfulReturnTuple code) :
        fairSteps (coarseSuccessfulTailAtom code tail) =
          stoppedWordMass (atom.complementWord Unit.unit) *
            ∏ j, stoppedWordMass (atom.bridgeWord j (tail.1 j)) := by
      rw [coarseSuccessfulTailAtom, fairSteps_stoppedWordCylinder,
        stoppedWordMass_assemble]
    simp_rw [hmass]
    rw [ENNReal.tsum_mul_left]
    calc
      stoppedWordMass (atom.complementWord Unit.unit) *
          (∑' tail : CoarseSuccessfulReturnTuple code,
            ∏ j, stoppedWordMass (atom.bridgeWord j (tail.1 j))) ≤
          stoppedWordMass (atom.complementWord Unit.unit) *
            (ENNReal.ofReal radialTail * ∏ j, atom.kernel j) := by
              gcongr
              simpa only [atom] using hrow code
      _ = ENNReal.ofReal radialTail *
          (stoppedWordMass (atom.complementWord Unit.unit) *
            ∏ j, atom.kernel j) := by ac_rfl
      _ = ENNReal.ofReal radialTail * fairSteps (coarseRetainedAtom rooted.1) := by
        have hdenom : fairSteps (coarseRetainedAtom code) =
            atom.weight * ∏ j, atom.kernel j := by
          simpa only [atom, coarseAtom] using
            (fairSteps_coarseRetainedAtom_eq_weight_mul_prod_kernel code)
        rw [hdenom]
        congr 1
        congr 1
        unfold atom coarseAtom coarseSplitCompletionAtomOfData
        rw [fixComplement_weight]
        rfl

/-- Equality-level wrapper for the original coarse split. -/
def coarseCompletionTailRowsOfBridgeProduct
    {start n k : ℕ} {hk : k + 1 ≤ n} {profileDelta radialTail : ℝ}
    {x y : Point} (hn : 2 ≤ n)
    (hseparation : k = AppendixPair.separationLevel n x y)
    (hlevel : k ≤ n)
    (hrow : ∀ code : CoarseSplitCompletionCode start n k hk profileDelta x y
        (profileInnerBoundary n k y)
        (discBoundary (0, 0) (outerScale n)) (0, 0),
      (∑' tail : CoarseSuccessfulReturnTuple code,
        ∏ j, stoppedWordMass ((coarseAtom code).bridgeWord j (tail.1 j))) ≤
        ENNReal.ofReal radialTail * ∏ j, (coarseAtom code).kernel j) :
    CoarseCompletionTailRows (start := start) hk profileDelta x y
      (profileInnerBoundary n k y)
      (discBoundary (0, 0) (outerScale n)) (0, 0)
      (stoppedSuccessfulPairEvent start n profileDelta x y) radialTail :=
  coarseCompletionTailRowsOfBridgeProduct_of_separation_le
    hn (by omega) hlevel hrow

end

end Erdos1165.AsymmetricCoarseSuccessfulTailAtoms
