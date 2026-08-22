/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/
import ErdosProblems.Erdos1165.AsymmetricPaddedConstrainedTailRow
import ErdosProblems.Erdos1165.AsymmetricCoarseCompletionRecovered

/-!
# A normalized coarse upper bound without the level-one condition

At self-centre split level two, constrained continuations define a genuine
stopped-prefix event.  The unrooted coarse atoms are disjoint, so the padded
bridge row normalizes against their exact kernel product and the whole event
has the same radial upper bound.
-/

open Filter MeasureTheory Set
open scoped BigOperators ENNReal

namespace Erdos1165.AsymmetricCoarseHighTailUpper

open AnnularProfileClocks AnnularProfileLiteralAtoms
open AppendixFirstMoment AppendixPair AppendixPairMoment
open AppendixPairCrossingTail GaussianGeometricCutoff
open AsymmetricCoarseCompletionRecovered
open AsymmetricCoarseCompletionSourceGeometry
open AsymmetricCoarseCompletionCode AsymmetricCoarseNormalizedCompletionRows
open AsymmetricCoarseSplitCompletion AsymmetricCoarseSplitCompletionSource
open AsymmetricCoarseSuccessfulTailAtoms
open AsymmetricExtractedReturnClockRecovery
open AsymmetricExtractedReturnCompletion AsymmetricSplitLevelSplice
open AsymmetricPaddedConstrainedTailRow CoarseProfileTailUpper
open AsymmetricPairTwoStageMass
open MarkedBridgeFactorization PlanarPotential Proposition13Assembly
open BufferedSuccessfulProfile
open ProfileWeightUpper Proposition13LiteralAssembly
open TerminalGlobalExitSplice
open TerminalSkeletonFactorization TerminalSkeletonInvariance
open TerminalSequentialVisitLaw TerminalSkeletonWords ThickPoint

noncomputable section

attribute [local instance] Classical.propDecidable

/-- A literal constrained fine cylinder over one unrooted coarse code. -/
def coarseConstrainedTailAtom
    {start n k : ℕ} {hk : k + 1 ≤ n} {profileDelta : ℝ}
    {x y : Point}
    (code : CoarseSplitCompletionCode start n k hk profileDelta x y
      (profileInnerBoundary n k y)
      (discBoundary (0, 0) (outerScale n)) (0, 0))
    (tail : CoarseConstrainedTailReturnTuple code) : Set StepPath :=
  stoppedWordCylinder ((coarseAtom code).assemble (Unit.unit, tail.1))

theorem coarseConstrainedTailAtom_subset_coarseRetainedAtom
    {start n k : ℕ} {hk : k + 1 ≤ n} {profileDelta : ℝ}
    {x y : Point}
    (code : CoarseSplitCompletionCode start n k hk profileDelta x y
      (profileInnerBoundary n k y)
      (discBoundary (0, 0) (outerScale n)) (0, 0))
    (tail : CoarseConstrainedTailReturnTuple code) :
    coarseConstrainedTailAtom code tail ⊆ coarseRetainedAtom code := by
  intro source hsource
  exact Set.mem_iUnion.mpr ⟨(Unit.unit, tail.1), hsource⟩

/-- Union of all unrooted retained atoms at one self-centred split. -/
def unrootedCoarseRetainedEvent
    {start n k : ℕ} (hk : k + 1 ≤ n) (profileDelta : ℝ) (x : Point) :
    Set StepPath :=
  ⋃ code : CoarseSplitCompletionCode start n k hk profileDelta x x
      (profileInnerBoundary n k x)
      (discBoundary (0, 0) (outerScale n)) (0, 0),
    coarseRetainedAtom code

/-- The self-centred constrained high-tail event. -/
def coarseConstrainedHighTailEvent
    {start n k : ℕ} (hk : k + 1 ≤ n) (profileDelta : ℝ) (x : Point) :
    Set StepPath :=
  ⋃ code : CoarseSplitCompletionCode start n k hk profileDelta x x
      (profileInnerBoundary n k x)
      (discBoundary (0, 0) (outerScale n)) (0, 0),
    ⋃ tail : CoarseConstrainedTailReturnTuple code,
      coarseConstrainedTailAtom code tail

theorem coarseConstrainedHighTailEvent_subset_unrootedCoarseRetainedEvent
    {start n k : ℕ} {hk : k + 1 ≤ n} {profileDelta : ℝ} {x : Point} :
    coarseConstrainedHighTailEvent (start := start) hk profileDelta x ⊆
      unrootedCoarseRetainedEvent (start := start) hk profileDelta x := by
  rintro source hsource
  obtain ⟨code, hsource⟩ := Set.mem_iUnion.mp hsource
  obtain ⟨tail, hsource⟩ := Set.mem_iUnion.mp hsource
  exact Set.mem_iUnion.mpr
    ⟨code, coarseConstrainedTailAtom_subset_coarseRetainedAtom
      code tail hsource⟩

/-- A normalized bridge-product row bounds the full unrooted high-tail
union. -/
theorem fairSteps_coarseConstrainedHighTailEvent_le
    {start n k : ℕ} {hk : k + 1 ≤ n} {profileDelta radialTail : ℝ}
    {x : Point}
    (hrow : ∀ code : CoarseSplitCompletionCode start n k hk profileDelta x x
        (profileInnerBoundary n k x)
        (discBoundary (0, 0) (outerScale n)) (0, 0),
      (∑' tail : CoarseConstrainedTailReturnTuple code,
        ∏ j, stoppedWordMass ((coarseAtom code).bridgeWord j (tail.1 j))) ≤
        ENNReal.ofReal radialTail * ∏ j, (coarseAtom code).kernel j) :
    fairSteps (coarseConstrainedHighTailEvent
        (start := start) hk profileDelta x) ≤ ENNReal.ofReal radialTail := by
  let Code := CoarseSplitCompletionCode start n k hk profileDelta x x
    (profileInnerBoundary n k x)
    (discBoundary (0, 0) (outerScale n)) (0, 0)
  have htail (code : Code) :
      (∑' tail : CoarseConstrainedTailReturnTuple code,
          fairSteps (coarseConstrainedTailAtom code tail)) ≤
        ENNReal.ofReal radialTail * fairSteps (coarseRetainedAtom code) := by
    let atom := coarseAtom code
    have hmass (tail : CoarseConstrainedTailReturnTuple code) :
        fairSteps (coarseConstrainedTailAtom code tail) =
          stoppedWordMass (atom.complementWord Unit.unit) *
            ∏ j, stoppedWordMass (atom.bridgeWord j (tail.1 j)) := by
      rw [coarseConstrainedTailAtom, fairSteps_stoppedWordCylinder,
        stoppedWordMass_assemble]
    simp_rw [hmass]
    rw [ENNReal.tsum_mul_left]
    calc
      stoppedWordMass (atom.complementWord Unit.unit) *
          (∑' tail : CoarseConstrainedTailReturnTuple code,
            ∏ j, stoppedWordMass (atom.bridgeWord j (tail.1 j))) ≤
          stoppedWordMass (atom.complementWord Unit.unit) *
            (ENNReal.ofReal radialTail * ∏ j, atom.kernel j) := by
              gcongr
              simpa only [atom] using hrow code
      _ = ENNReal.ofReal radialTail *
          (stoppedWordMass (atom.complementWord Unit.unit) *
            ∏ j, atom.kernel j) := by ac_rfl
      _ = ENNReal.ofReal radialTail * fairSteps (coarseRetainedAtom code) := by
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
  calc
    fairSteps (coarseConstrainedHighTailEvent
        (start := start) hk profileDelta x) ≤
        ∑' code : Code,
          fairSteps (⋃ tail : CoarseConstrainedTailReturnTuple code,
            coarseConstrainedTailAtom code tail) := measure_iUnion_le _
    _ ≤ ∑' code : Code,
          ∑' tail : CoarseConstrainedTailReturnTuple code,
            fairSteps (coarseConstrainedTailAtom code tail) :=
      ENNReal.tsum_le_tsum fun _ ↦ measure_iUnion_le _
    _ ≤ ∑' code : Code,
          ENNReal.ofReal radialTail * fairSteps (coarseRetainedAtom code) :=
      ENNReal.tsum_le_tsum htail
    _ = ENNReal.ofReal radialTail *
          ∑' code : Code, fairSteps (coarseRetainedAtom code) :=
      ENNReal.tsum_mul_left
    _ = ENNReal.ofReal radialTail *
          fairSteps (unrootedCoarseRetainedEvent
            (start := start) hk profileDelta x) := by
      rw [unrootedCoarseRetainedEvent,
        measure_iUnion coarseRetainedAtom_pairwise
          measurableSet_coarseRetainedAtom]
    _ ≤ ENNReal.ofReal radialTail * 1 := by
      gcongr
      exact prob_le_one
    _ = ENNReal.ofReal radialTail := mul_one _

/-! ## Source coverage of the unrooted high-tail event -/

/-- Fill discarded low coordinates by the parabola and retain the stopped
source profile from scale `k+1` onward. -/
def stoppedHighTailProfile
    (start n k : ℕ) (x : Point) (source : StepPath) : Profile n :=
  fun i ↦
    if k + 1 ≤ AppendixFirstMoment.scaleIndex i then
      internalProfile
        (excursionProfile (trajectory (shiftSteps start source)) n
          (stoppedOuterExitHorizon start n source) x) i
    else centerProfile n i

/-- The source-dependent coarse witness does not logically require a
successful level-one profile; only the centre and the stopped outer exit are
needed. -/
def sourceUnrootedCoarseSplitCompletionWitness
    {start n k : ℕ} {profileDelta : ℝ} {x y : Point} {source : StepPath}
    (hn : 2 ≤ n) (hk : k + 1 ≤ n)
    (hy : y ∈ candidateBox n)
    (hexit : IsOuterExitTime (trajectory (shiftSteps start source)) n
      (stoppedOuterExitHorizon start n source)) :
    CoarseSplitCompletionWitness hk (profileDelta := profileDelta) x y
      (profileInnerBoundary n k y)
      (discBoundary (0, 0) (outerScale n)) (0, 0)
      (sourceCoarseSplitCompletionData start n k hk x y source) where
  origin_exists := ⟨source, rfl, hy, hexit⟩
  globalFirst := sourceCoarseSplitCompletionGlobalFirst
    (Nat.one_le_of_lt hn) hk hy hexit
  recovered := by
    simpa only [sourceCoarseSplitCompletionAtom] using
      (sourceCoarseSplitCompletionData_recovered hn hk hy hexit)

def sourceUnrootedCoarseSplitCompletionCode
    {start n k : ℕ} {profileDelta : ℝ} {x y : Point} {source : StepPath}
    (hn : 2 ≤ n) (hk : k + 1 ≤ n)
    (hy : y ∈ candidateBox n)
    (hexit : IsOuterExitTime (trajectory (shiftSteps start source)) n
      (stoppedOuterExitHorizon start n source)) :
    CoarseSplitCompletionCode start n k hk profileDelta x y
      (profileInnerBoundary n k y)
      (discBoundary (0, 0) (outerScale n)) (0, 0) :=
  ⟨sourceCoarseSplitCompletionData start n k hk x y source,
    sourceUnrootedCoarseSplitCompletionWitness hn hk hy hexit⟩

theorem source_mem_sourceUnrootedCoarseRetainedAtom
    {start n k : ℕ} {profileDelta : ℝ} {x y : Point} {source : StepPath}
    (hn : 2 ≤ n) (hk : k + 1 ≤ n)
    (hy : y ∈ candidateBox n)
    (hexit : IsOuterExitTime (trajectory (shiftSteps start source)) n
      (stoppedOuterExitHorizon start n source)) :
    source ∈ coarseRetainedAtom
      (sourceUnrootedCoarseSplitCompletionCode
        (profileDelta := profileDelta) (x := x) (y := y)
        hn hk hy hexit) := by
  unfold coarseRetainedAtom sourceUnrootedCoarseSplitCompletionCode
    sourceUnrootedCoarseSplitCompletionWitness
  simpa only [sourceCoarseSplitCompletionAtom] using
    (source_mem_coarseSplitCompletionAtomAt
      (x := x) (y := y) (Nat.one_le_of_lt hn) hk hy hexit)

/-- A stopped source with constrained retained coordinates is represented by
one literal constrained tail of its canonical unrooted self code. -/
theorem mem_coarseConstrainedHighTailEvent_of_stoppedHighTailProfile
    {start n k : ℕ} {profileDelta : ℝ} {x : Point} {source : StepPath}
    (hn : 2 ≤ n) (hk : k + 1 ≤ n)
    (hx : x ∈ candidateBox n)
    (hexit : IsOuterExitTime (trajectory (shiftSteps start source)) n
      (stoppedOuterExitHorizon start n source))
    (hprofile : IsConstrainedProfile profileDelta
      (stoppedHighTailProfile start n k x source)) :
    source ∈ coarseConstrainedHighTailEvent
      (start := start) hk profileDelta x := by
  let code := sourceUnrootedCoarseSplitCompletionCode
    (profileDelta := profileDelta) (x := x) (y := x)
    hn hk hx hexit
  have hsourceMem : source ∈ coarseRetainedAtom code := by
    exact source_mem_sourceUnrootedCoarseRetainedAtom hn hk hx hexit
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
    simpa only [horizon, assembledTerminalHorizon,
      AbsoluteBoundaryFirstAt, IsOuterExitTime,
      trajectoryFrom_zero_eq_trajectory] using hactualFirst
  have hhorizon : horizon = stoppedOuterExitHorizon start n source :=
    isOuterExitTime_unique hsourceExitAt hexit
  have htrajectory : ∀ q ≤ horizon,
      trajectory (shiftSteps start source) q =
        trajectory (assembledTerminalPath code.1.skeleton words) q := by
    intro q hq
    exact trajectory_eq_assembledTerminalPath_of_mem_stoppedWordCylinder
      htailCylinder hq
  have hexcursion :
      excursionProfile
          (trajectory (assembledTerminalPath code.1.skeleton words)) n
          horizon x =
        excursionProfile (trajectory (shiftSteps start source)) n
          (stoppedOuterExitHorizon start n source) x := by
    rw [← hhorizon]
    exact (Proposition13Measurability.excursionProfile_congr_prefix
      htrajectory x).symm
  have htailProfile :
      coarseTailProfile code bridges =
        stoppedHighTailProfile start n k x source := by
    funext i
    unfold coarseTailProfile stoppedHighTailProfile
    split_ifs
    · simpa only [words, horizon] using congrFun
        (congrArg internalProfile hexcursion) i
    · rfl
  let tail : CoarseConstrainedTailReturnTuple code := ⟨bridges, by
    rw [htailProfile]
    exact hprofile⟩
  exact Set.mem_iUnion.mpr ⟨code,
    Set.mem_iUnion.mpr ⟨tail, by
      simpa only [coarseConstrainedTailAtom, coarseAtom, tail,
        words, coarseTupleWords, coarseSplitCompletionAtomOfData,
        fixComplement, restrictBridges, boundaryReturnCompletionAtom]
        using hcylinder⟩⟩

/-- At separation level at most two, every completion in the rooted pair
atom retains all internal profile coordinates from scale three onward.  Its
possible low-coordinate damage is therefore absorbed by the self-centred
high-tail event. -/
theorem sourceCoarseSplitCompletionAtom_subset_highTail_of_separation_le_two
    {start n k : ℕ} {profileDelta : ℝ} {x y : Point} {source : StepPath}
    (hn : 2 ≤ n) (hk : k + 1 ≤ n) (hself : 2 + 1 ≤ n)
    (hy : y ∈ candidateBox n)
    (hexit : IsOuterExitTime (trajectory (shiftSteps start source)) n
      (stoppedOuterExitHorizon start n source))
    (hseparation : separationLevel n x y ≤ k) (hlevel : k ≤ n)
    (htwo : separationLevel n x y ≤ 2)
    (hsourceX : source ∈ stoppedSuccessfulPointEvent
      start n profileDelta x) :
    (sourceCoarseSplitCompletionAtom (x := x) (y := y)
      source (Nat.one_le_of_lt hn) hk hy hexit).event ⊆
      coarseConstrainedHighTailEvent
        (start := start) hself profileDelta x := by
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
  have hactualHorizon :
      stoppedOuterExitHorizon start n omega = horizon :=
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
        (assembledTerminalWord data.skeleton referenceWords) := by
    exact TerminalSkeletonFactorization.shiftSteps_mem_assembledTerminalWordCylinder_of_mem_assembleAfterPrefix
      hsourceCylinder
  have hreferenceFirst : AbsoluteBoundaryFirstAt
      (discBoundary (0, 0) (outerScale n)) (0, 0)
      (assembledTerminalPath data.skeleton referenceWords)
      referenceHorizon := by
    exact sourceCoarseSplitCompletionGlobalFirst
      (Nat.one_le_of_lt hn) hk hy hexit (fun j ↦ (reference j).1)
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
  have hsourceReferenceTrajectory : ∀ r ≤ referenceHorizon,
      trajectory (shiftSteps start source) r =
        trajectory (assembledTerminalPath data.skeleton referenceWords) r := by
    intro r hr
    exact trajectory_eq_assembledTerminalPath_of_mem_stoppedWordCylinder
      hsourceTail hr
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
  have hconstrained : IsConstrainedProfile profileDelta
      (stoppedHighTailProfile start n 2 x omega) := by
    have hsourceConstrained :=
      internalProfile_isConstrained hsourceSuccessful.2
    intro i
    by_cases hi : 2 + 1 ≤ scaleIndex i
    · have hcoord :
          internalProfile
              (excursionProfile (trajectory (shiftSteps start omega)) n
                (stoppedOuterExitHorizon start n omega) x) i =
            internalProfile
              (excursionProfile (trajectory (shiftSteps start source)) n
                (stoppedOuterExitHorizon start n source) x) i := by
        simp only [internalProfile_apply]
        rw [hactualHorizon]
        exact hactualSourceProfile
          ⟨scaleIndex i, by unfold scaleIndex; omega⟩ (by
            right
            exact (Nat.add_le_add_right htwo 1).trans hi)
      unfold stoppedHighTailProfile
      rw [if_pos hi, hcoord]
      exact hsourceConstrained i
    · unfold stoppedHighTailProfile
      rw [if_neg hi]
      exact mem_constrainedProfiles.mp
        (centerProfile_mem_constrainedProfiles n profileDelta) i
  apply mem_coarseConstrainedHighTailEvent_of_stoppedHighTailProfile
    hn hself hsourceSuccessful.1
  · simpa only [hactualHorizon] using hactualExit
  · exact hconstrained

/-- Rooted retained atoms at separation one or two are contained in the
self-centred high-tail event. -/
theorem coarseRetainedAtom_subset_highTail_of_separation_le_two
    {start n k : ℕ} {hk : k + 1 ≤ n} {profileDelta : ℝ} {x y : Point}
    (hn : 2 ≤ n) (hself : 2 + 1 ≤ n)
    (hseparation : separationLevel n x y ≤ k)
    (hlevel : k ≤ n) (htwo : separationLevel n x y ≤ 2)
    (code : SuccessfullyRootedCoarseSplitCompletionCode
      start n k hk profileDelta x y
      (profileInnerBoundary n k y)
      (discBoundary (0, 0) (outerScale n)) (0, 0)) :
    coarseRetainedAtom code.1 ⊆
      coarseConstrainedHighTailEvent
        (start := start) hself profileDelta x := by
  obtain ⟨origin, hdata, hy, hexit, hx⟩ := code.2
  have hsource :=
    sourceCoarseSplitCompletionAtom_subset_highTail_of_separation_le_two
      hn hk hself hy hexit hseparation hlevel htwo hx
  unfold coarseRetainedAtom
  rw [coarseSplitCompletionAtomOfData_event_eq_of_data_eq hdata
    code.1.2.globalFirst
    (sourceCoarseSplitCompletionGlobalFirst
      (Nat.one_le_of_lt hn) hk hy hexit)]
  simpa only [sourceCoarseSplitCompletionAtom] using hsource

theorem coarseRetainedEvent_subset_highTail_of_separation_le_two
    {start n k : ℕ} {hk : k + 1 ≤ n} {profileDelta : ℝ} {x y : Point}
    (hn : 2 ≤ n) (hself : 2 + 1 ≤ n)
    (hseparation : separationLevel n x y ≤ k)
    (hlevel : k ≤ n) (htwo : separationLevel n x y ≤ 2) :
    coarseRetainedEvent (start := start) hk profileDelta x y
        (profileInnerBoundary n k y)
        (discBoundary (0, 0) (outerScale n)) (0, 0) ⊆
      coarseConstrainedHighTailEvent
        (start := start) hself profileDelta x := by
  rintro omega homega
  obtain ⟨code, hcode⟩ := Set.mem_iUnion.mp homega
  exact coarseRetainedAtom_subset_highTail_of_separation_le_two
    hn hself hseparation hlevel htwo code hcode

/-! ## Quantitative self-centred upper bound -/

/-- The reserve between the sharp padded coefficient and the public profile
coefficient absorbs the fixed split and logarithmic padding. -/
theorem eventually_fairSteps_coarseConstrainedHighTailEvent_le_envelope :
    ∀ᶠ q : ℕ in atTop, ∀ (hqThree : 2 + 1 ≤ q)
      (start : ℕ) (x : Point),
      fairSteps (coarseConstrainedHighTailEvent
          (start := start) (n := q) (k := 2) hqThree
          profileUpperDelta x) ≤
        ENNReal.ofReal (Real.exp (-2 * (q : ℝ) +
          (profileUpperConstant * (q : ℝ) ^ (3 / 5 : ℝ) +
            prefixProfileCostDeficit))) := by
  filter_upwards
      [eventually_constrainedBridgeMass_le_radialTail_mul_kernel_all,
       eventually_decorrelationPadding_budget_rpow
        (by norm_num : (0 : ℝ) < 1),
       eventually_decorrelationPadding_budget_rpow
        (by norm_num : (0 : ℝ) < 3 / 5),
       eventually_geometricCutoff_le_decorrelationPadding,
       eventually_ge_atTop 3]
      with q hrow hpaddingOne hpaddingPow hpaddingLower hq
  intro hqThree start x
  have hqOne : (1 : ℝ) ≤ q := by exact_mod_cast (by omega : 1 ≤ q)
  have hpowOne : (1 : ℝ) ≤ (q : ℝ) ^ (3 / 5 : ℝ) :=
    Real.one_le_rpow hqOne (by norm_num)
  have hadd : 2 + decorrelationPadding q ≤ q := by
    norm_num [Real.rpow_one] at hpaddingOne
    have hcast : ((2 + decorrelationPadding q : ℕ) : ℝ) ≤ (q : ℝ) := by
      push_cast
      have hp0 : (0 : ℝ) ≤ (decorrelationPadding q : ℝ) := by positivity
      nlinarith
    exact_mod_cast hcast
  have hcutoff : 2 ≤ decorrelationCutoff q := by
    unfold decorrelationCutoff
    omega
  have hprefEq : pairPrefixScale q 2 = 2 + decorrelationPadding q :=
    pairPrefixScale_eq_of_add_le hadd
  have hpq : pairPrefixScale q 2 ≤ q := by
    unfold pairPrefixScale
    exact min_le_left _ _
  have hpaddingTwo : 2 ≤ decorrelationPadding q :=
    (show 2 ≤ geometricCutoff by
      norm_num [geometricCutoff, geometricCutoffBase]).trans hpaddingLower
  have hkp : 2 + 1 < pairPrefixScale q 2 := by
    rw [hprefEq]
    omega
  have htail : profileUpperTailStart ≤ pairPrefixScale q 2 := by
    rw [hprefEq]
    exact (show profileUpperTailStart ≤ geometricCutoff by
      norm_num [profileUpperTailStart, geometricCutoff,
        geometricCutoffBase]).trans (hpaddingLower.trans (by omega))
  have hbridge : ∀ code : CoarseSplitCompletionCode start q 2 hqThree
      profileUpperDelta x x (profileInnerBoundary q 2 x)
      (discBoundary (0, 0) (outerScale q)) (0, 0),
      (∑' tail : CoarseConstrainedTailReturnTuple code,
          ∏ j, stoppedWordMass ((coarseAtom code).bridgeWord j (tail.1 j))) ≤
        ENNReal.ofReal (Real.exp 1 *
          Real.exp (-(2 * (q - pairPrefixScale q 2 : ℕ) : ℝ) +
            (profileUpperCoreConstant + 101) *
              (q : ℝ) ^ (3 / 5 : ℝ))) *
          ∏ j, (coarseAtom code).kernel j := by
    intro code
    have h := hrow 2 hcutoff hqThree (by omega) hkp htail code
    have hword (tail : CoarseConstrainedTailReturnTuple code)
        (j : Fin code.1.returnCount) :
        (coarseAtom code).bridgeWord j (tail.1 j) = (tail.1 j).1.1 := rfl
    simpa only [hword] using h
  have hmass := fairSteps_coarseConstrainedHighTailEvent_le hbridge
  refine hmass.trans (ENNReal.ofReal_le_ofReal ?_)
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hsubcast : ((q - pairPrefixScale q 2 : ℕ) : ℝ) =
      (q : ℝ) - (pairPrefixScale q 2 : ℝ) := by
    rw [Nat.cast_sub hpq]
  have hprefCast : (pairPrefixScale q 2 : ℝ) =
      (2 : ℝ) + (decorrelationPadding q : ℝ) := by
    exact_mod_cast hprefEq
  have hcore0 : 0 ≤ profileUpperCoreConstant := by
    unfold profileUpperCoreConstant
    have ha : 0 ≤ ProfileA11Assembly.a11ErrorCoefficient
        profileUpperDelta 2 1 11 :=
      ProfileA11Assembly.a11ErrorCoefficient_nonneg
        (by norm_num [profileUpperDelta]) (by norm_num) (by norm_num)
          (by norm_num)
    have hlog : 0 ≤ Real.log
        ((constrainedProfiles profileUpperTailStart
          profileUpperDelta).card + 1) := by
      apply Real.log_nonneg
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr (by omega :
        (constrainedProfiles profileUpperTailStart
          profileUpperDelta).card + 1 ≠ 0)
    positivity
  have hdeficit0 : 0 ≤ prefixProfileCostDeficit :=
    prefixProfileCostDeficit_nonneg
  norm_num at hpaddingPow
  rw [hsubcast, hprefCast]
  unfold profileUpperConstant
  nlinarith

theorem eventually_fairSteps_real_coarseConstrainedHighTailEvent_le_pairPointEnvelope
    {delta : ℝ} :
    ∀ᶠ blockIndex : ℕ in atTop,
      ∀ (hqThree : 2 + 1 ≤ Proposition13Scales.scaleIndex delta blockIndex)
        (start : ℕ) (x : Point),
      fairSteps.real (coarseConstrainedHighTailEvent
          (start := start)
          (n := Proposition13Scales.scaleIndex delta blockIndex) (k := 2)
          hqThree profileUpperDelta x) ≤
        pairPointEnvelope delta blockIndex := by
  have hscaleNat : Tendsto (Proposition13Scales.scaleIndex delta) atTop atTop :=
    tendsto_natCast_atTop_iff.mp
      (Proposition13Scales.tendsto_scaleIndex_atTop delta)
  have hupper := hscaleNat.eventually
    eventually_fairSteps_coarseConstrainedHighTailEvent_le_envelope
  filter_upwards [hupper] with blockIndex hupper
  intro hqThree start x
  have h := hupper hqThree start x
  have hreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top h
  simpa only [Measure.real, pairPointEnvelope,
    ENNReal.toReal_ofReal (Real.exp_nonneg _)] using hreal

end

end Erdos1165.AsymmetricCoarseHighTailUpper
