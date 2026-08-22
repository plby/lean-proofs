/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/
import ErdosProblems.Erdos1165.AsymmetricCoarseCompletionRecovered

/-!
# Valid source-independent coarse completion codes

The retained atom fixes the stopped prefix, compressed return skeleton,
left scanner prefix and the single right split transition.  It does not fix
the strictly deeper right profile, which remains available for the tail row.
-/

open MeasureTheory Set

namespace Erdos1165.AsymmetricCoarseCompletionCode

open AnnularProfileClocks AppendixPair
open AsymmetricCoarseCompletionRecovered
open AsymmetricCoarseSplitCompletion AsymmetricCoarseSplitCompletionSource
open AsymmetricCoarseCompletionWitness AsymmetricSplitCompletionSource
open BufferedStoppedSuccessfulPointEvent
open MarkedBridgeFactorization Proposition13Assembly
open SharedPrefixPairExtraction TerminalSkeletonWords ThickPoint
open TerminalSequentialVisitLaw TerminalSkeletonInvariance

noncomputable section

attribute [local instance] Classical.propDecidable

/-- Pathwise validity of one coarse retained atom.  Recovery is the
prefix-free field: two distinct valid data records cannot share a path. -/
structure CoarseSplitCompletionWitness
    {start n k : ℕ} (hk : k + 1 ≤ n) {profileDelta : ℝ}
    (x y : Point) (returnBoundary globalBoundary : Set Point)
    (globalStart : Point) (data : CoarseSplitCompletionData start n k) : Prop
    where
  /-- Every admissible code is rooted in one genuine left-successful source.
  Keeping that source certificate, rather than baking one particular
  buffered consequence into the code, lets the same completion atoms be
  used at the exceptional separation levels. -/
  origin_exists : ∃ origin : StepPath,
    data = sourceCoarseSplitCompletionData start n k hk x y origin ∧
      y ∈ candidateBox n ∧
      IsOuterExitTime (trajectory (shiftSteps start origin)) n
        (stoppedOuterExitHorizon start n origin)
  globalFirst : ∀ bridges : (j : Fin data.returnCount) →
      BoundaryExitWordCode returnBoundary
        (data.skeleton.2.1 j) (data.skeleton.2.2 j),
    AbsoluteBoundaryFirstAt globalBoundary globalStart
      (assembledTerminalPath data.skeleton
        (fun j ↦ List.ofFn (bridges j).1.2))
      (assembledTerminalHorizon data.skeleton
        (fun j ↦ List.ofFn (bridges j).1.2))
  recovered :
    (coarseSplitCompletionAtomOfData (x := x) (y := y)
      returnBoundary globalBoundary globalStart data globalFirst).event ⊆
      {omega | sourceCoarseSplitCompletionData start n k hk x y omega = data}

/-- Countable type of all genuinely valid coarse retained completion atoms. -/
abbrev CoarseSplitCompletionCode
    (start n k : ℕ) (hk : k + 1 ≤ n) (profileDelta : ℝ)
    (x y : Point) (returnBoundary globalBoundary : Set Point)
    (globalStart : Point) :=
  {data : CoarseSplitCompletionData start n k //
    CoarseSplitCompletionWitness hk (profileDelta := profileDelta) x y
      returnBoundary globalBoundary globalStart data}

/-- A coarse code together with a genuine successful source at the retained
left centre.  The analytic bridge row is stated for the underlying unrooted
code; this extra certificate is used only for retained-event containment. -/
abbrev SuccessfullyRootedCoarseSplitCompletionCode
    (start n k : ℕ) (hk : k + 1 ≤ n) (profileDelta : ℝ)
    (x y : Point) (returnBoundary globalBoundary : Set Point)
    (globalStart : Point) :=
  {code : CoarseSplitCompletionCode start n k hk profileDelta x y
      returnBoundary globalBoundary globalStart //
    ∃ origin : StepPath,
      code.1 = sourceCoarseSplitCompletionData start n k hk x y origin ∧
        y ∈ candidateBox n ∧
        IsOuterExitTime (trajectory (shiftSteps start origin)) n
          (stoppedOuterExitHorizon start n origin) ∧
        origin ∈ stoppedSuccessfulPointEvent start n profileDelta x}

attribute [instance] coarseSplitCompletionDataCountable

/-- The genuine coarse retained atom represented by a valid code. -/
def coarseRetainedAtom
    {start n k : ℕ} {hk : k + 1 ≤ n} {profileDelta : ℝ}
    {x y : Point} {returnBoundary globalBoundary : Set Point}
    {globalStart : Point}
    (code : CoarseSplitCompletionCode start n k hk profileDelta x y
      returnBoundary globalBoundary globalStart) : Set StepPath :=
  (coarseSplitCompletionAtomOfData (x := x) (y := y)
    returnBoundary globalBoundary globalStart code.1
    code.2.globalFirst).event

/-- The event represented by a completion atom depends only on its data;
the dependent boundary-first proof is propositionally irrelevant. -/
theorem coarseSplitCompletionAtomOfData_event_eq_of_data_eq
    {start n splitLevel : ℕ} {x y : Point}
    {returnBoundary globalBoundary : Set Point} {globalStart : Point}
    {left right : CoarseSplitCompletionData start n splitLevel}
    (hdata : left = right)
    (hleft : ∀ bridges : (j : Fin left.returnCount) →
        BoundaryExitWordCode returnBoundary
          (left.skeleton.2.1 j) (left.skeleton.2.2 j),
      AbsoluteBoundaryFirstAt globalBoundary globalStart
        (assembledTerminalPath left.skeleton
          (fun j ↦ List.ofFn (bridges j).1.2))
        (assembledTerminalHorizon left.skeleton
          (fun j ↦ List.ofFn (bridges j).1.2)))
    (hright : ∀ bridges : (j : Fin right.returnCount) →
        BoundaryExitWordCode returnBoundary
          (right.skeleton.2.1 j) (right.skeleton.2.2 j),
      AbsoluteBoundaryFirstAt globalBoundary globalStart
        (assembledTerminalPath right.skeleton
          (fun j ↦ List.ofFn (bridges j).1.2))
        (assembledTerminalHorizon right.skeleton
          (fun j ↦ List.ofFn (bridges j).1.2))) :
    (coarseSplitCompletionAtomOfData (x := x) (y := y)
        returnBoundary globalBoundary globalStart left hleft).event =
      (coarseSplitCompletionAtomOfData (x := x) (y := y)
        returnBoundary globalBoundary globalStart right hright).event := by
  subst right
  rfl

theorem measurableSet_coarseRetainedAtom
    {start n k : ℕ} {hk : k + 1 ≤ n} {profileDelta : ℝ}
    {x y : Point} {returnBoundary globalBoundary : Set Point}
    {globalStart : Point}
    (code : CoarseSplitCompletionCode start n k hk profileDelta x y
      returnBoundary globalBoundary globalStart) :
    MeasurableSet (coarseRetainedAtom code) := by
  unfold coarseRetainedAtom ComplementarySkeletonAtom.event
  exact measurableSet_stoppedWordEvent _

/-- Exact mass of a coarse retained atom.  The bridge-kernel product is
part of its mass; it cannot be silently discarded when a deeper refinement
is conditioned on this event. -/
theorem fairSteps_coarseRetainedAtom_eq_weight_mul_prod_kernel
    {start n k : ℕ} {hk : k + 1 ≤ n} {profileDelta : ℝ}
    {x y : Point} {returnBoundary globalBoundary : Set Point}
    {globalStart : Point}
    (code : CoarseSplitCompletionCode start n k hk profileDelta x y
      returnBoundary globalBoundary globalStart) :
    fairSteps (coarseRetainedAtom code) =
      (coarseSplitCompletionAtomOfData (x := x) (y := y)
        returnBoundary globalBoundary globalStart code.1
        code.2.globalFirst).weight *
      ∏ j, (coarseSplitCompletionAtomOfData (x := x) (y := y)
        returnBoundary globalBoundary globalStart code.1
        code.2.globalFirst).kernel j := by
  exact fairSteps_event_eq_weight_mul_prod_kernel _

/-- Recovery makes the entire source-independent coarse family pairwise
disjoint. -/
theorem coarseRetainedAtom_pairwise
    {start n k : ℕ} {hk : k + 1 ≤ n} {profileDelta : ℝ}
    {x y : Point} {returnBoundary globalBoundary : Set Point}
    {globalStart : Point} :
    Pairwise fun left right :
        CoarseSplitCompletionCode start n k hk profileDelta x y
          returnBoundary globalBoundary globalStart ↦
      Disjoint (coarseRetainedAtom left) (coarseRetainedAtom right) := by
  intro left right hne
  rw [Set.disjoint_left]
  intro omega hleft hright
  have hl := left.2.recovered hleft
  have hr := right.2.recovered hright
  apply hne
  apply Subtype.ext
  exact hl.symm.trans hr

/-- The rooted refinement is still pairwise disjoint: its extra successful
source certificate is a proposition, so it cannot duplicate an underlying
coarse code. -/
theorem successfullyRooted_coarseRetainedAtom_pairwise
    {start n k : ℕ} {hk : k + 1 ≤ n} {profileDelta : ℝ}
    {x y : Point} {returnBoundary globalBoundary : Set Point}
    {globalStart : Point} :
    Pairwise fun left right :
        SuccessfullyRootedCoarseSplitCompletionCode start n k hk profileDelta
          x y returnBoundary globalBoundary globalStart ↦
      Disjoint (coarseRetainedAtom left.1) (coarseRetainedAtom right.1) := by
  intro left right hne
  apply coarseRetainedAtom_pairwise
  intro hval
  apply hne
  apply Subtype.ext
  exact hval

theorem coarseRetainedAtom_subset_stoppedSuccessfulPointEvent
    {start n k : ℕ} {hk : k + 1 ≤ n} {profileDelta : ℝ}
    {x y : Point} {returnBoundary globalBoundary : Set Point}
    {globalStart : Point}
    (code : CoarseSplitCompletionCode start n k hk profileDelta x y
      returnBoundary globalBoundary globalStart)
    (hsubset : coarseRetainedAtom code ⊆
      stoppedBufferedSuccessfulPointEvent start n
        (separationLevel n x y - 3) (separationLevel n x y + 1)
        profileDelta x) :
    coarseRetainedAtom code ⊆
      stoppedBufferedSuccessfulPointEvent start n
        (separationLevel n x y - 3) (separationLevel n x y + 1)
        profileDelta x :=
  hsubset

theorem iUnion_coarseRetainedAtom_subset_stoppedSuccessfulPointEvent
    {start n k : ℕ} {hk : k + 1 ≤ n} {profileDelta : ℝ}
    {x y : Point} {returnBoundary globalBoundary : Set Point}
    {globalStart : Point}
    (hsubset : ∀ code : CoarseSplitCompletionCode start n k hk profileDelta
      x y returnBoundary globalBoundary globalStart,
      coarseRetainedAtom code ⊆
        stoppedBufferedSuccessfulPointEvent start n
          (separationLevel n x y - 3) (separationLevel n x y + 1)
          profileDelta x) :
    (⋃ code : CoarseSplitCompletionCode start n k hk profileDelta x y
        returnBoundary globalBoundary globalStart,
      coarseRetainedAtom code) ⊆
      stoppedBufferedSuccessfulPointEvent start n
        (separationLevel n x y - 3) (separationLevel n x y + 1)
        profileDelta x := by
  intro omega homega
  obtain ⟨code, hcode⟩ := Set.mem_iUnion.mp homega
  exact hsubset code hcode

/-- At a genuinely separated scale the source certificate carried by every
coarse code recovers the original buffered left-event containment.  This is
kept as a theorem rather than a field so that the same code type remains
available at separation levels one and two. -/
theorem coarseRetainedAtom_subset_buffered_of_three
    {start n k : ℕ} {hk : k + 1 ≤ n} {profileDelta : ℝ}
    {x y : Point}
    (hn : 2 ≤ n) (hseparation : separationLevel n x y ≤ k)
    (hlevel : k ≤ n) (hthree : 3 ≤ separationLevel n x y)
    (code : SuccessfullyRootedCoarseSplitCompletionCode
      start n k hk profileDelta x y
      (profileInnerBoundary n k y)
      (discBoundary (0, 0) (outerScale n)) (0, 0)) :
    coarseRetainedAtom code.1 ⊆
      stoppedBufferedSuccessfulPointEvent start n
        (separationLevel n x y - 3) (separationLevel n x y + 1)
        profileDelta x := by
  obtain ⟨origin, hdata, hy, hexit, hx⟩ := code.2
  have hsource :=
    sourceCoarseSplitCompletionAtom_subset_stoppedSuccessfulPointEvent_of_separation_le
      hn hk hy hexit hseparation hlevel hthree hx
  unfold coarseRetainedAtom
  rw [coarseSplitCompletionAtomOfData_event_eq_of_data_eq hdata
    code.1.2.globalFirst
    (sourceCoarseSplitCompletionGlobalFirst
      (Nat.one_le_of_lt hn) hk hy hexit)]
  simpa only [sourceCoarseSplitCompletionAtom] using hsource

/-- Union form of `coarseRetainedAtom_subset_buffered_of_three`. -/
theorem iUnion_coarseRetainedAtom_subset_buffered_of_three
    {start n k : ℕ} {hk : k + 1 ≤ n} {profileDelta : ℝ}
    {x y : Point}
    (hn : 2 ≤ n) (hseparation : separationLevel n x y ≤ k)
    (hlevel : k ≤ n) (hthree : 3 ≤ separationLevel n x y) :
    (⋃ code : SuccessfullyRootedCoarseSplitCompletionCode
        start n k hk profileDelta x y
        (profileInnerBoundary n k y)
        (discBoundary (0, 0) (outerScale n)) (0, 0),
      coarseRetainedAtom code.1) ⊆
      stoppedBufferedSuccessfulPointEvent start n
        (separationLevel n x y - 3) (separationLevel n x y + 1)
        profileDelta x := by
  intro omega homega
  obtain ⟨code, hcode⟩ := Set.mem_iUnion.mp homega
  exact coarseRetainedAtom_subset_buffered_of_three
    hn hseparation hlevel hthree code hcode

/-- The actual stopped source supplies a valid coarse code. -/
def sourceCoarseSplitCompletionWitness
    {start n k : ℕ} {profileDelta : ℝ} {x y : Point} {source : StepPath}
    (hn : 2 ≤ n) (hk : k + 1 ≤ n)
    (hy : y ∈ candidateBox n)
    (hexit : IsOuterExitTime (trajectory (shiftSteps start source)) n
      (stoppedOuterExitHorizon start n source))
    (hsourceX : source ∈ stoppedSuccessfulPointEvent
      start n profileDelta x) :
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

/-- A valid source witness at any retained split no shallower than geometric
separation. -/
def sourceCoarseSplitCompletionWitness_of_separation_le
    {start n k : ℕ} {profileDelta : ℝ} {x y : Point} {source : StepPath}
    (hn : 2 ≤ n) (hk : k + 1 ≤ n)
    (hy : y ∈ candidateBox n)
    (hexit : IsOuterExitTime (trajectory (shiftSteps start source)) n
      (stoppedOuterExitHorizon start n source))
    (hsourceX : source ∈ stoppedSuccessfulPointEvent
      start n profileDelta x) :
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

/-- The valid coarse code canonically indexed by one stopped source. -/
def sourceCoarseSplitCompletionCode
    {start n k : ℕ} {profileDelta : ℝ} {x y : Point} {source : StepPath}
    (hn : 2 ≤ n) (hk : k + 1 ≤ n)
    (hy : y ∈ candidateBox n)
    (hexit : IsOuterExitTime (trajectory (shiftSteps start source)) n
      (stoppedOuterExitHorizon start n source))
    (hsourceX : source ∈ stoppedSuccessfulPointEvent
      start n profileDelta x) :
    CoarseSplitCompletionCode start n k hk profileDelta x y
      (profileInnerBoundary n k y)
      (discBoundary (0, 0) (outerScale n)) (0, 0) :=
  ⟨sourceCoarseSplitCompletionData start n k hk x y source,
    sourceCoarseSplitCompletionWitness hn hk hy hexit hsourceX⟩

/-- The valid coarse code indexed by a source at a deeper retained split. -/
def sourceCoarseSplitCompletionCode_of_separation_le
    {start n k : ℕ} {profileDelta : ℝ} {x y : Point} {source : StepPath}
    (hn : 2 ≤ n) (hk : k + 1 ≤ n)
    (hy : y ∈ candidateBox n)
    (hexit : IsOuterExitTime (trajectory (shiftSteps start source)) n
      (stoppedOuterExitHorizon start n source))
    (hsourceX : source ∈ stoppedSuccessfulPointEvent
      start n profileDelta x) :
    CoarseSplitCompletionCode start n k hk profileDelta x y
      (profileInnerBoundary n k y)
      (discBoundary (0, 0) (outerScale n)) (0, 0) :=
  ⟨sourceCoarseSplitCompletionData start n k hk x y source,
    sourceCoarseSplitCompletionWitness_of_separation_le
      hn hk hy hexit hsourceX⟩

/-- The canonical coarse code with its genuine successful left source
retained as a separate certificate. -/
def sourceSuccessfullyRootedCoarseSplitCompletionCode_of_separation_le
    {start n k : ℕ} {profileDelta : ℝ} {x y : Point}
    {source : StepPath}
    (hn : 2 ≤ n) (hk : k + 1 ≤ n)
    (hy : y ∈ candidateBox n)
    (hexit : IsOuterExitTime (trajectory (shiftSteps start source)) n
      (stoppedOuterExitHorizon start n source))
    (hsourceX : source ∈ stoppedSuccessfulPointEvent
      start n profileDelta x) :
    SuccessfullyRootedCoarseSplitCompletionCode
      start n k hk profileDelta x y
      (profileInnerBoundary n k y)
      (discBoundary (0, 0) (outerScale n)) (0, 0) :=
  ⟨sourceCoarseSplitCompletionCode_of_separation_le
      hn hk hy hexit hsourceX,
    ⟨source, rfl, hy, hexit, hsourceX⟩⟩

/-- Every stopped successful pair is covered by its valid coarse retained
atom.  This is the source coverage needed before the deeper `y` refinement. -/
theorem stoppedSuccessfulPairEvent_subset_iUnion_coarseRetainedAtom
    {start n k : ℕ} {profileDelta : ℝ} {x y : Point}
    (hn : 2 ≤ n) (hk : k + 1 ≤ n)
    (hseparation : k = separationLevel n x y) (hlevel : k ≤ n) :
    stoppedSuccessfulPairEvent start n profileDelta x y ⊆
      ⋃ code : SuccessfullyRootedCoarseSplitCompletionCode
          start n k hk profileDelta x y
          (profileInnerBoundary n k y)
          (discBoundary (0, 0) (outerScale n)) (0, 0),
        coarseRetainedAtom code.1 := by
  rintro source ⟨hsourceX, hsourceY⟩
  obtain ⟨horizon, hexit, hsuccessfulY⟩ := hsourceY
  have hhorizon : stoppedOuterExitHorizon start n source = horizon :=
    stoppedOuterExitHorizon_eq_of_isOuterExitTime hexit
  have hexitStopped : IsOuterExitTime
      (trajectory (shiftSteps start source)) n
      (stoppedOuterExitHorizon start n source) := by
    simpa only [Proposition13Measurability.shiftedWalk, hhorizon] using hexit
  let base := sourceCoarseSplitCompletionCode hn hk hsuccessfulY.1
    hexitStopped hsourceX
  let code : SuccessfullyRootedCoarseSplitCompletionCode
      start n k hk profileDelta x y
      (profileInnerBoundary n k y)
      (discBoundary (0, 0) (outerScale n)) (0, 0) :=
    ⟨base, ⟨source, rfl, hsuccessfulY.1, hexitStopped, hsourceX⟩⟩
  apply Set.mem_iUnion.mpr
  refine ⟨code, ?_⟩
  unfold coarseRetainedAtom code base sourceCoarseSplitCompletionCode
  simpa only [sourceCoarseSplitCompletionAtom] using
    (source_mem_coarseSplitCompletionAtomAt
      (x := x) (y := y) (Nat.one_le_of_lt hn) hk
        hsuccessfulY.1 hexitStopped)

/-- Source coverage at a retained split at or beyond geometric separation. -/
theorem stoppedSuccessfulPairEvent_subset_iUnion_coarseRetainedAtom_of_separation_le
    {start n k : ℕ} {profileDelta : ℝ} {x y : Point}
    (hn : 2 ≤ n) (hk : k + 1 ≤ n)
    (hseparation : separationLevel n x y ≤ k) (hlevel : k ≤ n) :
    stoppedSuccessfulPairEvent start n profileDelta x y ⊆
      ⋃ code : SuccessfullyRootedCoarseSplitCompletionCode
          start n k hk profileDelta x y
          (profileInnerBoundary n k y)
          (discBoundary (0, 0) (outerScale n)) (0, 0),
        coarseRetainedAtom code.1 := by
  rintro source ⟨hsourceX, hsourceY⟩
  obtain ⟨horizon, hexit, hsuccessfulY⟩ := hsourceY
  have hhorizon : stoppedOuterExitHorizon start n source = horizon :=
    stoppedOuterExitHorizon_eq_of_isOuterExitTime hexit
  have hexitStopped : IsOuterExitTime
      (trajectory (shiftSteps start source)) n
      (stoppedOuterExitHorizon start n source) := by
    simpa only [Proposition13Measurability.shiftedWalk, hhorizon] using hexit
  let code := sourceSuccessfullyRootedCoarseSplitCompletionCode_of_separation_le
    hn hk hsuccessfulY.1 hexitStopped hsourceX
  apply Set.mem_iUnion.mpr
  refine ⟨code, ?_⟩
  unfold coarseRetainedAtom code
    sourceSuccessfullyRootedCoarseSplitCompletionCode_of_separation_le
    sourceCoarseSplitCompletionCode_of_separation_le
  simpa only [sourceCoarseSplitCompletionAtom] using
    (source_mem_coarseSplitCompletionAtomAt
      (x := x) (y := y) (Nat.one_le_of_lt hn) hk
        hsuccessfulY.1 hexitStopped)

end

end Erdos1165.AsymmetricCoarseCompletionCode
