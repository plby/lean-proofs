/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/
import ErdosProblems.Erdos1165.AnnularErasedParentSpineProfileRow
import ErdosProblems.Erdos1165.AnnularDecoratedProfileCode
import ErdosProblems.Erdos1165.AnnularBoundaryExcursionKernel
import ErdosProblems.Erdos1165.AsymmetricSplitLevelSplice
import ErdosProblems.Erdos1165.TerminalRetainedPieceOffsets

/-!
# Literal retained spine extracted from one profile gap

The existing return extractor gives every deleted inner-to-middle child
word.  This file supplies the complementary half: the successive
middle-to-inner pieces and the final escape are canonical first-hit words
for the union of the next inner boundary and the parent outer boundary.
-/

open Set

namespace Erdos1165.AnnularExtractedProfileSpineCode

open AnnularDecoratedProfileCode AnnularErasedParentSpineProfileRow
open AnnularErasedParentSpineRowPartition
open AlternatingConcatPrefixFree
open AnnularBoundaryExcursionKernel
open AnnularOffspringRenewal
open AnnularOffspringKernelRadial AnnularOffspringScan AnnularProfileClocks
open AsymmetricSplitLevelSplice MarkedBridgeFactorization
open TerminalBoundaryScan TerminalClockSplice TerminalExcursionPathwise
open TerminalSequentialVisitLaw TerminalSpliceProfileGeometry ThickPoint
open TerminalSkeletonWords
open TerminalRetainedHitSplice TerminalRetainedPieceOffsets

noncomputable section

attribute [local instance] Classical.propDecidable

private theorem excursionStart_zero_eq_zero_of_mem
    (s : WalkPath) (middle inner : Set Point)
    [DecidablePred (· ∈ middle)] [DecidablePred (· ∈ inner)]
    (horizon : ℕ) (hzero : s 0 ∈ middle) :
    excursionStart s middle inner horizon 0 = 0 := by
  unfold excursionStart
  simp only [Function.iterate_zero_apply]
  let times := hitTimesThrough s middle 0 horizon
  have hmem : 0 ∈ times := by
    simp only [times, hitTimesThrough, Finset.mem_filter, Finset.mem_Icc]
    exact ⟨⟨Nat.zero_le _, Nat.zero_le _⟩, hzero⟩
  have hnonempty : times.Nonempty := ⟨0, hmem⟩
  rw [firstHitThrough, dif_pos hnonempty]
  exact Nat.eq_zero_of_le_zero (Finset.min'_le _ _ hmem)

/-- Every return following a completed child reaches the parent middle
boundary before the first parent outer exit. -/
theorem profileReturnExit_complete
    {n k q : ℕ} {center : Point}
    (hn : 2 ≤ n) (hk0 : 0 < k) (hk : k + 1 ≤ n)
    (u : ProfileCycleMiddlePoint n k center)
    (w : ProfileCycleOuterPoint n k center)
    (parent : BoundaryExcursionExitWordCode
      (profileOuterBoundary n k center)
      (profileInnerBoundary n k center)
      (profileInnerBoundary n (k + 1) center) u.1 q w.1) :
    ∀ j : Fin q,
      excursionStart
        (PlanarPotential.trajectoryFrom u.1 (extendStoppedWord parent.1))
        (profileInnerBoundary n k center)
        (profileInnerBoundary n (k + 1) center)
        parent.1.1 (j + 1) ≤ parent.1.1 := by
  apply returnExitTime_le_of_boundaryExcursionExitAtom
    parent.2.1 parent.2.2.1
  intro z hz
  have hkpred : k - 1 + 1 = k := Nat.sub_add_cancel hk0
  exact FirstHitSeparates.discBoundaries hz
    (scaleRadius_antitone_of_le (by omega : k ≤ k + 1) hk)
    (by
      simpa only [hkpred] using
        (scaleRadius_succ_add_one_le (n := n) (k := k - 1)
          (by omega : 1 ≤ n) (by omega : (k - 1) + 1 ≤ n)))

/-- Every successive parent middle clock, including the final escape clock,
is reached by the parent horizon. -/
theorem profileExcursionStart_le
    {n k q : ℕ} {center : Point}
    (hn : 2 ≤ n) (hk0 : 0 < k) (hk : k + 1 ≤ n)
    (u : ProfileCycleMiddlePoint n k center)
    (w : ProfileCycleOuterPoint n k center)
    (parent : BoundaryExcursionExitWordCode
      (profileOuterBoundary n k center)
      (profileInnerBoundary n k center)
      (profileInnerBoundary n (k + 1) center) u.1 q w.1) :
    ∀ j : Fin (q + 1),
      excursionStart
        (PlanarPotential.trajectoryFrom u.1 (extendStoppedWord parent.1))
        (profileInnerBoundary n k center)
        (profileInnerBoundary n (k + 1) center)
        parent.1.1 j ≤ parent.1.1 := by
  intro j
  refine Fin.cases ?_ (fun i ↦ ?_) j
  · have hzero : PlanarPotential.trajectoryFrom u.1
        (extendStoppedWord parent.1) 0 ∈ profileInnerBoundary n k center := by
      simpa only [PlanarPotential.trajectoryFrom_zero, profileInnerBoundary]
        using (RealDiscFinite.mem_discBoundaryFinset.mp u.2)
    have hclock := excursionStart_zero_eq_zero_of_mem
      (PlanarPotential.trajectoryFrom u.1 (extendStoppedWord parent.1))
      (profileInnerBoundary n k center)
      (profileInnerBoundary n (k + 1) center)
      parent.1.1 hzero
    change excursionStart
      (PlanarPotential.trajectoryFrom u.1 (extendStoppedWord parent.1))
      (profileInnerBoundary n k center)
      (profileInnerBoundary n (k + 1) center) parent.1.1 0 ≤ parent.1.1
    rw [hclock]
    exact Nat.zero_le _
  · exact profileReturnExit_complete hn hk0 hk u w parent i

/-- The `j`-th child entrance is reached before the parent horizon. -/
theorem profileExcursionFinish_le
    {n k q : ℕ} {center : Point}
    (u : ProfileCycleMiddlePoint n k center)
    (w : ProfileCycleOuterPoint n k center)
    (parent : BoundaryExcursionExitWordCode
      (profileOuterBoundary n k center)
      (profileInnerBoundary n k center)
      (profileInnerBoundary n (k + 1) center) u.1 q w.1)
    (j : Fin q) :
    excursionFinish
        (PlanarPotential.trajectoryFrom u.1 (extendStoppedWord parent.1))
        (profileInnerBoundary n k center)
        (profileInnerBoundary n (k + 1) center)
        parent.1.1 j ≤ parent.1.1 := by
  have hcount : completedExcursionCount
      (PlanarPotential.trajectoryFrom u.1 (extendStoppedWord parent.1))
      (profileInnerBoundary n k center)
      (profileInnerBoundary n (k + 1) center) parent.1.1 = q := by
    simpa only [boundaryExcursionCount] using parent.2.2.1
  have hqle : q ≤ parent.1.1 + 1 := by
    calc
      q = completedExcursionCount
          (PlanarPotential.trajectoryFrom u.1 (extendStoppedWord parent.1))
          (profileInnerBoundary n k center)
          (profileInnerBoundary n (k + 1) center) parent.1.1 := hcount.symm
      _ ≤ parent.1.1 + 1 := completedExcursionCount_le _ _ _ _
  apply (excursionFinish_le_horizon_iff_lt_completedExcursionCount
    _ _ _ _ (by omega)).2
  rw [hcount]
  exact j.isLt

theorem extractedProfileMiddlePoint_mem
    {n k q : ℕ} {center : Point}
    (hn : 2 ≤ n) (hk0 : 0 < k) (hk : k + 1 ≤ n)
    (u : ProfileCycleMiddlePoint n k center)
    (w : ProfileCycleOuterPoint n k center)
    (parent : BoundaryExcursionExitWordCode
      (profileOuterBoundary n k center)
      (profileInnerBoundary n k center)
      (profileInnerBoundary n (k + 1) center) u.1 q w.1)
    (j : Fin (q + 1)) :
    PlanarPotential.trajectoryFrom u.1 (extendStoppedWord parent.1)
      (excursionStart
        (PlanarPotential.trajectoryFrom u.1 (extendStoppedWord parent.1))
        (profileInnerBoundary n k center)
        (profileInnerBoundary n (k + 1) center) parent.1.1 j) ∈
      RealDiscFinite.discBoundaryFinset center (scaleRadius n k) := by
  apply RealDiscFinite.mem_discBoundaryFinset.mpr
  simpa only [profileInnerBoundary] using (show
    PlanarPotential.trajectoryFrom u.1 (extendStoppedWord parent.1)
      (excursionStart
        (PlanarPotential.trajectoryFrom u.1 (extendStoppedWord parent.1))
        (profileInnerBoundary n k center)
        (profileInnerBoundary n (k + 1) center) parent.1.1 j) ∈
      profileInnerBoundary n k center from by
    unfold excursionStart
    exact firstHitThrough_mem_set_of_le _ _ _ _
      (profileExcursionStart_le hn hk0 hk u w parent j))

theorem extractedProfileInnerPoint_mem
    {n k q : ℕ} {center : Point}
    (u : ProfileCycleMiddlePoint n k center)
    (w : ProfileCycleOuterPoint n k center)
    (parent : BoundaryExcursionExitWordCode
      (profileOuterBoundary n k center)
      (profileInnerBoundary n k center)
      (profileInnerBoundary n (k + 1) center) u.1 q w.1)
    (j : Fin q) :
    PlanarPotential.trajectoryFrom u.1 (extendStoppedWord parent.1)
      (excursionFinish
        (PlanarPotential.trajectoryFrom u.1 (extendStoppedWord parent.1))
        (profileInnerBoundary n k center)
        (profileInnerBoundary n (k + 1) center) parent.1.1 j) ∈
      RealDiscFinite.discBoundaryFinset center (scaleRadius n (k + 1)) := by
  apply RealDiscFinite.mem_discBoundaryFinset.mpr
  simpa only [profileInnerBoundary] using
    (excursionFinish_mem_inner_of_le
      (PlanarPotential.trajectoryFrom u.1 (extendStoppedWord parent.1))
      (profileInnerBoundary n k center)
      (profileInnerBoundary n (k + 1) center) parent.1.1 j
      (profileExcursionFinish_le u w parent j))

/-- Supported middle endpoints of the retained spine. -/
def extractedProfileMiddlePoint
    {n k q : ℕ} {center : Point}
    (hn : 2 ≤ n) (hk0 : 0 < k) (hk : k + 1 ≤ n)
    (u : ProfileCycleMiddlePoint n k center)
    (w : ProfileCycleOuterPoint n k center)
    (parent : BoundaryExcursionExitWordCode
      (profileOuterBoundary n k center)
      (profileInnerBoundary n k center)
      (profileInnerBoundary n (k + 1) center) u.1 q w.1)
    (j : Fin (q + 1)) : ProfileCycleMiddlePoint n k center :=
  ⟨PlanarPotential.trajectoryFrom u.1 (extendStoppedWord parent.1)
      (excursionStart
        (PlanarPotential.trajectoryFrom u.1 (extendStoppedWord parent.1))
        (profileInnerBoundary n k center)
        (profileInnerBoundary n (k + 1) center) parent.1.1 j),
    extractedProfileMiddlePoint_mem hn hk0 hk u w parent j⟩

/-- Supported inner endpoints of the retained inward pieces. -/
def extractedProfileInnerPoint
    {n k q : ℕ} {center : Point}
    (u : ProfileCycleMiddlePoint n k center)
    (w : ProfileCycleOuterPoint n k center)
    (parent : BoundaryExcursionExitWordCode
      (profileOuterBoundary n k center)
      (profileInnerBoundary n k center)
      (profileInnerBoundary n (k + 1) center) u.1 q w.1)
    (j : Fin q) : ProfileCycleInnerPoint n k center :=
  ⟨PlanarPotential.trajectoryFrom u.1 (extendStoppedWord parent.1)
      (excursionFinish
        (PlanarPotential.trajectoryFrom u.1 (extendStoppedWord parent.1))
        (profileInnerBoundary n k center)
        (profileInnerBoundary n (k + 1) center) parent.1.1 j),
    extractedProfileInnerPoint_mem u w parent j⟩

@[simp] theorem extractedProfileMiddlePoint_zero
    {n k q : ℕ} {center : Point}
    (hn : 2 ≤ n) (hk0 : 0 < k) (hk : k + 1 ≤ n)
    (u : ProfileCycleMiddlePoint n k center)
    (w : ProfileCycleOuterPoint n k center)
    (parent : BoundaryExcursionExitWordCode
      (profileOuterBoundary n k center)
      (profileInnerBoundary n k center)
      (profileInnerBoundary n (k + 1) center) u.1 q w.1) :
    extractedProfileMiddlePoint hn hk0 hk u w parent (0 : Fin (q + 1)) = u := by
  apply Subtype.ext
  change PlanarPotential.trajectoryFrom u.1 (extendStoppedWord parent.1)
    (excursionStart
      (PlanarPotential.trajectoryFrom u.1 (extendStoppedWord parent.1))
      (profileInnerBoundary n k center)
      (profileInnerBoundary n (k + 1) center) parent.1.1 0) = u.1
  rw [excursionStart_zero_eq_zero_of_mem]
  · exact PlanarPotential.trajectoryFrom_zero _ _
  · simpa only [PlanarPotential.trajectoryFrom_zero, profileInnerBoundary] using
      (RealDiscFinite.mem_discBoundaryFinset.mp u.2)

/-- One actual retained middle-to-inner piece as a canonical union-boundary
first-hit word. -/
def extractedProfileInwardWordCode
    {n k q : ℕ} {center : Point}
    (hn : 2 ≤ n) (hk0 : 0 < k) (hk : k + 1 ≤ n)
    (u : ProfileCycleMiddlePoint n k center)
    (w : ProfileCycleOuterPoint n k center)
    (parent : BoundaryExcursionExitWordCode
      (profileOuterBoundary n k center)
      (profileInnerBoundary n k center)
      (profileInnerBoundary n (k + 1) center) u.1 q w.1)
    (j : Fin q) :
    ProfileInwardWordCode n k center
      (extractedProfileMiddlePoint hn hk0 hk u w parent j.castSucc)
      (extractedProfileInnerPoint u w parent j) := by
  let s := PlanarPotential.trajectoryFrom u.1 (extendStoppedWord parent.1)
  let begin := excursionStart s (profileInnerBoundary n k center)
    (profileInnerBoundary n (k + 1) center) parent.1.1 j
  let finish := excursionFinish s (profileInnerBoundary n k center)
    (profileInnerBoundary n (k + 1) center) parent.1.1 j
  have hbegin : begin ≤ finish := excursionStart_le_finish _ _ _ _ _
  have hfinish : finish ≤ parent.1.1 := profileExcursionFinish_le u w parent j
  have hspec := firstHitThrough_spec_of_le s
    (profileInnerBoundary n (k + 1) center) begin parent.1.1
    (by simpa only [finish, excursionFinish] using hfinish)
  apply incrementSliceBoundaryExitWordCode u.1 (extendStoppedWord parent.1)
    (profileInnerBoundary n (k + 1) center ∪
      profileOuterBoundary n k center) hbegin
  · exact Or.inl (by
      simpa only [s, finish, excursionFinish, begin] using hspec.2.1)
  · intro r hbr hrf
    rw [Set.mem_union]
    push Not
    constructor
    · exact hspec.2.2 r (by simpa only [finish, excursionFinish] using hrf) hbr
    · exact parent.2.1.2 r (hrf.trans_le hfinish)

/-- The actual retained final middle-to-outer piece.  The first unfinished
child clock is sentinel-valued, hence this word avoids the next inner
boundary until the parent exits. -/
def extractedProfileEscapeWordCode
    {n k q : ℕ} {center : Point}
    (hn : 2 ≤ n) (hk0 : 0 < k) (hk : k + 1 ≤ n)
    (u : ProfileCycleMiddlePoint n k center)
    (w : ProfileCycleOuterPoint n k center)
    (parent : BoundaryExcursionExitWordCode
      (profileOuterBoundary n k center)
      (profileInnerBoundary n k center)
      (profileInnerBoundary n (k + 1) center) u.1 q w.1) :
    ProfileEscapeWordCode n k center
      (extractedProfileMiddlePoint hn hk0 hk u w parent (Fin.last q)) w := by
  let s := PlanarPotential.trajectoryFrom u.1 (extendStoppedWord parent.1)
  let begin := excursionStart s (profileInnerBoundary n k center)
    (profileInnerBoundary n (k + 1) center) parent.1.1 q
  have hbegin : begin ≤ parent.1.1 := by
    simpa only [begin, s, Fin.val_last] using
      (profileExcursionStart_le hn hk0 hk u w parent (Fin.last q))
  have hcount : completedExcursionCount s
      (profileInnerBoundary n k center)
      (profileInnerBoundary n (k + 1) center) parent.1.1 = q := by
    simpa only [s, boundaryExcursionCount] using parent.2.2.1
  have hdisjoint : Disjoint (profileInnerBoundary n k center)
      (profileInnerBoundary n (k + 1) center) :=
    adjacent_profileInnerBoundaries_disjoint (by omega : 1 ≤ n) hk center
  have hsentinel : excursionFinish s (profileInnerBoundary n k center)
      (profileInnerBoundary n (k + 1) center) parent.1.1 q =
        parent.1.1 + 1 := by
    simpa only [hcount] using
      (excursionFinish_completedExcursionCount_eq_sentinel s
        (profileInnerBoundary n k center)
        (profileInnerBoundary n (k + 1) center) hdisjoint parent.1.1)
  have hinnerAvoid : AvoidsThrough s (profileInnerBoundary n (k + 1) center)
      begin parent.1.1 := by
    apply avoidsThrough_of_firstHitThrough_eq_sentinel
    simpa only [excursionFinish, begin] using hsentinel
  have code := incrementSliceBoundaryExitWordCode u.1
    (extendStoppedWord parent.1)
    (profileInnerBoundary n (k + 1) center ∪
      profileOuterBoundary n k center) hbegin
    (Or.inr parent.2.1.1) (by
      intro r hbr hrh
      rw [Set.mem_union]
      push Not
      exact ⟨hinnerAvoid r hbr hrh.le,
        parent.2.1.2 r hrh⟩)
  refine ⟨code.1, ?_, ?_⟩
  · simpa only [extractedProfileMiddlePoint, s, begin, Fin.val_last] using
      code.2.1
  · simpa only [extractedProfileMiddlePoint, s, begin, Fin.val_last] using
      code.2.2.trans parent.2.2.2

/-- The actual deleted inner-to-middle return, with its profile endpoint
subtypes made explicit. -/
def extractedProfileReturnWordCode
    {n k q : ℕ} {center : Point}
    (hn : 2 ≤ n) (hk0 : 0 < k) (hk : k + 1 ≤ n)
    (u : ProfileCycleMiddlePoint n k center)
    (w : ProfileCycleOuterPoint n k center)
    (parent : BoundaryExcursionExitWordCode
      (profileOuterBoundary n k center)
      (profileInnerBoundary n k center)
      (profileInnerBoundary n (k + 1) center) u.1 q w.1)
    (j : Fin q) : BoundaryExitWordCode (profileInnerBoundary n k center)
      (extractedProfileInnerPoint u w parent j).1
      (extractedProfileMiddlePoint hn hk0 hk u w parent j.succ).1 := by
  let code := extractedReturnCodes
    (profileReturnExit_complete hn hk0 hk u w parent) j
  refine ⟨code.1, ?_, ?_⟩
  · simpa only [code, extractedProfileInnerPoint, extractedProfileMiddlePoint,
      returnEntrancePoint, returnEntranceTime, returnExitPoint, returnExitTime,
      Fin.val_succ] using code.2.1
  · simpa only [code, extractedProfileInnerPoint, extractedProfileMiddlePoint,
      returnEntrancePoint, returnEntranceTime, returnExitPoint, returnExitTime,
      Fin.val_succ] using code.2.2

@[simp] theorem extractedProfileInwardWordCode_toList
    {n k q : ℕ} {center : Point}
    (hn : 2 ≤ n) (hk0 : 0 < k) (hk : k + 1 ≤ n)
    (u : ProfileCycleMiddlePoint n k center)
    (w : ProfileCycleOuterPoint n k center)
    (parent : BoundaryExcursionExitWordCode
      (profileOuterBoundary n k center)
      (profileInnerBoundary n k center)
      (profileInnerBoundary n (k + 1) center) u.1 q w.1)
    (j : Fin q) :
    List.ofFn
        (extractedProfileInwardWordCode hn hk0 hk u w parent j).1.2 =
      incrementSlice (extendStoppedWord parent.1)
        (excursionStart
          (PlanarPotential.trajectoryFrom u.1 (extendStoppedWord parent.1))
          (profileInnerBoundary n k center)
          (profileInnerBoundary n (k + 1) center) parent.1.1 j)
        (excursionFinish
          (PlanarPotential.trajectoryFrom u.1 (extendStoppedWord parent.1))
          (profileInnerBoundary n k center)
          (profileInnerBoundary n (k + 1) center) parent.1.1 j) := by
  simp only [extractedProfileInwardWordCode,
    incrementSliceBoundaryExitWordCode,
    TerminalVisitSpliceInvariance.stoppedWordOfList]
  exact List.ofFn_get _

@[simp] theorem extractedProfileEscapeWordCode_toList
    {n k q : ℕ} {center : Point}
    (hn : 2 ≤ n) (hk0 : 0 < k) (hk : k + 1 ≤ n)
    (u : ProfileCycleMiddlePoint n k center)
    (w : ProfileCycleOuterPoint n k center)
    (parent : BoundaryExcursionExitWordCode
      (profileOuterBoundary n k center)
      (profileInnerBoundary n k center)
      (profileInnerBoundary n (k + 1) center) u.1 q w.1) :
    List.ofFn
        (extractedProfileEscapeWordCode hn hk0 hk u w parent).1.2 =
      incrementSlice (extendStoppedWord parent.1)
        (excursionStart
          (PlanarPotential.trajectoryFrom u.1 (extendStoppedWord parent.1))
          (profileInnerBoundary n k center)
          (profileInnerBoundary n (k + 1) center) parent.1.1 q)
        parent.1.1 := by
  simp only [extractedProfileEscapeWordCode,
    incrementSliceBoundaryExitWordCode,
    TerminalVisitSpliceInvariance.stoppedWordOfList]
  exact List.ofFn_get _

@[simp] theorem extractedProfileReturnWordCode_toList
    {n k q : ℕ} {center : Point}
    (hn : 2 ≤ n) (hk0 : 0 < k) (hk : k + 1 ≤ n)
    (u : ProfileCycleMiddlePoint n k center)
    (w : ProfileCycleOuterPoint n k center)
    (parent : BoundaryExcursionExitWordCode
      (profileOuterBoundary n k center)
      (profileInnerBoundary n k center)
      (profileInnerBoundary n (k + 1) center) u.1 q w.1)
    (j : Fin q) :
    List.ofFn
        (extractedProfileReturnWordCode hn hk0 hk u w parent j).1.2 =
      intervalWords (extendStoppedWord parent.1)
        (extractTimedReturnSkeleton (extendStoppedWord parent.1) u.1
          (profileInnerBoundary n k center)
          (profileInnerBoundary n (k + 1) center) parent.1.1 q).entrance
        (extractTimedReturnSkeleton (extendStoppedWord parent.1) u.1
          (profileInnerBoundary n k center)
          (profileInnerBoundary n (k + 1) center) parent.1.1 q).exit j := by
  change extractedReturnWords
    (profileReturnExit_complete hn hk0 hk u w parent) j = _
  exact
    (extractedReturnCodes_toList
      (profileReturnExit_complete hn hk0 hk u w parent) j)

/-- The chronological middle endpoints extracted from the source are exactly
the `Fin.cons` middle-stage array determined by the parent entrance and the
deleted return endpoints. -/
theorem extractedProfileMiddlePoint_eq_profileMiddleStage
    {n k q : ℕ} {center : Point}
    (hn : 2 ≤ n) (hk0 : 0 < k) (hk : k + 1 ≤ n)
    (u : ProfileCycleMiddlePoint n k center)
    (w : ProfileCycleOuterPoint n k center)
    (parent : BoundaryExcursionExitWordCode
      (profileOuterBoundary n k center)
      (profileInnerBoundary n k center)
      (profileInnerBoundary n (k + 1) center) u.1 q w.1) :
    ∀ i : Fin (q + 1),
      extractedProfileMiddlePoint hn hk0 hk u w parent i =
        profileMiddleStage u
          (fun j ↦ extractedProfileMiddlePoint hn hk0 hk u w parent j.succ) i := by
  intro i
  refine Fin.cases ?_ (fun j ↦ ?_) i
  · exact extractedProfileMiddlePoint_zero hn hk0 hk u w parent
  · rfl

/-- The retained word lists extracted above are literally the complementary
pieces of the timed deletion skeleton. -/
theorem extractedProfileRetainedPieces_eq
    {n k q : ℕ} {center : Point}
    (hn : 2 ≤ n) (hk0 : 0 < k) (hk : k + 1 ≤ n)
    (u : ProfileCycleMiddlePoint n k center)
    (w : ProfileCycleOuterPoint n k center)
    (parent : BoundaryExcursionExitWordCode
      (profileOuterBoundary n k center)
      (profileInnerBoundary n k center)
      (profileInnerBoundary n (k + 1) center) u.1 q w.1) :
    Fin.lastCases
        (List.ofFn
          (extractedProfileEscapeWordCode hn hk0 hk u w parent).1.2)
        (fun j ↦ List.ofFn
          (extractedProfileInwardWordCode hn hk0 hk u w parent j).1.2) =
      complementaryPieces q (extendStoppedWord parent.1) 0 parent.1.1
        (extractTimedReturnSkeleton (extendStoppedWord parent.1) u.1
          (profileInnerBoundary n k center)
          (profileInnerBoundary n (k + 1) center) parent.1.1 q).entrance
        (extractTimedReturnSkeleton (extendStoppedWord parent.1) u.1
          (profileInnerBoundary n k center)
          (profileInnerBoundary n (k + 1) center) parent.1.1 q).exit := by
  funext i
  refine Fin.lastCases ?_ (fun j ↦ ?_) i
  · simp only [Fin.lastCases_last, extractedProfileEscapeWordCode_toList]
    cases q with
    | zero =>
        change incrementSlice (extendStoppedWord parent.1)
            (excursionStart
              (PlanarPotential.trajectoryFrom u.1 (extendStoppedWord parent.1))
              (profileInnerBoundary n k center)
              (profileInnerBoundary n (k + 1) center) parent.1.1 0)
              parent.1.1 = incrementSlice (extendStoppedWord parent.1) 0 parent.1.1
        rw [excursionStart_zero_eq_zero_of_mem]
        simpa only [PlanarPotential.trajectoryFrom_zero, profileInnerBoundary]
          using (RealDiscFinite.mem_discBoundaryFinset.mp u.2)
    | succ r =>
        rw [complementaryPieces_last r]
        rfl
  · simp only [Fin.lastCases_castSucc,
      extractedProfileInwardWordCode_toList]
    cases q with
    | zero => exact Fin.elim0 j
    | succ r =>
        refine Fin.cases ?_ (fun p ↦ ?_) j
        · rw [show (0 : Fin (r + 1)).castSucc =
              (0 : Fin (r + 1 + 1)) by ext; rfl,
            complementaryPieces_zero]
          change incrementSlice (extendStoppedWord parent.1)
              (excursionStart
                (PlanarPotential.trajectoryFrom u.1 (extendStoppedWord parent.1))
                (profileInnerBoundary n k center)
                (profileInnerBoundary n (k + 1) center) parent.1.1 0)
                (excursionFinish
                  (PlanarPotential.trajectoryFrom u.1 (extendStoppedWord parent.1))
                  (profileInnerBoundary n k center)
                  (profileInnerBoundary n (k + 1) center) parent.1.1 0) =
                incrementSlice (extendStoppedWord parent.1) 0
                  (excursionFinish
                    (PlanarPotential.trajectoryFrom u.1 (extendStoppedWord parent.1))
                    (profileInnerBoundary n k center)
                    (profileInnerBoundary n (k + 1) center) parent.1.1 0)
          rw [excursionStart_zero_eq_zero_of_mem]
          simpa only [PlanarPotential.trajectoryFrom_zero,
            profileInnerBoundary] using
              (RealDiscFinite.mem_discBoundaryFinset.mp u.2)
        · rw [show p.succ.castSucc = p.castSucc.succ by ext; rfl,
            complementaryPieces_succ (extendStoppedWord parent.1) 0
              parent.1.1 _ _ p.castSucc (Nat.succ_lt_succ p.isLt)]
          rfl

/-- The complete literal one-parent assembly extracted from a genuine
boundary-excursion word.  Its retained coordinates are the inward spine and
final escape; its child coordinates are exactly the deleted return words. -/
def extractedProfileAssemblyCode
    {n k q : ℕ} {center : Point}
    (hn : 2 ≤ n) (hk0 : 0 < k) (hk : k + 1 ≤ n)
    (u : ProfileCycleMiddlePoint n k center)
    (w : ProfileCycleOuterPoint n k center)
    (parent : BoundaryExcursionExitWordCode
      (profileOuterBoundary n k center)
      (profileInnerBoundary n k center)
      (profileInnerBoundary n (k + 1) center) u.1 q w.1) :
    ErasedParentAssemblyCode q
      (profileInnerBoundary n (k + 1) center ∪
        profileOuterBoundary n k center)
      (profileInnerBoundary n k center) u.1
      (fun j ↦ (extractedProfileInnerPoint u w parent j).1)
      (fun j ↦
        (extractedProfileMiddlePoint hn hk0 hk u w parent j.succ).1) w.1 := by
  refine ⟨?_, ?_, ?_⟩
  · intro j
    have code := extractedProfileInwardWordCode hn hk0 hk u w parent j
    have hstart : middleStage u.1
        (fun j ↦
          (extractedProfileMiddlePoint hn hk0 hk u w parent j.succ).1)
          j.castSucc =
        (extractedProfileMiddlePoint hn hk0 hk u w parent j.castSucc).1 := by
      simpa only [coe_profileMiddleStage] using
      (congrArg Subtype.val
        (extractedProfileMiddlePoint_eq_profileMiddleStage
          hn hk0 hk u w parent j.castSucc)).symm
    refine ⟨code.1, ?_, ?_⟩
    · simpa only [hstart] using code.2.1
    · simpa only [hstart] using code.2.2
  · exact extractedProfileReturnWordCode hn hk0 hk u w parent
  · have code := extractedProfileEscapeWordCode hn hk0 hk u w parent
    have hstart : middleStage u.1
        (fun j ↦
          (extractedProfileMiddlePoint hn hk0 hk u w parent j.succ).1)
          (Fin.last q) =
        (extractedProfileMiddlePoint hn hk0 hk u w parent (Fin.last q)).1 := by
      simpa only [coe_profileMiddleStage] using
      (congrArg Subtype.val
        (extractedProfileMiddlePoint_eq_profileMiddleStage
          hn hk0 hk u w parent (Fin.last q))).symm
    refine ⟨code.1, ?_, ?_⟩
    · simpa only [hstart] using code.2.1
    · simpa only [hstart] using code.2.2

/-- Reassembling the extracted retained spine with the extracted deleted
returns recovers the source parent stopped word exactly. -/
theorem extractedProfileAssemblyWord_eq_parent
    {n k q : ℕ} {center : Point}
    (hn : 2 ≤ n) (hk0 : 0 < k) (hk : k + 1 ≤ n)
    (u : ProfileCycleMiddlePoint n k center)
    (w : ProfileCycleOuterPoint n k center)
    (parent : BoundaryExcursionExitWordCode
      (profileOuterBoundary n k center)
      (profileInnerBoundary n k center)
      (profileInnerBoundary n (k + 1) center) u.1 q w.1) :
    erasedParentAssemblyWord
      (extractedProfileAssemblyCode hn hk0 hk u w parent) = parent.1 := by
  let code := extractedProfileAssemblyCode hn hk0 hk u w parent
  have hinward : (fun j : Fin q ↦ List.ofFn (code.1 j).1.2) =
      fun j ↦ List.ofFn
        (extractedProfileInwardWordCode hn hk0 hk u w parent j).1.2 := by
    funext j
    simp only [code, extractedProfileAssemblyCode]
    apply List.ext_get
    · simp
    · intro i hi hi'
      simp only [List.get_ofFn]
      congr 1
  have hchild : (fun j : Fin q ↦ List.ofFn (code.2.1 j).1.2) =
      fun j ↦ List.ofFn
        (extractedProfileReturnWordCode hn hk0 hk u w parent j).1.2 := by
    rfl
  have hescape : List.ofFn code.2.2.1.2 = List.ofFn
      (extractedProfileEscapeWordCode hn hk0 hk u w parent).1.2 := by
    simp only [code, extractedProfileAssemblyCode]
    apply List.ext_get
    · simp
    · intro i hi hi'
      simp only [List.get_ofFn]
      congr 1
  rw [show erasedParentAssemblyWord code = listStoppedWord
      (interleavedErasedParentList q
        (fun j ↦ List.ofFn (code.1 j).1.2)
        (fun j ↦ List.ofFn (code.2.1 j).1.2)
        (List.ofFn code.2.2.1.2)) by rfl,
    hinward, hchild, hescape,
    interleavedErasedParentList_eq_alternatingConcat,
    extractedProfileRetainedPieces_eq]
  have hwords : (fun j : Fin q ↦ List.ofFn
      (extractedProfileReturnWordCode hn hk0 hk u w parent j).1.2) =
      intervalWords (extendStoppedWord parent.1)
        (extractTimedReturnSkeleton (extendStoppedWord parent.1) u.1
          (profileInnerBoundary n k center)
          (profileInnerBoundary n (k + 1) center) parent.1.1 q).entrance
        (extractTimedReturnSkeleton (extendStoppedWord parent.1) u.1
          (profileInnerBoundary n k center)
          (profileInnerBoundary n (k + 1) center) parent.1.1 q).exit := by
    funext j
    exact extractedProfileReturnWordCode_toList hn hk0 hk u w parent j
  rw [hwords]
  rw [show alternatingConcat q
      (complementaryPieces q (extendStoppedWord parent.1) 0 parent.1.1
        (extractTimedReturnSkeleton (extendStoppedWord parent.1) u.1
          (profileInnerBoundary n k center)
          (profileInnerBoundary n (k + 1) center) parent.1.1 q).entrance
        (extractTimedReturnSkeleton (extendStoppedWord parent.1) u.1
          (profileInnerBoundary n k center)
          (profileInnerBoundary n (k + 1) center) parent.1.1 q).exit)
      (intervalWords (extendStoppedWord parent.1)
        (extractTimedReturnSkeleton (extendStoppedWord parent.1) u.1
          (profileInnerBoundary n k center)
          (profileInnerBoundary n (k + 1) center) parent.1.1 q).entrance
        (extractTimedReturnSkeleton (extendStoppedWord parent.1) u.1
          (profileInnerBoundary n k center)
          (profileInnerBoundary n (k + 1) center) parent.1.1 q).exit) =
      incrementSlice (extendStoppedWord parent.1) 0 parent.1.1 by
        exact reconstruct_extractTimedReturnSkeleton
          (profileReturnExit_complete hn hk0 hk u w parent)]
  have hslice : incrementSlice (extendStoppedWord parent.1) 0 parent.1.1 =
      List.ofFn parent.1.2 := by
    have hprefix := stepPrefix_extendStoppedWord parent.1
    change (fun k : Fin parent.1.1 ↦
      extendStoppedWord parent.1 (k : ℕ)) = parent.1.2 at hprefix
    simpa only [incrementSlice, Nat.sub_zero, Nat.zero_add] using
      congrArg List.ofFn hprefix
  exact (congrArg listStoppedWord hslice).trans
    (listStoppedWord_ofFn parent.1)

end

end Erdos1165.AnnularExtractedProfileSpineCode
