/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/
import ErdosProblems.Erdos1165.AsymmetricPaddedBridgeLiteralFactorization
import ErdosProblems.Erdos1165.AnnularExtractedProfileSpineCode

/-!
# Literal active padded factorization

Once a remote coarse bridge first enters the padded predecessor boundary,
its remaining word is a genuine excursion-count word from that boundary to
the retained remote boundary.  This file deletes its completed level-`p`
returns and packages the complementary pieces as canonical first-hit words
for the union of the level-`p` and remote boundaries.
-/

open Set

namespace Erdos1165.AsymmetricPaddedActiveFactorization

open AlternatingConcatPrefixFree AnnularBoundaryExcursionKernel
open AnnularErasedParentSpineProfileRow
open AnnularErasedParentSpineRowPartition AnnularProfileClocks
open AnnularOffspringRenewal AnnularOffspringScan
open AsymmetricPaddedBridgeExtraction AsymmetricPaddedRemoteRenewal
open AsymmetricSplitLevelSplice MarkedBridgeFactorization
open PlanarPotential RealDiscFinite TerminalExcursionPathwise
open TerminalBoundaryScan TerminalClockSplice TerminalSequentialVisitLaw
open TerminalSkeletonWords TerminalSpliceProfileGeometry ThickPoint
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

/-- Every completed padded return reaches the predecessor boundary before
the remote parent exits. -/
theorem paddedParentReturnComplete
    {n l p q : ℕ} {center : Point}
    (hn : 2 ≤ n) (hlp : l + 1 < p) (hp : p ≤ n)
    (u : PaddedMiddlePoint n p center)
    (w : PaddedOuterPoint n l center)
    (parent : BoundaryExcursionExitWordCode
      (profileInnerBoundary n l center)
      (profileInnerBoundary n (p - 1) center)
      (profileInnerBoundary n p center) u.1 q w.1) :
    ∀ j : Fin q,
      excursionStart
        (trajectoryFrom u.1 (extendStoppedWord parent.1))
        (profileInnerBoundary n (p - 1) center)
        (profileInnerBoundary n p center) parent.1.1 (j + 1) ≤
          parent.1.1 := by
  apply returnExitTime_le_of_boundaryExcursionExitAtom
    parent.2.1 parent.2.2.1
  intro z hz
  exact paddedBoundary_firstHitSeparates hn hlp hp hz

/-- Every predecessor-boundary clock, including the final escape clock, is
reached by the parent horizon. -/
theorem paddedParentExcursionStart_le
    {n l p q : ℕ} {center : Point}
    (hn : 2 ≤ n) (hlp : l + 1 < p) (hp : p ≤ n)
    (u : PaddedMiddlePoint n p center)
    (w : PaddedOuterPoint n l center)
    (parent : BoundaryExcursionExitWordCode
      (profileInnerBoundary n l center)
      (profileInnerBoundary n (p - 1) center)
      (profileInnerBoundary n p center) u.1 q w.1) :
    ∀ j : Fin (q + 1),
      excursionStart
        (trajectoryFrom u.1 (extendStoppedWord parent.1))
        (profileInnerBoundary n (p - 1) center)
        (profileInnerBoundary n p center) parent.1.1 j ≤ parent.1.1 := by
  intro j
  refine Fin.cases ?_ (fun i ↦ ?_) j
  · have hzero : trajectoryFrom u.1 (extendStoppedWord parent.1) 0 ∈
        profileInnerBoundary n (p - 1) center := by
      simpa only [PlanarPotential.trajectoryFrom_zero, profileInnerBoundary]
        using (mem_discBoundaryFinset.mp u.2)
    change excursionStart
      (trajectoryFrom u.1 (extendStoppedWord parent.1))
      (profileInnerBoundary n (p - 1) center)
      (profileInnerBoundary n p center) parent.1.1 0 ≤ parent.1.1
    rw [excursionStart_zero_eq_zero_of_mem _ _ _ _ hzero]
    exact Nat.zero_le _
  · exact paddedParentReturnComplete hn hlp hp u w parent i

/-- Every completed padded entrance clock is reached by the horizon. -/
theorem paddedParentExcursionFinish_le
    {n l p q : ℕ} {center : Point}
    (u : PaddedMiddlePoint n p center)
    (w : PaddedOuterPoint n l center)
    (parent : BoundaryExcursionExitWordCode
      (profileInnerBoundary n l center)
      (profileInnerBoundary n (p - 1) center)
      (profileInnerBoundary n p center) u.1 q w.1)
    (j : Fin q) :
    excursionFinish
        (trajectoryFrom u.1 (extendStoppedWord parent.1))
        (profileInnerBoundary n (p - 1) center)
        (profileInnerBoundary n p center) parent.1.1 j ≤ parent.1.1 := by
  have hcount : completedExcursionCount
      (trajectoryFrom u.1 (extendStoppedWord parent.1))
      (profileInnerBoundary n (p - 1) center)
      (profileInnerBoundary n p center) parent.1.1 = q := by
    simpa only [boundaryExcursionCount] using parent.2.2.1
  have hqle : q ≤ parent.1.1 + 1 := by
    calc
      q = completedExcursionCount
          (trajectoryFrom u.1 (extendStoppedWord parent.1))
          (profileInnerBoundary n (p - 1) center)
          (profileInnerBoundary n p center) parent.1.1 := hcount.symm
      _ ≤ parent.1.1 + 1 := completedExcursionCount_le _ _ _ _
  apply (excursionFinish_le_horizon_iff_lt_completedExcursionCount
    _ _ _ _ (by omega)).2
  rw [hcount]
  exact j.isLt

/-- Chronological predecessor-boundary endpoints of the retained pieces. -/
def extractedPaddedMiddlePoint
    {n l p q : ℕ} {center : Point}
    (hn : 2 ≤ n) (hlp : l + 1 < p) (hp : p ≤ n)
    (u : PaddedMiddlePoint n p center)
    (w : PaddedOuterPoint n l center)
    (parent : BoundaryExcursionExitWordCode
      (profileInnerBoundary n l center)
      (profileInnerBoundary n (p - 1) center)
      (profileInnerBoundary n p center) u.1 q w.1)
    (j : Fin (q + 1)) : PaddedMiddlePoint n p center :=
  ⟨trajectoryFrom u.1 (extendStoppedWord parent.1)
      (excursionStart
        (trajectoryFrom u.1 (extendStoppedWord parent.1))
        (profileInnerBoundary n (p - 1) center)
        (profileInnerBoundary n p center) parent.1.1 j),
    mem_discBoundaryFinset.mpr (by
      simpa only [profileInnerBoundary, excursionStart] using
        (firstHitThrough_mem_set_of_le _ _ _ _
          (paddedParentExcursionStart_le hn hlp hp u w parent j)))⟩

/-- Chronological level-`p` entrance endpoints. -/
def extractedPaddedInnerPoint
    {n l p q : ℕ} {center : Point}
    (u : PaddedMiddlePoint n p center)
    (w : PaddedOuterPoint n l center)
    (parent : BoundaryExcursionExitWordCode
      (profileInnerBoundary n l center)
      (profileInnerBoundary n (p - 1) center)
      (profileInnerBoundary n p center) u.1 q w.1)
    (j : Fin q) : PaddedInnerPoint n p center :=
  ⟨trajectoryFrom u.1 (extendStoppedWord parent.1)
      (excursionFinish
        (trajectoryFrom u.1 (extendStoppedWord parent.1))
        (profileInnerBoundary n (p - 1) center)
        (profileInnerBoundary n p center) parent.1.1 j),
    mem_discBoundaryFinset.mpr (by
      simpa only [profileInnerBoundary] using
        (excursionFinish_mem_inner_of_le
          (trajectoryFrom u.1 (extendStoppedWord parent.1))
          (profileInnerBoundary n (p - 1) center)
          (profileInnerBoundary n p center) parent.1.1 j
          (paddedParentExcursionFinish_le u w parent j)))⟩

@[simp] theorem extractedPaddedMiddlePoint_zero
    {n l p q : ℕ} {center : Point}
    (hn : 2 ≤ n) (hlp : l + 1 < p) (hp : p ≤ n)
    (u : PaddedMiddlePoint n p center)
    (w : PaddedOuterPoint n l center)
    (parent : BoundaryExcursionExitWordCode
      (profileInnerBoundary n l center)
      (profileInnerBoundary n (p - 1) center)
      (profileInnerBoundary n p center) u.1 q w.1) :
    extractedPaddedMiddlePoint hn hlp hp u w parent (0 : Fin (q + 1)) = u := by
  apply Subtype.ext
  change trajectoryFrom u.1 (extendStoppedWord parent.1)
    (excursionStart
      (trajectoryFrom u.1 (extendStoppedWord parent.1))
      (profileInnerBoundary n (p - 1) center)
      (profileInnerBoundary n p center) parent.1.1 0) = u.1
  rw [excursionStart_zero_eq_zero_of_mem]
  · exact PlanarPotential.trajectoryFrom_zero _ _
  · simpa only [PlanarPotential.trajectoryFrom_zero, profileInnerBoundary]
      using (mem_discBoundaryFinset.mp u.2)

/-- One retained predecessor-to-inner piece. -/
def extractedPaddedInwardWordCode
    {n l p q : ℕ} {center : Point}
    (u : PaddedMiddlePoint n p center)
    (w : PaddedOuterPoint n l center)
    (parent : BoundaryExcursionExitWordCode
      (profileInnerBoundary n l center)
      (profileInnerBoundary n (p - 1) center)
      (profileInnerBoundary n p center) u.1 q w.1)
    (j : Fin q) : BoundaryExitWordCode
      (profileInnerBoundary n p center ∪ profileInnerBoundary n l center)
      (trajectoryFrom u.1 (extendStoppedWord parent.1)
        (excursionStart
          (trajectoryFrom u.1 (extendStoppedWord parent.1))
          (profileInnerBoundary n (p - 1) center)
          (profileInnerBoundary n p center) parent.1.1 j))
      (extractedPaddedInnerPoint u w parent j).1 := by
  let s := trajectoryFrom u.1 (extendStoppedWord parent.1)
  let begin := excursionStart s (profileInnerBoundary n (p - 1) center)
    (profileInnerBoundary n p center) parent.1.1 j
  let finish := excursionFinish s (profileInnerBoundary n (p - 1) center)
    (profileInnerBoundary n p center) parent.1.1 j
  have hbegin : begin ≤ finish := excursionStart_le_finish _ _ _ _ _
  have hfinish : finish ≤ parent.1.1 :=
    paddedParentExcursionFinish_le u w parent j
  have hspec := firstHitThrough_spec_of_le s
    (profileInnerBoundary n p center) begin parent.1.1
    (by simpa only [finish, excursionFinish] using hfinish)
  apply incrementSliceBoundaryExitWordCode u.1 (extendStoppedWord parent.1)
    (profileInnerBoundary n p center ∪ profileInnerBoundary n l center) hbegin
  · exact Or.inl (by
      simpa only [s, finish, excursionFinish, begin,
        extractedPaddedInnerPoint] using hspec.2.1)
  · intro r hbr hrf
    rw [Set.mem_union]
    push Not
    constructor
    · exact hspec.2.2 r
        (by simpa only [finish, excursionFinish] using hrf) hbr
    · exact parent.2.1.2 r (hrf.trans_le hfinish)

/-- The final retained predecessor-to-remote-boundary piece. -/
def extractedPaddedEscapeWordCode
    {n l p q : ℕ} {center : Point}
    (hn : 2 ≤ n) (hlp : l + 1 < p) (hp : p ≤ n)
    (u : PaddedMiddlePoint n p center)
    (w : PaddedOuterPoint n l center)
    (parent : BoundaryExcursionExitWordCode
      (profileInnerBoundary n l center)
      (profileInnerBoundary n (p - 1) center)
      (profileInnerBoundary n p center) u.1 q w.1) :
    BoundaryExitWordCode
      (profileInnerBoundary n p center ∪ profileInnerBoundary n l center)
      (extractedPaddedMiddlePoint hn hlp hp u w parent (Fin.last q)).1 w.1 := by
  let s := trajectoryFrom u.1 (extendStoppedWord parent.1)
  let begin := excursionStart s (profileInnerBoundary n (p - 1) center)
    (profileInnerBoundary n p center) parent.1.1 q
  have hbegin : begin ≤ parent.1.1 := by
    simpa only [begin, s, Fin.val_last] using
      (paddedParentExcursionStart_le hn hlp hp u w parent (Fin.last q))
  have hcount : completedExcursionCount s
      (profileInnerBoundary n (p - 1) center)
      (profileInnerBoundary n p center) parent.1.1 = q := by
    simpa only [s, boundaryExcursionCount] using parent.2.2.1
  have hp0 : 0 < p := by omega
  have hdisjoint : Disjoint (profileInnerBoundary n (p - 1) center)
      (profileInnerBoundary n p center) := by
    have hp' : (p - 1) + 1 ≤ n := by omega
    simpa only [Nat.sub_add_cancel hp0] using
      (adjacent_profileInnerBoundaries_disjoint
        (by omega : 1 ≤ n) hp' center)
  have hsentinel : excursionFinish s
      (profileInnerBoundary n (p - 1) center)
      (profileInnerBoundary n p center) parent.1.1 q = parent.1.1 + 1 := by
    simpa only [hcount] using
      (excursionFinish_completedExcursionCount_eq_sentinel s
        (profileInnerBoundary n (p - 1) center)
        (profileInnerBoundary n p center) hdisjoint parent.1.1)
  have hinnerAvoid : AvoidsThrough s (profileInnerBoundary n p center)
      begin parent.1.1 := by
    apply avoidsThrough_of_firstHitThrough_eq_sentinel
    simpa only [excursionFinish, begin] using hsentinel
  have code := incrementSliceBoundaryExitWordCode u.1
    (extendStoppedWord parent.1)
    (profileInnerBoundary n p center ∪ profileInnerBoundary n l center)
    hbegin (Or.inr parent.2.1.1) (by
      intro r hbr hrh
      rw [Set.mem_union]
      push Not
      exact ⟨hinnerAvoid r hbr hrh.le, parent.2.1.2 r hrh⟩)
  refine ⟨code.1, ?_, ?_⟩
  · simpa only [extractedPaddedMiddlePoint, s, begin, Fin.val_last] using
      code.2.1
  · simpa only [extractedPaddedMiddlePoint, s, begin, Fin.val_last] using
      code.2.2.trans parent.2.2.2

/-- The deleted inner-to-predecessor return word. -/
def extractedPaddedReturnWordCode
    {n l p q : ℕ} {center : Point}
    (hn : 2 ≤ n) (hlp : l + 1 < p) (hp : p ≤ n)
    (u : PaddedMiddlePoint n p center)
    (w : PaddedOuterPoint n l center)
    (parent : BoundaryExcursionExitWordCode
      (profileInnerBoundary n l center)
      (profileInnerBoundary n (p - 1) center)
      (profileInnerBoundary n p center) u.1 q w.1)
    (j : Fin q) : BoundaryExitWordCode
      (profileInnerBoundary n (p - 1) center)
      (extractedPaddedInnerPoint u w parent j).1
      (extractedPaddedMiddlePoint hn hlp hp u w parent j.succ).1 := by
  let code := extractedReturnCodes
    (paddedParentReturnComplete hn hlp hp u w parent) j
  refine ⟨code.1, ?_, ?_⟩
  · simpa only [code, extractedPaddedInnerPoint, extractedPaddedMiddlePoint,
      returnEntrancePoint, returnEntranceTime, returnExitPoint, returnExitTime,
      Fin.val_succ] using code.2.1
  · simpa only [code, extractedPaddedInnerPoint, extractedPaddedMiddlePoint,
      returnEntrancePoint, returnEntranceTime, returnExitPoint, returnExitTime,
      Fin.val_succ] using code.2.2

@[simp] theorem extractedPaddedInwardWordCode_toList
    {n l p q : ℕ} {center : Point}
    (u : PaddedMiddlePoint n p center)
    (w : PaddedOuterPoint n l center)
    (parent : BoundaryExcursionExitWordCode
      (profileInnerBoundary n l center)
      (profileInnerBoundary n (p - 1) center)
      (profileInnerBoundary n p center) u.1 q w.1)
    (j : Fin q) :
    List.ofFn (extractedPaddedInwardWordCode u w parent j).1.2 =
      incrementSlice (extendStoppedWord parent.1)
        (excursionStart
          (trajectoryFrom u.1 (extendStoppedWord parent.1))
          (profileInnerBoundary n (p - 1) center)
          (profileInnerBoundary n p center) parent.1.1 j)
        (excursionFinish
          (trajectoryFrom u.1 (extendStoppedWord parent.1))
          (profileInnerBoundary n (p - 1) center)
          (profileInnerBoundary n p center) parent.1.1 j) := by
  simp only [extractedPaddedInwardWordCode,
    incrementSliceBoundaryExitWordCode,
    TerminalVisitSpliceInvariance.stoppedWordOfList]
  exact List.ofFn_get _

@[simp] theorem extractedPaddedEscapeWordCode_toList
    {n l p q : ℕ} {center : Point}
    (hn : 2 ≤ n) (hlp : l + 1 < p) (hp : p ≤ n)
    (u : PaddedMiddlePoint n p center)
    (w : PaddedOuterPoint n l center)
    (parent : BoundaryExcursionExitWordCode
      (profileInnerBoundary n l center)
      (profileInnerBoundary n (p - 1) center)
      (profileInnerBoundary n p center) u.1 q w.1) :
    List.ofFn (extractedPaddedEscapeWordCode hn hlp hp u w parent).1.2 =
      incrementSlice (extendStoppedWord parent.1)
        (excursionStart
          (trajectoryFrom u.1 (extendStoppedWord parent.1))
          (profileInnerBoundary n (p - 1) center)
          (profileInnerBoundary n p center) parent.1.1 q)
        parent.1.1 := by
  simp only [extractedPaddedEscapeWordCode,
    incrementSliceBoundaryExitWordCode,
    TerminalVisitSpliceInvariance.stoppedWordOfList]
  exact List.ofFn_get _

@[simp] theorem extractedPaddedReturnWordCode_toList
    {n l p q : ℕ} {center : Point}
    (hn : 2 ≤ n) (hlp : l + 1 < p) (hp : p ≤ n)
    (u : PaddedMiddlePoint n p center)
    (w : PaddedOuterPoint n l center)
    (parent : BoundaryExcursionExitWordCode
      (profileInnerBoundary n l center)
      (profileInnerBoundary n (p - 1) center)
      (profileInnerBoundary n p center) u.1 q w.1)
    (j : Fin q) :
    List.ofFn
        (extractedPaddedReturnWordCode hn hlp hp u w parent j).1.2 =
      intervalWords (extendStoppedWord parent.1)
        (extractTimedReturnSkeleton (extendStoppedWord parent.1) u.1
          (profileInnerBoundary n (p - 1) center)
          (profileInnerBoundary n p center) parent.1.1 q).entrance
        (extractTimedReturnSkeleton (extendStoppedWord parent.1) u.1
          (profileInnerBoundary n (p - 1) center)
          (profileInnerBoundary n p center) parent.1.1 q).exit j := by
  change extractedReturnWords
    (paddedParentReturnComplete hn hlp hp u w parent) j = _
  exact extractedReturnCodes_toList
    (paddedParentReturnComplete hn hlp hp u w parent) j

/-- The extracted predecessor endpoints are the standard middle-stage
array determined by the initial endpoint and completed returns. -/
theorem extractedPaddedMiddlePoint_eq_middleStage
    {n l p q : ℕ} {center : Point}
    (hn : 2 ≤ n) (hlp : l + 1 < p) (hp : p ≤ n)
    (u : PaddedMiddlePoint n p center)
    (w : PaddedOuterPoint n l center)
    (parent : BoundaryExcursionExitWordCode
      (profileInnerBoundary n l center)
      (profileInnerBoundary n (p - 1) center)
      (profileInnerBoundary n p center) u.1 q w.1) :
    ∀ i : Fin (q + 1),
      extractedPaddedMiddlePoint hn hlp hp u w parent i =
        profileMiddleStage u
          (fun j ↦ extractedPaddedMiddlePoint hn hlp hp u w parent j.succ) i := by
  intro i
  refine Fin.cases ?_ (fun j ↦ ?_) i
  · exact extractedPaddedMiddlePoint_zero hn hlp hp u w parent
  · rfl

/-- The retained padded pieces are literally the complementary pieces of
the deleted-return skeleton. -/
theorem extractedPaddedRetainedPieces_eq
    {n l p q : ℕ} {center : Point}
    (hn : 2 ≤ n) (hlp : l + 1 < p) (hp : p ≤ n)
    (u : PaddedMiddlePoint n p center)
    (w : PaddedOuterPoint n l center)
    (parent : BoundaryExcursionExitWordCode
      (profileInnerBoundary n l center)
      (profileInnerBoundary n (p - 1) center)
      (profileInnerBoundary n p center) u.1 q w.1) :
    Fin.lastCases
        (List.ofFn
          (extractedPaddedEscapeWordCode hn hlp hp u w parent).1.2)
        (fun j ↦ List.ofFn
          (extractedPaddedInwardWordCode u w parent j).1.2) =
      complementaryPieces q (extendStoppedWord parent.1) 0 parent.1.1
        (extractTimedReturnSkeleton (extendStoppedWord parent.1) u.1
          (profileInnerBoundary n (p - 1) center)
          (profileInnerBoundary n p center) parent.1.1 q).entrance
        (extractTimedReturnSkeleton (extendStoppedWord parent.1) u.1
          (profileInnerBoundary n (p - 1) center)
          (profileInnerBoundary n p center) parent.1.1 q).exit := by
  funext i
  refine Fin.lastCases ?_ (fun j ↦ ?_) i
  · simp only [Fin.lastCases_last, extractedPaddedEscapeWordCode_toList]
    cases q with
    | zero =>
        change incrementSlice (extendStoppedWord parent.1)
            (excursionStart
              (trajectoryFrom u.1 (extendStoppedWord parent.1))
              (profileInnerBoundary n (p - 1) center)
              (profileInnerBoundary n p center) parent.1.1 0)
              parent.1.1 = incrementSlice (extendStoppedWord parent.1) 0
                parent.1.1
        rw [excursionStart_zero_eq_zero_of_mem]
        simpa only [PlanarPotential.trajectoryFrom_zero, profileInnerBoundary]
          using (mem_discBoundaryFinset.mp u.2)
    | succ r =>
        rw [complementaryPieces_last r]
        rfl
  · simp only [Fin.lastCases_castSucc,
      extractedPaddedInwardWordCode_toList]
    cases q with
    | zero => exact Fin.elim0 j
    | succ r =>
        refine Fin.cases ?_ (fun a ↦ ?_) j
        · rw [show (0 : Fin (r + 1)).castSucc =
              (0 : Fin (r + 1 + 1)) by ext; rfl,
            complementaryPieces_zero]
          change incrementSlice (extendStoppedWord parent.1)
              (excursionStart
                (trajectoryFrom u.1 (extendStoppedWord parent.1))
                (profileInnerBoundary n (p - 1) center)
                (profileInnerBoundary n p center) parent.1.1 0)
              (excursionFinish
                (trajectoryFrom u.1 (extendStoppedWord parent.1))
                (profileInnerBoundary n (p - 1) center)
                (profileInnerBoundary n p center) parent.1.1 0) =
            incrementSlice (extendStoppedWord parent.1) 0
              (excursionFinish
                (trajectoryFrom u.1 (extendStoppedWord parent.1))
                (profileInnerBoundary n (p - 1) center)
                (profileInnerBoundary n p center) parent.1.1 0)
          rw [excursionStart_zero_eq_zero_of_mem]
          simpa only [PlanarPotential.trajectoryFrom_zero,
            profileInnerBoundary] using (mem_discBoundaryFinset.mp u.2)
        · rw [show a.succ.castSucc = a.castSucc.succ by ext; rfl,
            complementaryPieces_succ (extendStoppedWord parent.1) 0
              parent.1.1 _ _ a.castSucc (Nat.succ_lt_succ a.isLt)]
          rfl

/-- Complete literal assembly extracted from an active padded parent. -/
def extractedPaddedAssemblyCode
    {n l p q : ℕ} {center : Point}
    (hn : 2 ≤ n) (hlp : l + 1 < p) (hp : p ≤ n)
    (u : PaddedMiddlePoint n p center)
    (w : PaddedOuterPoint n l center)
    (parent : BoundaryExcursionExitWordCode
      (profileInnerBoundary n l center)
      (profileInnerBoundary n (p - 1) center)
      (profileInnerBoundary n p center) u.1 q w.1) :
    ErasedParentAssemblyCode q
      (profileInnerBoundary n p center ∪ profileInnerBoundary n l center)
      (profileInnerBoundary n (p - 1) center) u.1
      (fun j ↦ (extractedPaddedInnerPoint u w parent j).1)
      (fun j ↦
        (extractedPaddedMiddlePoint hn hlp hp u w parent j.succ).1) w.1 := by
  refine ⟨?_, ?_, ?_⟩
  · intro j
    have code := extractedPaddedInwardWordCode u w parent j
    have hstart : middleStage u.1
        (fun j ↦
          (extractedPaddedMiddlePoint hn hlp hp u w parent j.succ).1)
          j.castSucc =
        (extractedPaddedMiddlePoint hn hlp hp u w parent j.castSucc).1 := by
      simpa only [coe_profileMiddleStage] using
        (congrArg Subtype.val
          (extractedPaddedMiddlePoint_eq_middleStage
            hn hlp hp u w parent j.castSucc)).symm
    have hstartRaw : middleStage u.1
        (fun j ↦
          (extractedPaddedMiddlePoint hn hlp hp u w parent j.succ).1)
          j.castSucc =
        trajectoryFrom u.1 (extendStoppedWord parent.1)
          (excursionStart
            (trajectoryFrom u.1 (extendStoppedWord parent.1))
            (profileInnerBoundary n (p - 1) center)
            (profileInnerBoundary n p center) parent.1.1 j) := by
      calc
        _ = (extractedPaddedMiddlePoint hn hlp hp u w parent
              j.castSucc).1 := hstart
        _ = _ := by rfl
    refine ⟨code.1, ?_, ?_⟩
    · simpa only [hstartRaw] using code.2.1
    · simpa only [hstartRaw] using code.2.2
  · exact extractedPaddedReturnWordCode hn hlp hp u w parent
  · have code := extractedPaddedEscapeWordCode hn hlp hp u w parent
    have hstart : middleStage u.1
        (fun j ↦
          (extractedPaddedMiddlePoint hn hlp hp u w parent j.succ).1)
          (Fin.last q) =
        (extractedPaddedMiddlePoint hn hlp hp u w parent (Fin.last q)).1 := by
      simpa only [coe_profileMiddleStage] using
        (congrArg Subtype.val
          (extractedPaddedMiddlePoint_eq_middleStage
            hn hlp hp u w parent (Fin.last q))).symm
    refine ⟨code.1, ?_, ?_⟩
    · simpa only [hstart] using code.2.1
    · simpa only [hstart] using code.2.2

/-- Reassembling the retained padded spine with its deleted returns recovers
the active parent stopped word exactly. -/
theorem extractedPaddedAssemblyWord_eq_parent
    {n l p q : ℕ} {center : Point}
    (hn : 2 ≤ n) (hlp : l + 1 < p) (hp : p ≤ n)
    (u : PaddedMiddlePoint n p center)
    (w : PaddedOuterPoint n l center)
    (parent : BoundaryExcursionExitWordCode
      (profileInnerBoundary n l center)
      (profileInnerBoundary n (p - 1) center)
      (profileInnerBoundary n p center) u.1 q w.1) :
    erasedParentAssemblyWord
      (extractedPaddedAssemblyCode hn hlp hp u w parent) = parent.1 := by
  let code := extractedPaddedAssemblyCode hn hlp hp u w parent
  have hinward : (fun j : Fin q ↦ List.ofFn (code.1 j).1.2) =
      fun j ↦ List.ofFn
        (extractedPaddedInwardWordCode u w parent j).1.2 := by
    funext j
    simp only [code, extractedPaddedAssemblyCode]
    apply List.ext_get
    · simp
    · intro i hi hi'
      simp only [List.get_ofFn]
      congr 1
  have hchild : (fun j : Fin q ↦ List.ofFn (code.2.1 j).1.2) =
      fun j ↦ List.ofFn
        (extractedPaddedReturnWordCode hn hlp hp u w parent j).1.2 := by
    rfl
  have hescape : List.ofFn code.2.2.1.2 = List.ofFn
      (extractedPaddedEscapeWordCode hn hlp hp u w parent).1.2 := by
    simp only [code, extractedPaddedAssemblyCode]
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
    extractedPaddedRetainedPieces_eq]
  have hwords : (fun j : Fin q ↦ List.ofFn
      (extractedPaddedReturnWordCode hn hlp hp u w parent j).1.2) =
      intervalWords (extendStoppedWord parent.1)
        (extractTimedReturnSkeleton (extendStoppedWord parent.1) u.1
          (profileInnerBoundary n (p - 1) center)
          (profileInnerBoundary n p center) parent.1.1 q).entrance
        (extractTimedReturnSkeleton (extendStoppedWord parent.1) u.1
          (profileInnerBoundary n (p - 1) center)
          (profileInnerBoundary n p center) parent.1.1 q).exit := by
    funext j
    exact extractedPaddedReturnWordCode_toList hn hlp hp u w parent j
  rw [hwords]
  rw [show alternatingConcat q
      (complementaryPieces q (extendStoppedWord parent.1) 0 parent.1.1
        (extractTimedReturnSkeleton (extendStoppedWord parent.1) u.1
          (profileInnerBoundary n (p - 1) center)
          (profileInnerBoundary n p center) parent.1.1 q).entrance
        (extractTimedReturnSkeleton (extendStoppedWord parent.1) u.1
          (profileInnerBoundary n (p - 1) center)
          (profileInnerBoundary n p center) parent.1.1 q).exit)
      (intervalWords (extendStoppedWord parent.1)
        (extractTimedReturnSkeleton (extendStoppedWord parent.1) u.1
          (profileInnerBoundary n (p - 1) center)
          (profileInnerBoundary n p center) parent.1.1 q).entrance
        (extractTimedReturnSkeleton (extendStoppedWord parent.1) u.1
          (profileInnerBoundary n (p - 1) center)
          (profileInnerBoundary n p center) parent.1.1 q).exit) =
      incrementSlice (extendStoppedWord parent.1) 0 parent.1.1 by
        exact reconstruct_extractTimedReturnSkeleton
          (paddedParentReturnComplete hn hlp hp u w parent)]
  have hslice : incrementSlice (extendStoppedWord parent.1) 0 parent.1.1 =
      List.ofFn parent.1.2 := by
    have hprefix := stepPrefix_extendStoppedWord parent.1
    change (fun k : Fin parent.1.1 ↦ extendStoppedWord parent.1 (k : ℕ)) =
      parent.1.2 at hprefix
    simpa only [incrementSlice, Nat.sub_zero, Nat.zero_add] using
      congrArg List.ofFn hprefix
  exact (congrArg listStoppedWord hslice).trans
    (listStoppedWord_ofFn parent.1)

end

end Erdos1165.AsymmetricPaddedActiveFactorization
