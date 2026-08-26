/- leanprover/lean4:v4.33.0 -/
import ErdosProblems.Erdos547b.Lemma58GlobalPlannedOnlineState
import ErdosProblems.Erdos547b.Lemma58PlannedOwnerLocalStep
import ErdosProblems.Erdos547b.Lemma58ChosenOrientationTransport

/-!
# Plan-certified synchronized owner successors

This file pulls the global branch-coordinate side plan back to the literal
owner batch on each matching edge.  The resulting successor datum contains
only plan-certified threshold/Appendix/fixed source data.
-/

open scoped SimpleGraph
noncomputable section

namespace Erdos547b.ZhaoLemma58GlobalPlannedOwnerSuccessor

open Finset Fintype SimpleGraph
open Erdos547b.RegularPair
open Erdos547b.ZhaoLemma59Part2Full
open Erdos547b.ZhaoClaim616SourceBridge
open Erdos547b.ZhaoClaim616SourceBridge.OrderedBranchForest
open Erdos547b.ZhaoLemma58MatchingAssembly
open Erdos547b.ZhaoLemma58DynamicBatchAppend
open Erdos547b.ZhaoLemma58ChosenOwnerBatches
open Erdos547b.ZhaoLemma58GlobalOwnerOnlineState
open Erdos547b.ZhaoLemma58GlobalOwnerBranchImage
open Erdos547b.ZhaoLemma58GlobalPlannedOnlineState
open Erdos547b.ZhaoLemma58PlannedOwnerLocalStep
open Erdos547b.ZhaoLemma58ChosenOrientationTransport
open Erdos547b.ZhaoLemma58GlobalCutOnline
open Erdos547b.ZhaoLemma58OnlineParentSideCleaning

universe v

/-- Owner-`n` component indices inside one matching-edge fiber. -/
abbrev onlineOwnerBatch
    {r b k : ℕ}
    (F : OrderedBranchForest r b) (assign : Fin b → Fin k)
    (e : Fin k) (n : ℕ) (hn : n < r) :=
  ownerBatch Finset.univ (onlineFiberOwner F assign e) ⟨n, hn⟩

/-- Literal selected forest of the owner-`n` batch on edge `e`. -/
abbrev onlineOwnerBatchForest
    {r b k : ℕ}
    (F : OrderedBranchForest r b) (assign : Fin b → Fin k)
    (e : Fin k) (n : ℕ) (hn : n < r) :=
  selectedForest (onlineFiberForest F assign e)
    (onlineOwnerBatch F assign e n hn)

/-- Original global branch represented by a local owner-batch component. -/
noncomputable def onlineOwnerBatchBranch
    {r b k : ℕ}
    (F : OrderedBranchForest r b) (assign : Fin b → Fin k)
    (e : Fin k) (n : ℕ) (hn : n < r)
    (i : Fin (onlineOwnerBatch F assign e n hn).card) : Fin b :=
  OrderedBranchForest.selectedEquiv (matchingFiber assign e)
    (OrderedBranchForest.selectedEquiv
      (onlineOwnerBatch F assign e n hn) i)

/-- Every branch in the owner-`n` batch has literal global owner `n`. -/
@[simp] theorem onlineOwnerBatchBranch_owner
    {r b k : ℕ}
    (F : OrderedBranchForest r b) (assign : Fin b → Fin k)
    (e : Fin k) (n : ℕ) (hn : n < r)
    (i : Fin (onlineOwnerBatch F assign e n hn).card) :
    F.owner (onlineOwnerBatchBranch F assign e n hn i) = ⟨n, hn⟩ := by
  change onlineFiberOwner F assign e
      (OrderedBranchForest.selectedEquiv
        (onlineOwnerBatch F assign e n hn) i) = ⟨n, hn⟩
  exact (Finset.mem_filter.mp
    (OrderedBranchForest.selectedEquiv
      (onlineOwnerBatch F assign e n hn) i).property).2

/-- Every branch in the edge-`e` owner batch is literally assigned to `e`. -/
theorem onlineOwnerBatchBranch_assign
    {r b k : ℕ}
    (F : OrderedBranchForest r b) (assign : Fin b → Fin k)
    (e : Fin k) (n : ℕ) (hn : n < r)
    (i : Fin (onlineOwnerBatch F assign e n hn).card) :
    assign (onlineOwnerBatchBranch F assign e n hn i) = e := by
  exact (mem_matchingFiber assign e _).mp
    (OrderedBranchForest.selectedEquiv (matchingFiber assign e)
      (OrderedBranchForest.selectedEquiv
        (onlineOwnerBatch F assign e n hn) i)).property

/-- Original global vertex coordinate represented by a local owner-batch
coordinate. -/
noncomputable def onlineOwnerBatchVertex
    {r b k : ℕ}
    (F : OrderedBranchForest r b) (assign : Fin b → Fin k)
    (e : Fin k) (n : ℕ) (hn : n < r)
    (i : Fin (onlineOwnerBatch F assign e n hn).card)
    (a : Fin ((onlineOwnerBatchForest F assign e n hn).size i)) :
    Fin (F.branches.size (onlineOwnerBatchBranch F assign e n hn i)) :=
  Fin.cast (by rfl) a

/-- Pull the global branch-root side plan back to one owner batch. -/
def onlineOwnerBatchRootAllowed
    {r b k : ℕ}
    (F : OrderedBranchForest r b) (assign : Fin b → Fin k)
    (e : Fin k) (n : ℕ) (hn : n < r)
    (rootAllowed : Fin b → Finset (Fin 2))
    (i : Fin (onlineOwnerBatch F assign e n hn).card) : Finset (Fin 2) :=
  rootAllowed (onlineOwnerBatchBranch F assign e n hn i)

/-- Pull the global coordinate-side plan back to one owner batch. -/
def onlineOwnerBatchCoordinateAllowed
    {r b k : ℕ}
    (F : OrderedBranchForest r b) (assign : Fin b → Fin k)
    (e : Fin k) (n : ℕ) (hn : n < r)
    (coordinateAllowed : (Σ j, Fin (F.branches.size j)) → Finset (Fin 2))
    (z : Σ i, Fin ((onlineOwnerBatchForest F assign e n hn).size i)) :
    Finset (Fin 2) :=
  coordinateAllowed
    ⟨onlineOwnerBatchBranch F assign e n hn z.1,
      onlineOwnerBatchVertex F assign e n hn z.1 z.2⟩

/-- Plan-certified source/live-host datum for owner `n` on every matching
edge after reparenting the already embedded prefix. -/
abbrev PlannedOnlineOwnerSuccessorData
    {r b k : ℕ} {B : Type v} [Fintype B] [DecidableEq B]
    (F : OrderedBranchForest r b) (G : SimpleGraph B) [DecidableRel G.Adj]
    (assign : Fin b → Fin k)
    (whole endpoint : Fin k → Fin 2 → Finset B)
    (rho density : Fin k → ℝ)
    (rootCandidate : Fin r → Finset B)
    (rootAllowed : Fin b → Finset (Fin 2))
    (coordinateAllowed : (Σ j, Fin (F.branches.size j)) → Finset (Fin 2))
    (n : ℕ) (hn : n < r)
    (S : OnlineOwnerPrefixState F G assign endpoint rootCandidate n)
    (z : B) :=
  ∀ e, PlannedOwnerLocalStepData
    (onlineOwnerBatchForest F assign e n hn) G
    (fun i ↦ extendedRootImage S.rootImage n hn z
      (onlineFiberOwner F assign e
        (OrderedBranchForest.selectedEquiv
          (onlineOwnerBatch F assign e n hn) i)))
    (whole e)
    (fun c ↦ endpoint e c \
      (reparentedEdgeState F G assign endpoint rootCandidate n hn S z e).used c)
    (rho e) (density e)
    (onlineOwnerBatchRootAllowed F assign e n hn rootAllowed)
    (onlineOwnerBatchCoordinateAllowed F assign e n hn coordinateAllowed)

/-- Forget the side-plan certificates, retaining the deterministic local
source data consumed by the base synchronized successor. -/
noncomputable def PlannedOnlineOwnerSuccessorData.toOnline
    {r b k : ℕ} {B : Type v} [Fintype B] [DecidableEq B]
    (F : OrderedBranchForest r b) (G : SimpleGraph B) [DecidableRel G.Adj]
    (assign : Fin b → Fin k)
    (whole endpoint : Fin k → Fin 2 → Finset B)
    (rho density : Fin k → ℝ)
    (rootCandidate : Fin r → Finset B)
    (rootAllowed : Fin b → Finset (Fin 2))
    (coordinateAllowed : (Σ j, Fin (F.branches.size j)) → Finset (Fin 2))
    (n : ℕ) (hn : n < r)
    (S : OnlineOwnerPrefixState F G assign endpoint rootCandidate n)
    (z : B)
    (D : PlannedOnlineOwnerSuccessorData F G assign whole endpoint rho
      density rootCandidate rootAllowed coordinateAllowed n hn S z) :
    OnlineOwnerSuccessorData F G assign whole endpoint rho density
      rootCandidate n hn S z := by
  intro e
  exact (D e).toOwnerLocalStepData
    (onlineOwnerBatchForest F assign e n hn) G
    (fun i ↦ extendedRootImage S.rootImage n hn z
      (onlineFiberOwner F assign e
        (OrderedBranchForest.selectedEquiv
          (onlineOwnerBatch F assign e n hn) i)))
    (whole e)
    (fun c ↦ endpoint e c \
      (reparentedEdgeState F G assign endpoint rootCandidate n hn S z e).used c)
    (rho e) (density e)
    (onlineOwnerBatchRootAllowed F assign e n hn rootAllowed)
    (onlineOwnerBatchCoordinateAllowed F assign e n hn coordinateAllowed)

/-- Extend one globally synchronized owner while preserving the coordinate
side-plan invariant. -/
noncomputable def extendPlannedOnlineOwnerPrefixState
    {r b k : ℕ} {B : Type v} [Fintype B] [DecidableEq B]
    (F : OrderedBranchForest r b) (G : SimpleGraph B) [DecidableRel G.Adj]
    (assign : Fin b → Fin k)
    (whole endpoint : Fin k → Fin 2 → Finset B)
    (hendpoint : ∀ e c, endpoint e c ⊆ whole e c)
    (hwholeDisjoint : ∀ e, Disjoint (whole e 0) (whole e 1))
    (rho density : Fin k → ℝ)
    (rootCandidate : Fin r → Finset B)
    (rootAllowed : Fin b → Finset (Fin 2))
    (coordinateAllowed : (Σ j, Fin (F.branches.size j)) → Finset (Fin 2))
    (n : ℕ) (hn : n < r)
    (S : PlannedOnlineOwnerPrefixState F G assign endpoint rootCandidate
      coordinateAllowed n)
    (z : B) (hzmem : z ∈ rootCandidate ⟨n, hn⟩)
    (hzfresh : ∀ q, q.val < n → z ≠ S.state.rootImage q)
    (D : PlannedOnlineOwnerSuccessorData F G assign whole endpoint rho
      density rootCandidate rootAllowed coordinateAllowed n hn S.state
      z) :
    PlannedOnlineOwnerPrefixState F G assign endpoint rootCandidate
      coordinateAllowed (n + 1) := by
  classical
  let Dplain := D.toOnline F G assign whole endpoint rho density rootCandidate
    rootAllowed coordinateAllowed n hn S.state z
  let next := extendOnlineOwnerPrefixState F G assign whole endpoint hendpoint
    hwholeDisjoint rho density rootCandidate n hn S.state z hzmem hzfresh
    Dplain
  refine { state := next, coordinate_side_mem := ?_ }
  intro j hj a
  by_cases hold : (F.owner j).val < n
  · have hi : assignmentIndex assign j ∈ ownerPrefix Finset.univ
        (onlineFiberOwner F assign (assign j)) n :=
      (assignmentIndex_mem_ownerPrefix F assign j n).2 hold
    have horient := extendOnlineOwnerPrefixState_orient_before F G assign
      whole endpoint hendpoint hwholeDisjoint rho density rootCandidate n hn
      S.state z hzmem hzfresh Dplain (assign j)
      (assignmentIndex assign j) hi
    have hmem := S.coordinate_side_mem j hold a
    simpa only [next, Dplain, horient] using hmem
  · have howner : F.owner j = ⟨n, hn⟩ := by
      apply Fin.ext
      change (F.owner j).val = n
      omega
    let e := assign j
    let iFiber := assignmentIndex assign j
    have hiBatch : iFiber ∈ onlineOwnerBatch F assign e n hn := by
      rw [onlineOwnerBatch]
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      simpa only [e, iFiber, onlineFiberOwner,
        selectedEquiv_assignmentIndex]
        using howner
    let iLocal := selectedIndex (onlineOwnerBatch F assign e n hn)
      iFiber hiBatch
    let aFiber := assignmentVertex F assign j a
    let aLocal := selectedVertex (onlineFiberForest F assign e)
      (onlineOwnerBatch F assign e n hn) iFiber hiBatch aFiber
    let Dlocal := D e
    let Downer := Dlocal.toOwnerLocalStepData
      (onlineOwnerBatchForest F assign e n hn) G
      (fun i ↦ extendedRootImage S.state.rootImage n hn z
        (onlineFiberOwner F assign e
          (Erdos547b.ZhaoClaim616SourceBridge.OrderedBranchForest.selectedEquiv
            (onlineOwnerBatch F assign e n hn) i)))
      (whole e)
      (fun c ↦ endpoint e c \
        (reparentedEdgeState F G assign endpoint rootCandidate n hn
          S.state z e).used c)
      (rho e) (density e)
      (onlineOwnerBatchRootAllowed F assign e n hn rootAllowed)
      (onlineOwnerBatchCoordinateAllowed F assign e n hn coordinateAllowed)
    have hplan := Dlocal.orientation_coordinate_side_mem
      (onlineOwnerBatchForest F assign e n hn) G
      (fun i ↦ extendedRootImage S.state.rootImage n hn z
        (onlineFiberOwner F assign e
          (Erdos547b.ZhaoClaim616SourceBridge.OrderedBranchForest.selectedEquiv
            (onlineOwnerBatch F assign e n hn) i)))
      (whole e)
      (fun c ↦ endpoint e c \
        (reparentedEdgeState F G assign endpoint rootCandidate n hn
          S.state z e).used c)
      (rho e) (density e)
      (onlineOwnerBatchRootAllowed F assign e n hn rootAllowed)
      (onlineOwnerBatchCoordinateAllowed F assign e n hn coordinateAllowed)
      iLocal aLocal
    have horient := extendOnlineOwnerPrefixState_orient_current F G assign
      whole endpoint hendpoint hwholeDisjoint rho density rootCandidate n hn
      S.state z hzmem hzfresh Dplain e iLocal
    have hindex :
        (Erdos547b.ZhaoClaim616SourceBridge.OrderedBranchForest.selectedEquiv
          (onlineOwnerBatch F assign e n hn) iLocal :
            Fin (matchingFiber assign e).card) = iFiber := by
      exact selectedEquiv_selectedIndex _ _ _
    have hbranch : onlineOwnerBatchBranch F assign e n hn iLocal = j := by
      simp only [onlineOwnerBatchBranch, hindex, e, iFiber,
        selectedEquiv_assignmentIndex]
    have hcoordinate :
        (⟨onlineOwnerBatchBranch F assign e n hn iLocal,
            onlineOwnerBatchVertex F assign e n hn iLocal aLocal⟩ :
          Σ j, Fin (F.branches.size j)) = ⟨j, a⟩ := by
      apply Sigma.ext hbranch
      exact (Fin.heq_ext_iff (congrArg F.branches.size hbranch)).2 rfl
    have hcolor :
        ((onlineOwnerBatchForest F assign e n hn).isTree iLocal
          |>.coloringTwoOfVert
            ((onlineOwnerBatchForest F assign e n hn).root iLocal) aLocal) =
          ((onlineFiberForest F assign e).isTree iFiber
            |>.coloringTwoOfVert
              ((onlineFiberForest F assign e).root iFiber) aFiber) := by
      exact selectedVertex_coloring (onlineFiberForest F assign e)
        (onlineOwnerBatch F assign e n hn) iFiber hiBatch aFiber
    have horient' :
        (next.edgeState e).orient iFiber =
          Downer.orientation (onlineOwnerBatchForest F assign e n hn) G
            (fun i ↦ extendedRootImage S.state.rootImage n hn z
              (onlineFiberOwner F assign e
                (Erdos547b.ZhaoClaim616SourceBridge.OrderedBranchForest.selectedEquiv
                  (onlineOwnerBatch F assign e n hn) i)))
            (whole e)
            (fun c ↦ endpoint e c \
              (reparentedEdgeState F G assign endpoint rootCandidate n hn
                S.state z e).used c)
            (rho e) (density e) iLocal := by
      rw [← hindex]
      simpa only [next, Dplain, Downer, Dlocal,
        PlannedOnlineOwnerSuccessorData.toOnline] using horient
    dsimp only
    rw [horient', ← hcolor]
    rw [onlineOwnerBatchCoordinateAllowed, hcoordinate] at hplan
    exact hplan

/-- Extend one cut-aware synchronized owner while preserving both the
deleted cut-edge adjacencies and the coordinate-side plan. -/
noncomputable def extendPlannedCutOnlineOwnerPrefixState
    {V : Type*} [Fintype V] [DecidableEq V]
    {T : SimpleGraph V} [DecidableRel T.Adj]
    {globalRoot : V} {small : ℕ}
    (P : Erdos547b.TreePartition.ZhaoForestPartition T globalRoot small)
    {B : Type v} [Fintype B] [DecidableEq B]
    (G : SimpleGraph B) [DecidableRel G.Adj]
    {k : ℕ}
    (assign : Fin (Fintype.card (Erdos547b.ZhaoClaim68BranchAdapter.ChildKey
      P.orderedForest)) → Fin k)
    (whole endpoint : Fin k → Fin 2 → Finset B)
    (hendpoint : ∀ e c, endpoint e c ⊆ whole e c)
    (hwholeDisjoint : ∀ e, Disjoint (whole e 0) (whole e 1))
    (rho density : Fin k → ℝ)
    (rootCandidate : Fin P.numParts → Finset B)
    (rootAllowed : Fin (Fintype.card
      (Erdos547b.ZhaoClaim68BranchAdapter.ChildKey P.orderedForest)) →
      Finset (Fin 2))
    (coordinateAllowed :
      (Σ j : Fin (Fintype.card
        (Erdos547b.ZhaoClaim68BranchAdapter.ChildKey P.orderedForest)),
        Fin ((Erdos547b.ZhaoClaim617BranchCount.branchForest P).branches.size j)) →
        Finset (Fin 2))
    (n : ℕ) (hn : n < P.numParts)
    (S : PlannedCutOnlineOwnerPrefixState P G assign endpoint rootCandidate
      coordinateAllowed n)
    (z : B) (hzmem : z ∈ rootCandidate ⟨n, hn⟩)
    (hzfresh : ∀ q, q.val < n → z ≠ S.state.state.rootImage q)
    (hzparent : ∀ hzero : n ≠ 0,
      G.Adj
        (onlineCutParentImage P G assign endpoint rootCandidate n S.state.state
          ⟨n, hn⟩ (by simpa using hzero) le_rfl)
        z)
    (D : PlannedOnlineOwnerSuccessorData
      (Erdos547b.ZhaoClaim617BranchCount.branchForest P) G assign whole endpoint
      rho density rootCandidate rootAllowed coordinateAllowed n hn S.state.state
      z) :
    PlannedCutOnlineOwnerPrefixState P G assign endpoint rootCandidate
      coordinateAllowed (n + 1) := by
  classical
  let Splain : PlannedOnlineOwnerPrefixState
      (Erdos547b.ZhaoClaim617BranchCount.branchForest P) G assign endpoint
      rootCandidate coordinateAllowed n :=
    { state := S.state.state
      coordinate_side_mem := by
        intro j hj a
        simpa only [onlineCoordinateSide] using
          S.coordinate_side_mem j hj a }
  let Dplain := D.toOnline
    (Erdos547b.ZhaoClaim617BranchCount.branchForest P) G assign whole endpoint
    rho density rootCandidate rootAllowed coordinateAllowed n hn S.state.state z
  let cutNext := extendCutOnlineOwnerPrefixState P G assign whole endpoint
    hendpoint hwholeDisjoint rho density rootCandidate n hn S.state z hzmem
    hzfresh hzparent Dplain
  let plannedNext := extendPlannedOnlineOwnerPrefixState
    (Erdos547b.ZhaoClaim617BranchCount.branchForest P) G assign whole endpoint
    hendpoint hwholeDisjoint rho density rootCandidate rootAllowed
    coordinateAllowed n hn Splain z hzmem hzfresh D
  refine { state := cutNext, coordinate_side_mem := ?_ }
  intro j hj a
  have hmem := plannedNext.coordinate_side_mem j hj a
  simpa only [onlineCoordinateSide, cutNext, plannedNext, Splain, Dplain,
    extendCutOnlineOwnerPrefixState, extendPlannedOnlineOwnerPrefixState] using
      hmem

/-- Empty cut-aware synchronized state with the side-plan invariant. -/
noncomputable def emptyPlannedCutOnlineOwnerPrefixState
    {V : Type*} [Fintype V] [DecidableEq V]
    {T : SimpleGraph V} [DecidableRel T.Adj]
    {globalRoot : V} {small : ℕ}
    (P : Erdos547b.TreePartition.ZhaoForestPartition T globalRoot small)
    {B : Type v} [Fintype B] [DecidableEq B]
    (G : SimpleGraph B) [DecidableRel G.Adj]
    {k : ℕ}
    (assign : Fin (Fintype.card (Erdos547b.ZhaoClaim68BranchAdapter.ChildKey
      P.orderedForest)) → Fin k)
    (endpoint : Fin k → Fin 2 → Finset B)
    (rootCandidate : Fin P.numParts → Finset B)
    (coordinateAllowed :
      (Σ j : Fin (Fintype.card
        (Erdos547b.ZhaoClaim68BranchAdapter.ChildKey P.orderedForest)),
        Fin ((Erdos547b.ZhaoClaim617BranchCount.branchForest P).branches.size j)) →
        Finset (Fin 2))
    (initialRootImage : Fin P.numParts → B) :
    PlannedCutOnlineOwnerPrefixState P G assign endpoint rootCandidate
      coordinateAllowed 0 where
  state := emptyCutOnlineOwnerPrefixState P G assign endpoint rootCandidate
    initialRootImage
  coordinate_side_mem := by omega

/-- Execute the synchronized owner recursion with side-aware cleaning.  The
stored planned-side invariant supplies every dynamic cut-parent-side fact, so
the only recursive callback is the plan-certified local realization datum. -/
theorem exists_plannedCutOnlineOwnerPrefixState_sideCleaning
    {V : Type*} [Fintype V] [DecidableEq V]
    {T : SimpleGraph V} [DecidableRel T.Adj]
    {globalRoot : V} {small : ℕ}
    (P : Erdos547b.TreePartition.ZhaoForestPartition T globalRoot small)
    {B : Type v} [Fintype B] [DecidableEq B]
    (G : SimpleGraph B) [DecidableRel G.Adj]
    {k : ℕ}
    (assign : Fin (Fintype.card (Erdos547b.ZhaoClaim68BranchAdapter.ChildKey
      P.orderedForest)) → Fin k)
    (whole endpoint : Fin k → Fin 2 → Finset B)
    (hendpoint : ∀ e c, endpoint e c ⊆ whole e c)
    (hwholeDisjoint : ∀ e, Disjoint (whole e 0) (whole e 1))
    (rho density : Fin k → ℝ)
    (rootCandidate : Fin P.numParts → Finset B)
    (allowed :
      (Σ j : Fin (Fintype.card
        (Erdos547b.ZhaoClaim68BranchAdapter.ChildKey P.orderedForest)),
        Fin ((Erdos547b.ZhaoClaim617BranchCount.branchForest P).branches.size j)) →
        Finset (Fin 2))
    (rootAllowed : Fin (Fintype.card
      (Erdos547b.ZhaoClaim68BranchAdapter.ChildKey P.orderedForest)) →
      Finset (Fin 2))
    (initialRootImage : Fin P.numParts → B)
    (hfirst : P.numParts ≤ #(rootCandidate ⟨0, P.numParts_pos⟩))
    (hrootLink : ∀ q (hq : q.val ≠ 0)
      (_hroot : P.parent q hq = P.roots (P.parentPart q hq))
      x, x ∈ rootCandidate (P.parentPart q hq) →
      P.numParts ≤ #((rootCandidate q).filter (G.Adj x)))
    (hsuccessor : ∀ n (hn : n < P.numParts)
      (S : PlannedCutOnlineOwnerPrefixState P G assign
        (onlineSideCleanEndpoint P G rootCandidate assign endpoint allowed)
        rootCandidate allowed n)
      z,
      z ∈ onlineRootEligible P G assign
        (onlineSideCleanEndpoint P G rootCandidate assign endpoint allowed)
        rootCandidate n hn S.state →
      (∀ q, q.val < n → z ≠ S.state.state.rootImage q) →
      PlannedOnlineOwnerSuccessorData
        (Erdos547b.ZhaoClaim617BranchCount.branchForest P) G assign whole
        (onlineSideCleanEndpoint P G rootCandidate assign endpoint allowed)
        rho density rootCandidate rootAllowed allowed n hn S.state.state z) :
    Nonempty (PlannedCutOnlineOwnerPrefixState P G assign
      (onlineSideCleanEndpoint P G rootCandidate assign endpoint allowed)
      rootCandidate allowed P.numParts) := by
  classical
  let clean := onlineSideCleanEndpoint P G rootCandidate assign endpoint allowed
  have hcleanEndpoint : ∀ e c, clean e c ⊆ whole e c := by
    intro e c
    exact (onlineSideCleanEndpoint_subset P G rootCandidate assign endpoint
      allowed e c).trans (hendpoint e c)
  have hbuild : ∀ n, n ≤ P.numParts →
      Nonempty (PlannedCutOnlineOwnerPrefixState P G assign clean
        rootCandidate allowed n) := by
    intro n hnr
    induction n with
    | zero =>
        exact ⟨emptyPlannedCutOnlineOwnerPrefixState P G assign clean
          rootCandidate allowed initialRootImage⟩
    | succ n ih =>
        have hn : n < P.numParts := Nat.lt_of_succ_le hnr
        obtain ⟨S⟩ := ih (Nat.le_of_lt hn)
        have heligible : P.numParts ≤
            #(onlineRootEligible P G assign clean rootCandidate n hn S.state) :=
          card_onlineRootEligible_sideCleanEndpoint P G rootCandidate assign
            endpoint allowed hfirst hrootLink n hn S.state
            (fun q hq hnotroot hqn ↦
              S.parentSide P G assign endpoint rootCandidate allowed n q hq
                hnotroot hqn)
        let eligible := onlineRootEligible P G assign clean rootCandidate n hn
          S.state
        have heligibleCard : n < #eligible :=
          lt_of_lt_of_le hn heligible
        have hnotSubset : ¬ eligible ⊆ priorRootImages n hn S.state.state := by
          intro hsubset
          have hcard : #eligible ≤ n :=
            (Finset.card_le_card hsubset).trans
              (card_priorRootImages_le n hn S.state.state)
          exact (Nat.not_lt_of_ge hcard) heligibleCard
        obtain ⟨z, hzeligible, hznot⟩ := Finset.not_subset.mp hnotSubset
        have hzmem : z ∈ rootCandidate ⟨n, hn⟩ :=
          onlineRootEligible_subset P G assign clean rootCandidate n hn S.state
            hzeligible
        have hzfresh : ∀ q, q.val < n → z ≠ S.state.state.rootImage q := by
          intro q hq heq
          apply hznot
          rw [heq]
          exact mem_priorRootImages_of_before n hn S.state.state q hq
        have hzparent : ∀ hzero : n ≠ 0,
            G.Adj
              (onlineCutParentImage P G assign clean rootCandidate n
                S.state.state ⟨n, hn⟩ (by simpa using hzero) le_rfl)
              z := by
          intro hzero
          exact onlineRootEligible_parent_adj P G assign clean rootCandidate n
            hn S.state z hzeligible hzero
        exact ⟨extendPlannedCutOnlineOwnerPrefixState P G assign whole clean
          hcleanEndpoint hwholeDisjoint rho density rootCandidate rootAllowed
          allowed n hn S z hzmem hzfresh hzparent
          (hsuccessor n hn S z hzeligible hzfresh)⟩
  exact hbuild P.numParts le_rfl

end Erdos547b.ZhaoLemma58GlobalPlannedOwnerSuccessor

#print axioms Erdos547b.ZhaoLemma58GlobalPlannedOwnerSuccessor.onlineOwnerBatchBranch_owner
#print axioms Erdos547b.ZhaoLemma58GlobalPlannedOwnerSuccessor.onlineOwnerBatchBranch_assign
#print axioms Erdos547b.ZhaoLemma58GlobalPlannedOwnerSuccessor.exists_plannedCutOnlineOwnerPrefixState_sideCleaning
