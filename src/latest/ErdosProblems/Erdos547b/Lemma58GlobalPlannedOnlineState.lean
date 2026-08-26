/- leanprover/lean4:v4.33.0 -/
import ErdosProblems.Erdos547b.Lemma58OnlineParentSideCleaning

/-!
# Planned-side invariant for the synchronized online state

The state remembers that every already embedded source coordinate lies on a
side allowed by the fixed/adaptive target plan.  This is precisely the
invariant needed to turn side-aware parent cleaning into the dynamic root
eligibility bound.
-/

open scoped SimpleGraph
noncomputable section

namespace Erdos547b.ZhaoLemma58GlobalPlannedOnlineState

open Finset Fintype SimpleGraph
open Erdos547b.TreePartition
open Erdos547b.ZhaoClaim68BranchAdapter
open Erdos547b.ZhaoClaim617BranchCount
open Erdos547b.ZhaoClaim616SourceBridge
open Erdos547b.ZhaoClaim616SourceBridge.OrderedBranchForest
open Erdos547b.ZhaoLemma58MatchingAssembly
open Erdos547b.ZhaoLemma58DynamicBatchAppend
open Erdos547b.ZhaoLemma58GlobalOwnerOnlineState
open Erdos547b.ZhaoLemma58GlobalOwnerBranchImage
open Erdos547b.ZhaoLemma58GlobalCutOnline
open Erdos547b.ZhaoLemma58OnlineParentSideCleaning

universe u v

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {T : SimpleGraph V} [DecidableRel T.Adj]
variable {globalRoot : V} {small : ℕ}

/-- Actual endpoint side of one global branch coordinate in a synchronized
partial state. -/
def onlineCoordinateSide
    {B : Type v} [Fintype B] [DecidableEq B]
    (P : ZhaoForestPartition T globalRoot small)
    (G : SimpleGraph B) [DecidableRel G.Adj]
    {k : ℕ}
    (assign : Fin (Fintype.card (ChildKey P.orderedForest)) → Fin k)
    (endpoint : Fin k → Fin 2 → Finset B)
    (rootCandidate : Fin P.numParts → Finset B)
    (n : ℕ)
    (S : OnlineOwnerPrefixState (branchForest P) G assign endpoint
      rootCandidate n)
    (j : Fin (Fintype.card (ChildKey P.orderedForest)))
    (a : Fin ((branchForest P).branches.size j)) : Fin 2 :=
  let i := assignmentIndex assign j
  (S.edgeState (assign j)).orient i
    ((onlineFiberForest (branchForest P) assign (assign j)).isTree i
      |>.coloringTwoOfVert
        ((onlineFiberForest (branchForest P) assign (assign j)).root i)
        (assignmentVertex (branchForest P) assign j a))

/-- Generic synchronized owner state whose processed coordinates respect a
side plan. -/
structure PlannedOnlineOwnerPrefixState
    {r b k : ℕ} {B : Type v} [Fintype B] [DecidableEq B]
    (F : Erdos547b.ZhaoLemma59Part2Full.OrderedBranchForest r b)
    (G : SimpleGraph B)
    (assign : Fin b → Fin k)
    (endpoint : Fin k → Fin 2 → Finset B)
    (rootCandidate : Fin r → Finset B)
    (allowed : (Σ j, Fin (F.branches.size j)) → Finset (Fin 2))
    (n : ℕ) where
  state : OnlineOwnerPrefixState F G assign endpoint rootCandidate n
  coordinate_side_mem : ∀ j, (F.owner j).val < n → ∀ a,
    let i := assignmentIndex assign j
    (state.edgeState (assign j)).orient i
        ((onlineFiberForest F assign (assign j)).isTree i
          |>.coloringTwoOfVert
            ((onlineFiberForest F assign (assign j)).root i)
            (assignmentVertex F assign j a)) ∈ allowed ⟨j, a⟩

/-- A cut-aware synchronized state whose processed coordinates all respect
the pre-orientation side plan. -/
structure PlannedCutOnlineOwnerPrefixState
    {B : Type v} [Fintype B] [DecidableEq B]
    (P : ZhaoForestPartition T globalRoot small)
    (G : SimpleGraph B) [DecidableRel G.Adj]
    {k : ℕ}
    (assign : Fin (Fintype.card (ChildKey P.orderedForest)) → Fin k)
    (endpoint : Fin k → Fin 2 → Finset B)
    (rootCandidate : Fin P.numParts → Finset B)
    (allowed : (Σ j : Fin (Fintype.card (ChildKey P.orderedForest)),
      Fin ((branchForest P).branches.size j)) → Finset (Fin 2))
    (n : ℕ) where
  state : CutOnlineOwnerPrefixState P G assign endpoint rootCandidate n
  coordinate_side_mem : ∀ j,
    ((branchForest P).owner j).val < n →
    ∀ a, onlineCoordinateSide P G assign endpoint rootCandidate n state.state
      j a ∈ allowed ⟨j, a⟩

/-- The planned-side invariant supplies the exact parent-side callback used
by `card_onlineRootEligible_sideCleanEndpoint`. -/
theorem PlannedCutOnlineOwnerPrefixState.parentSide
    {B : Type v} [Fintype B] [DecidableEq B]
    (P : ZhaoForestPartition T globalRoot small)
    (G : SimpleGraph B) [DecidableRel G.Adj]
    {k : ℕ}
    (assign : Fin (Fintype.card (ChildKey P.orderedForest)) → Fin k)
    (raw : Fin k → Fin 2 → Finset B)
    (rootCandidate : Fin P.numParts → Finset B)
    (allowed : (Σ j : Fin (Fintype.card (ChildKey P.orderedForest)),
      Fin ((branchForest P).branches.size j)) → Finset (Fin 2))
    (n : ℕ)
    (S : PlannedCutOnlineOwnerPrefixState P G assign
      (onlineSideCleanEndpoint P G rootCandidate assign raw allowed)
      rootCandidate allowed n)
    (q : Fin P.numParts) (hq : q.val ≠ 0)
    (hnotroot : P.parent q hq ≠ P.roots (P.parentPart q hq))
    (hqn : q.val ≤ n) :
    let z := cutParentBranchCoordinate P q hq hnotroot
    let hj : ((branchForest P).owner z.1).val < n := by
      rw [cutParentBranchCoordinate_owner P q hq hnotroot]
      exact lt_of_lt_of_le (P.parent_earlier q hq) hqn
    ∃ c,
      OnlineOwnerPrefixState.branchCopy (branchForest P) G assign
          (onlineSideCleanEndpoint P G rootCandidate assign raw allowed)
          rootCandidate n S.state.state z.1 hj z.2 ∈
        onlineSideCleanEndpoint P G rootCandidate assign raw allowed
          (assign z.1) c ∧
      c ∈ allowed z := by
  classical
  let z := cutParentBranchCoordinate P q hq hnotroot
  have hj : ((branchForest P).owner z.1).val < n := by
    rw [cutParentBranchCoordinate_owner P q hq hnotroot]
    exact lt_of_lt_of_le (P.parent_earlier q hq) hqn
  let i := assignmentIndex assign z.1
  have hi : i ∈ ownerPrefix Finset.univ
      (onlineFiberOwner (branchForest P) assign (assign z.1)) n :=
    (assignmentIndex_mem_ownerPrefix (branchForest P) assign z.1 n).2 hj
  let c := onlineCoordinateSide P G assign
    (onlineSideCleanEndpoint P G rootCandidate assign raw allowed)
    rootCandidate n S.state.state z.1 z.2
  refine ⟨c, ?_, ?_⟩
  · have hm := (S.state.state.edgeState (assign z.1)).state.map_side i hi
      (assignmentVertex (branchForest P) assign z.1 z.2)
    simpa only [OnlineOwnerPrefixState.branchCopy, onlineCoordinateSide, i, c]
      using hm
  · exact S.coordinate_side_mem z.1 hj z.2

end Erdos547b.ZhaoLemma58GlobalPlannedOnlineState

#print axioms Erdos547b.ZhaoLemma58GlobalPlannedOnlineState.PlannedCutOnlineOwnerPrefixState.parentSide
