/- leanprover/lean4:v4.33.0 -/
import ErdosProblems.Erdos547b.Lemma58GlobalOwnerOnlineState
import ErdosProblems.Erdos547b.Lemma58OwnerForbiddenCertificate

/-!
# Reading stable branch images from the synchronized owner state

The global online construction stores one partial embedding per matching
edge.  This file gives the canonical image of an original branch vertex and
proves that extending the owner prefix does not change images belonging to
an earlier owner.
-/

open scoped SimpleGraph
noncomputable section

namespace Erdos547b.ZhaoLemma58GlobalOwnerBranchImage

open Finset Fintype SimpleGraph
open Erdos547b.ZhaoLemma59Part2Full
open Erdos547b.ZhaoClaim616SourceBridge
open Erdos547b.ZhaoClaim616SourceBridge.OrderedBranchForest
open Erdos547b.ZhaoLemma58MatchingAssembly
open Erdos547b.ZhaoLemma58DynamicBatchAppend
open Erdos547b.ZhaoLemma58ChosenOwnerBatches
open Erdos547b.ZhaoLemma58OwnerForbiddenCertificate
open Erdos547b.ZhaoLemma58GlobalOwnerOnlineState
open Erdos547b.ZhaoLemma58OnlineOwnerReparent

universe v

@[simp] theorem onlineFiberOwner_assignmentIndex
    {r b k : ℕ} (F : OrderedBranchForest r b)
    (assign : Fin b → Fin k) (j : Fin b) :
    onlineFiberOwner F assign (assign j) (assignmentIndex assign j) =
      F.owner j := by
  simp only [onlineFiberOwner, selectedEquiv_assignmentIndex]

theorem assignmentIndex_mem_ownerPrefix
    {r b k : ℕ} (F : OrderedBranchForest r b)
    (assign : Fin b → Fin k) (j : Fin b) (n : ℕ) :
    assignmentIndex assign j ∈
        ownerPrefix Finset.univ
          (onlineFiberOwner F assign (assign j)) n ↔
      (F.owner j).val < n := by
  simp only [ownerPrefix, Finset.mem_filter, Finset.mem_univ, true_and,
    onlineFiberOwner_assignmentIndex]

/-- Image of one original branch vertex already present in the owner prefix. -/
noncomputable def OnlineOwnerPrefixState.branchCopy
    {r b k : ℕ} {B : Type v} [Fintype B] [DecidableEq B]
    (F : OrderedBranchForest r b) (G : SimpleGraph B)
    (assign : Fin b → Fin k) (endpoint : Fin k → Fin 2 → Finset B)
    (rootCandidate : Fin r → Finset B) (n : ℕ)
    (S : OnlineOwnerPrefixState F G assign endpoint rootCandidate n)
    (j : Fin b) (hj : (F.owner j).val < n)
    (a : Fin (F.branches.size j)) : B :=
  (S.edgeState (assign j)).state.forestCopy.componentCopy
    (assignmentIndex assign j)
    ((assignmentIndex_mem_ownerPrefix F assign j n).2 hj)
    (assignmentVertex F assign j a)

/-- Reparenting the old edge state changes no branch vertex image. -/
theorem reparentedEdgeState_componentCopy
    {r b k : ℕ} {B : Type v} [Fintype B] [DecidableEq B]
    (F : OrderedBranchForest r b) (G : SimpleGraph B)
    (assign : Fin b → Fin k) (endpoint : Fin k → Fin 2 → Finset B)
    (rootCandidate : Fin r → Finset B) (n : ℕ) (hn : n < r)
    (S : OnlineOwnerPrefixState F G assign endpoint rootCandidate n)
    (z : B) (j : Fin b) (hj : (F.owner j).val < n)
    (a : Fin (F.branches.size j)) :
    (reparentedEdgeState F G assign endpoint rootCandidate n hn S z
      (assign j)).state.forestCopy.componentCopy
        (assignmentIndex assign j)
        ((assignmentIndex_mem_ownerPrefix F assign j n).2 hj)
        (assignmentVertex F assign j a) =
      OnlineOwnerPrefixState.branchCopy F G assign endpoint rootCandidate n
        S j hj a := by
  rfl

/-- Extending the synchronized state keeps every already embedded branch
vertex at exactly the same host vertex. -/
theorem branchCopy_extend_before
    {r b k : ℕ} {B : Type v} [Fintype B] [DecidableEq B]
    (F : OrderedBranchForest r b) (G : SimpleGraph B) [DecidableRel G.Adj]
    (assign : Fin b → Fin k)
    (whole endpoint : Fin k → Fin 2 → Finset B)
    (hendpoint : ∀ e c, endpoint e c ⊆ whole e c)
    (hwholeDisjoint : ∀ e, Disjoint (whole e 0) (whole e 1))
    (rho density : Fin k → ℝ)
    (rootCandidate : Fin r → Finset B) (n : ℕ) (hn : n < r)
    (S : OnlineOwnerPrefixState F G assign endpoint rootCandidate n)
    (z : B) (hzmem : z ∈ rootCandidate ⟨n, hn⟩)
    (hzfresh : ∀ q, q.val < n → z ≠ S.rootImage q)
    (D : OnlineOwnerSuccessorData F G assign whole endpoint rho density
      rootCandidate n hn S z)
    (j : Fin b) (hj : (F.owner j).val < n)
    (a : Fin (F.branches.size j)) :
    OnlineOwnerPrefixState.branchCopy F G assign endpoint rootCandidate
        (n + 1)
        (extendOnlineOwnerPrefixState F G assign whole endpoint hendpoint
          hwholeDisjoint rho density rootCandidate n hn S z hzmem hzfresh D)
        j (by omega) a =
      OnlineOwnerPrefixState.branchCopy F G assign endpoint rootCandidate n
        S j hj a := by
  classical
  have hmem : assignmentIndex assign j ∈
      ownerPrefix Finset.univ
        (onlineFiberOwner F assign (assign j)) n :=
    (assignmentIndex_mem_ownerPrefix F assign j n).2 hj
  unfold OnlineOwnerPrefixState.branchCopy
  unfold extendOnlineOwnerPrefixState
  dsimp only
  erw [castChosenSelected_componentCopy]
  erw [appendChosen_componentCopy_left]
  rfl
  exact Finset.mem_union_left _ hmem

end Erdos547b.ZhaoLemma58GlobalOwnerBranchImage

#print axioms Erdos547b.ZhaoLemma58GlobalOwnerBranchImage.reparentedEdgeState_componentCopy
#print axioms Erdos547b.ZhaoLemma58GlobalOwnerBranchImage.branchCopy_extend_before
