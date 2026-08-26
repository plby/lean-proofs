/- leanprover/lean4:v4.33.0 -/
import ErdosProblems.Erdos547b.Lemma58GlobalOwnerOnlineState

/-!
# Orientation transport through chosen-state append operations

Small projection lemmas for the deterministic orientation stored by the
synchronized owner recursion.
-/

open scoped SimpleGraph
noncomputable section

namespace Erdos547b.ZhaoLemma58ChosenOrientationTransport

open Finset Fintype SimpleGraph
open Erdos547b.RegularPair
open Erdos547b.ZhaoClaim616SourceBridge.OrderedBranchForest
open Erdos547b.ZhaoLemma58GroupedSmallForest
open Erdos547b.ZhaoLemma58DynamicBatchAppend
open Erdos547b.ZhaoLemma58ChosenOwnerBatches
open Erdos547b.ZhaoLemma58OnlineOwnerReparent
open Erdos547b.ZhaoLemma58MatchingAssembly
open Erdos547b.ZhaoLemma58GlobalOwnerOnlineState

universe v

@[simp] theorem castChosenSelected_orient
    {b : ℕ} {B : Type v} [Fintype B] [DecidableEq B]
    (F : OrderedRootedForest b) (G : SimpleGraph B)
    (externalParent : Fin b → B) (available : Fin 2 → Finset B)
    {s t : Finset (Fin b)} (hst : s = t)
    (E : ChosenPartialDynamicEmbedding F G externalParent available s)
    (i : Fin b) :
    (castChosenSelected F G externalParent available hst E).orient i =
      E.orient i := by
  subst t
  rfl

@[simp] theorem chosenReparent_orient
    {b : ℕ} {B : Type v} [Fintype B] [DecidableEq B]
    (F : OrderedRootedForest b) (G : SimpleGraph B)
    (externalParent externalParent' : Fin b → B)
    (available : Fin 2 → Finset B) (selected : Finset (Fin b))
    (E : ChosenPartialDynamicEmbedding
      F G externalParent available selected)
    (hagrees : ∀ i, i ∈ selected →
      externalParent' i = externalParent i) (j : Fin b) :
    (chosenReparent F G externalParent externalParent' available selected E
      hagrees).orient j = E.orient j := rfl

@[simp] theorem appendChosen_orient_left
    {b : ℕ} {B : Type v} [Fintype B] [DecidableEq B]
    (F : OrderedRootedForest b) (G : SimpleGraph B)
    (externalParent : Fin b → B)
    (whole available : Fin 2 → Finset B)
    (havailable : ∀ c, available c ⊆ whole c)
    (hwholeDisjoint : Disjoint (whole 0) (whole 1))
    (s t : Finset (Fin b)) (hst : Disjoint s t)
    (E₁ : ChosenPartialDynamicEmbedding F G externalParent available s)
    (E₂ : ChosenPartialDynamicEmbedding F G externalParent
      (fun c ↦ available c \ E₁.used c) t)
    (i : Fin b) (hi : i ∈ s) :
    (appendChosen F G externalParent whole available havailable
      hwholeDisjoint s t hst E₁ E₂).orient i = E₁.orient i := by
  simp [appendChosen, pasteOrient, hi]

@[simp] theorem appendChosen_orient_right
    {b : ℕ} {B : Type v} [Fintype B] [DecidableEq B]
    (F : OrderedRootedForest b) (G : SimpleGraph B)
    (externalParent : Fin b → B)
    (whole available : Fin 2 → Finset B)
    (havailable : ∀ c, available c ⊆ whole c)
    (hwholeDisjoint : Disjoint (whole 0) (whole 1))
    (s t : Finset (Fin b)) (hst : Disjoint s t)
    (E₁ : ChosenPartialDynamicEmbedding F G externalParent available s)
    (E₂ : ChosenPartialDynamicEmbedding F G externalParent
      (fun c ↦ available c \ E₁.used c) t)
    (i : Fin b) (hi : i ∈ t) :
    (appendChosen F G externalParent whole available havailable
      hwholeDisjoint s t hst E₁ E₂).orient i = E₂.orient i := by
  have his : i ∉ s := by
    intro his
    exact Finset.disjoint_left.mp hst his hi
  simp [appendChosen, pasteOrient, his]

@[simp] theorem chosenPartialOfSelectedForest_orient
    {b : ℕ} {B : Type v} [Fintype B] [DecidableEq B]
    (F : OrderedRootedForest b) (G : SimpleGraph B)
    (externalParent : Fin b → B)
    (available : Fin 2 → Finset B) (selected : Finset (Fin b))
    (localOrient : Fin selected.card → Fin 2 ≃ Fin 2)
    (E : DynamicAttachedForestEmbedding (selectedForest F selected) G
      (fun k ↦ externalParent
        (Erdos547b.ZhaoClaim616SourceBridge.OrderedBranchForest.selectedEquiv
          selected k)) localOrient available)
    (i : Fin selected.card) :
    (chosenPartialOfSelectedForest F G externalParent available selected
      localOrient E).orient
        (Erdos547b.ZhaoClaim616SourceBridge.OrderedBranchForest.selectedEquiv
          selected i) = localOrient i := by
  simp [chosenPartialOfSelectedForest]

/-- Extending one synchronized owner preserves every earlier edge-fiber
orientation value. -/
theorem extendOnlineOwnerPrefixState_orient_before
    {r b k : ℕ} {B : Type v} [Fintype B] [DecidableEq B]
    (F : Erdos547b.ZhaoLemma59Part2Full.OrderedBranchForest r b)
    (G : SimpleGraph B) [DecidableRel G.Adj]
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
    (e : Fin k) (i : Fin (matchingFiber assign e).card)
    (hi : i ∈ ownerPrefix Finset.univ (onlineFiberOwner F assign e) n) :
    ((extendOnlineOwnerPrefixState F G assign whole endpoint hendpoint
      hwholeDisjoint rho density rootCandidate n hn S z hzmem hzfresh D).edgeState
        e).orient i = (S.edgeState e).orient i := by
  classical
  simp [extendOnlineOwnerPrefixState, hi, reparentedEdgeState]
  rfl

/-- On the newly added owner batch, the extended state stores exactly the
deterministic orientation of its local source datum. -/
theorem extendOnlineOwnerPrefixState_orient_current
    {r b k : ℕ} {B : Type v} [Fintype B] [DecidableEq B]
    (F : Erdos547b.ZhaoLemma59Part2Full.OrderedBranchForest r b)
    (G : SimpleGraph B) [DecidableRel G.Adj]
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
    (e : Fin k)
    (i : Fin (ownerBatch Finset.univ
      (onlineFiberOwner F assign e) ⟨n, hn⟩).card) :
    ((extendOnlineOwnerPrefixState F G assign whole endpoint hendpoint
      hwholeDisjoint rho density rootCandidate n hn S z hzmem hzfresh D).edgeState
        e).orient
        (Erdos547b.ZhaoClaim616SourceBridge.OrderedBranchForest.selectedEquiv
          (ownerBatch Finset.univ (onlineFiberOwner F assign e) ⟨n, hn⟩) i) =
      (D e).orientation
        (selectedForest (onlineFiberForest F assign e)
          (ownerBatch Finset.univ (onlineFiberOwner F assign e) ⟨n, hn⟩)) G
        (fun j ↦ extendedRootImage S.rootImage n hn z
          (onlineFiberOwner F assign e
            (Erdos547b.ZhaoClaim616SourceBridge.OrderedBranchForest.selectedEquiv
              (ownerBatch Finset.univ (onlineFiberOwner F assign e)
                ⟨n, hn⟩) j)))
        (whole e)
        (fun c ↦ endpoint e c \
          (reparentedEdgeState F G assign endpoint rootCandidate n hn S z e).used
            c)
        (rho e) (density e) i := by
  classical
  simp [extendOnlineOwnerPrefixState]

end Erdos547b.ZhaoLemma58ChosenOrientationTransport
