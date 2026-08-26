/- leanprover/lean4:v4.33.0 -/
import ErdosProblems.Erdos547b.Lemma58OnlineOwnerReparent
import ErdosProblems.Erdos547b.Lemma58OwnerLocalStep
import ErdosProblems.Erdos547b.Lemma58ChosenMatchingAssembly

/-!
# Global owner-prefix state for the online Lemma 5.8 construction

The existing owner recursion processes every owner separately inside each
matching edge.  Reconstructing the deleted edges of a Zhao forest partition
requires the dual synchronization: owner `n` must be completed on *every*
matching edge before root `n+1` is chosen.  This file defines that synchronized
prefix state and its source-data-only successor operation.

No graph copy or embedding is accepted as a public successor premise.  Each
new edge batch is built from `OwnerLocalStepData`, whose `realize` theorem is
the checked threshold/Appendix constructor.
-/

open scoped SimpleGraph
noncomputable section

namespace Erdos547b.ZhaoLemma58GlobalOwnerOnlineState

open Finset Fintype SimpleGraph
open Erdos547b.RegularPair
open Erdos547b.ZhaoLemma59Part2Full
open Erdos547b.ZhaoClaim616SourceBridge
open Erdos547b.ZhaoClaim616SourceBridge.OrderedBranchForest
open Erdos547b.ZhaoLemma58GroupedSmallForest
open Erdos547b.ZhaoLemma58MatchingAssembly
open Erdos547b.ZhaoLemma58DynamicBatchAppend
open Erdos547b.ZhaoLemma58ChosenOwnerBatches
open Erdos547b.ZhaoLemma58ChosenMatchingAssembly
open Erdos547b.ZhaoLemma58OwnerLocalStep
open Erdos547b.ZhaoLemma58OnlineOwnerReparent

universe v

/-- The literal ordered forest on one matching-edge fiber. -/
abbrev onlineFiberForest {r b k : ℕ}
    (F : OrderedBranchForest r b) (assign : Fin b → Fin k) (e : Fin k) :
    OrderedRootedForest (matchingFiber assign e).card :=
  (OrderedBranchForest.restrict F (matchingFiber assign e)).branches

/-- Owner of one component in a matching-edge fiber. -/
abbrev onlineFiberOwner {r b k : ℕ}
    (F : OrderedBranchForest r b) (assign : Fin b → Fin k) (e : Fin k) :
    Fin (matchingFiber assign e).card → Fin r :=
  fun i ↦ F.owner
    (OrderedBranchForest.selectedEquiv (matchingFiber assign e) i)

/-- All component roots chosen before `n`, together with the exact dynamic
branch state already constructed on every matching edge.  Values of
`rootImage` at owners `≥ n` are placeholders and may be updated later. -/
structure OnlineOwnerPrefixState
    {r b k : ℕ} {B : Type v} [Fintype B] [DecidableEq B]
    (F : OrderedBranchForest r b) (G : SimpleGraph B)
    (assign : Fin b → Fin k) (endpoint : Fin k → Fin 2 → Finset B)
    (rootCandidate : Fin r → Finset B) (n : ℕ) where
  rootImage : Fin r → B
  root_mem : ∀ q, q.val < n → rootImage q ∈ rootCandidate q
  root_injective : ∀ q q', q.val < n → q'.val < n →
    rootImage q = rootImage q' → q = q'
  edgeState : ∀ e, ChosenPartialDynamicEmbedding
    (onlineFiberForest F assign e) G
    (fun i ↦ rootImage (onlineFiberOwner F assign e i))
    (endpoint e)
    (ownerPrefix Finset.univ (onlineFiberOwner F assign e) n)

/-- The empty synchronized state. -/
noncomputable def emptyOnlineOwnerPrefixState
    {r b k : ℕ} {B : Type v} [Fintype B] [DecidableEq B]
    (F : OrderedBranchForest r b) (G : SimpleGraph B)
    (assign : Fin b → Fin k) (endpoint : Fin k → Fin 2 → Finset B)
    (rootCandidate : Fin r → Finset B) (rootImage : Fin r → B) :
    OnlineOwnerPrefixState F G assign endpoint rootCandidate 0 where
  rootImage := rootImage
  root_mem := by omega
  root_injective := by omega
  edgeState := by
    intro e
    rw [ownerPrefix_zero]
    exact {
      orient := fun _ ↦ Equiv.refl _
      state := emptyPartial (onlineFiberForest F assign e) G
        (fun i ↦ rootImage (onlineFiberOwner F assign e i))
        (fun _ ↦ Equiv.refl _) (endpoint e)
    }

/-- The root map after choosing owner `n`. -/
def extendedRootImage
    {r : ℕ} {B : Type v} [DecidableEq B]
    (rootImage : Fin r → B) (n : ℕ) (hn : n < r) (z : B) : Fin r → B :=
  Function.update rootImage ⟨n, hn⟩ z

@[simp] theorem extendedRootImage_current
    {r : ℕ} {B : Type v} [DecidableEq B]
    (rootImage : Fin r → B) (n : ℕ) (hn : n < r) (z : B) :
    extendedRootImage rootImage n hn z ⟨n, hn⟩ = z := by
  simp [extendedRootImage, Function.update]

theorem extendedRootImage_before
    {r : ℕ} {B : Type v} [DecidableEq B]
    (rootImage : Fin r → B) (n : ℕ) (hn : n < r) (z : B)
    (q : Fin r) (hq : q.val < n) :
    extendedRootImage rootImage n hn z q = rootImage q := by
  apply Function.update_of_ne
  intro h
  have hval : q.val = n := congrArg Fin.val h
  exact (Nat.ne_of_lt hq) hval

/-- Reinterpret the old state on edge `e` after extending the root map at
owner `n`.  The exact used sets remain unchanged by
`used_chosenReparent`. -/
noncomputable def reparentedEdgeState
    {r b k : ℕ} {B : Type v} [Fintype B] [DecidableEq B]
    (F : OrderedBranchForest r b) (G : SimpleGraph B)
    (assign : Fin b → Fin k) (endpoint : Fin k → Fin 2 → Finset B)
    (rootCandidate : Fin r → Finset B) (n : ℕ) (hn : n < r)
    (S : OnlineOwnerPrefixState F G assign endpoint rootCandidate n)
    (z : B) (e : Fin k) :
    ChosenPartialDynamicEmbedding
      (onlineFiberForest F assign e) G
      (fun i ↦ extendedRootImage S.rootImage n hn z
        (onlineFiberOwner F assign e i))
      (endpoint e)
      (ownerPrefix Finset.univ (onlineFiberOwner F assign e) n) :=
  chosenReparent (onlineFiberForest F assign e) G
    (fun i ↦ S.rootImage (onlineFiberOwner F assign e i))
    (fun i ↦ extendedRootImage S.rootImage n hn z
      (onlineFiberOwner F assign e i))
    (endpoint e)
    (ownerPrefix Finset.univ (onlineFiberOwner F assign e) n)
    (S.edgeState e) (by
      intro i hi
      exact update_rootMap_agrees_on_ownerPrefix Finset.univ
        (onlineFiberOwner F assign e) S.rootImage n hn z i hi)

/-- Source/live-host datum for the owner-`n` batch on every matching edge,
after the new root has been fixed and the old state reparented. -/
abbrev OnlineOwnerSuccessorData
    {r b k : ℕ} {B : Type v} [Fintype B] [DecidableEq B]
    (F : OrderedBranchForest r b) (G : SimpleGraph B) [DecidableRel G.Adj]
    (assign : Fin b → Fin k)
    (whole endpoint : Fin k → Fin 2 → Finset B)
    (rho density : Fin k → ℝ)
    (rootCandidate : Fin r → Finset B) (n : ℕ) (hn : n < r)
    (S : OnlineOwnerPrefixState F G assign endpoint rootCandidate n)
    (z : B) :=
  ∀ e, OwnerLocalStepData
    (selectedForest (onlineFiberForest F assign e)
      (ownerBatch Finset.univ (onlineFiberOwner F assign e) ⟨n, hn⟩)) G
    (fun i ↦ extendedRootImage S.rootImage n hn z
      (onlineFiberOwner F assign e
        (OrderedBranchForest.selectedEquiv
          (ownerBatch Finset.univ (onlineFiberOwner F assign e) ⟨n, hn⟩) i)))
    (whole e)
    (fun c ↦ endpoint e c \
      (reparentedEdgeState F G assign endpoint rootCandidate n hn S z e).used c)
    (rho e) (density e)

/-- Transport only the selected-index finset of a chosen partial state. -/
noncomputable def castChosenSelected
    {b : ℕ} {B : Type v} [Fintype B] [DecidableEq B]
    (F : OrderedRootedForest b) (G : SimpleGraph B)
    (externalParent : Fin b → B) (available : Fin 2 → Finset B)
    {s t : Finset (Fin b)} (hst : s = t)
    (E : ChosenPartialDynamicEmbedding F G externalParent available s) :
    ChosenPartialDynamicEmbedding F G externalParent available t :=
  hst ▸ E

theorem castChosenSelected_componentCopy
    {b : ℕ} {B : Type v} [Fintype B] [DecidableEq B]
    (F : OrderedRootedForest b) (G : SimpleGraph B)
    (externalParent : Fin b → B) (available : Fin 2 → Finset B)
    {s t : Finset (Fin b)} (hst : s = t)
    (E : ChosenPartialDynamicEmbedding F G externalParent available s)
    (i : Fin b) (hit : i ∈ t) (his : i ∈ s) (a : Fin (F.size i)) :
    (castChosenSelected F G externalParent available hst E).state.forestCopy.componentCopy
        i hit a = E.state.forestCopy.componentCopy i his a := by
  subst t
  rfl

/-- Add one globally synchronized owner.  The root is required to be fresh
only from earlier roots; root/branch separation is supplied later by the
disjoint root reservoirs.  Every edge batch is constructed internally from
its `OwnerLocalStepData`. -/
noncomputable def extendOnlineOwnerPrefixState
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
      rootCandidate n hn S z) :
    OnlineOwnerPrefixState F G assign endpoint rootCandidate (n + 1) := by
  classical
  let rootImage' := extendedRootImage S.rootImage n hn z
  let old : ∀ e, ChosenPartialDynamicEmbedding
      (onlineFiberForest F assign e) G
      (fun i ↦ rootImage' (onlineFiberOwner F assign e i))
      (endpoint e)
      (ownerPrefix Finset.univ (onlineFiberOwner F assign e) n) :=
    fun e ↦ reparentedEdgeState F G assign endpoint rootCandidate n hn S z e
  let next : ∀ e, ChosenPartialDynamicEmbedding
      (onlineFiberForest F assign e) G
      (fun i ↦ rootImage' (onlineFiberOwner F assign e i))
      (endpoint e)
      (ownerPrefix Finset.univ (onlineFiberOwner F assign e) (n + 1)) := by
    intro e
    let De := D e
    let localOrient := De.orientation
      (selectedForest (onlineFiberForest F assign e)
        (ownerBatch Finset.univ (onlineFiberOwner F assign e) ⟨n, hn⟩)) G
      (fun i ↦ rootImage'
        (onlineFiberOwner F assign e
          (OrderedBranchForest.selectedEquiv
            (ownerBatch Finset.univ (onlineFiberOwner F assign e) ⟨n, hn⟩) i)))
      (whole e)
      (fun c ↦ endpoint e c \ (old e).used c) (rho e) (density e)
    let Elocal := Classical.choice (De.realize_orientation
      (selectedForest (onlineFiberForest F assign e)
        (ownerBatch Finset.univ (onlineFiberOwner F assign e) ⟨n, hn⟩)) G
      (fun i ↦ rootImage'
        (onlineFiberOwner F assign e
          (OrderedBranchForest.selectedEquiv
            (ownerBatch Finset.univ (onlineFiberOwner F assign e) ⟨n, hn⟩) i)))
      (whole e)
      (fun c ↦ endpoint e c \ (old e).used c) (rho e) (density e))
    let batch := chosenPartialOfSelectedForest
      (onlineFiberForest F assign e) G
      (fun i ↦ rootImage' (onlineFiberOwner F assign e i))
      (fun c ↦ endpoint e c \ (old e).used c)
      (ownerBatch Finset.univ (onlineFiberOwner F assign e) ⟨n, hn⟩)
      localOrient Elocal
    let joined := appendChosen (onlineFiberForest F assign e) G
      (fun i ↦ rootImage' (onlineFiberOwner F assign e i))
      (whole e) (endpoint e) (hendpoint e) (hwholeDisjoint e)
      (ownerPrefix Finset.univ (onlineFiberOwner F assign e) n)
      (ownerBatch Finset.univ (onlineFiberOwner F assign e) ⟨n, hn⟩)
      (ownerPrefix_disjoint_ownerBatch Finset.univ
        (onlineFiberOwner F assign e) n hn)
      (old e) batch
    exact castChosenSelected (onlineFiberForest F assign e) G
      (fun i ↦ rootImage' (onlineFiberOwner F assign e i)) (endpoint e)
      (ownerPrefix_succ Finset.univ (onlineFiberOwner F assign e) n hn)
      joined
  exact {
    rootImage := rootImage'
    root_mem := by
      intro q hq
      by_cases hqn : q = ⟨n, hn⟩
      · subst q
        change extendedRootImage S.rootImage n hn z ⟨n, hn⟩ ∈
          rootCandidate ⟨n, hn⟩
        rw [extendedRootImage_current]
        exact hzmem
      · have hqold : q.val < n := by
          have hqle : q.val ≤ n := by omega
          exact lt_of_le_of_ne hqle (by
            intro heq
            apply hqn
            exact Fin.ext heq)
        change extendedRootImage S.rootImage n hn z q ∈ rootCandidate q
        rw [extendedRootImage_before S.rootImage n hn z q hqold]
        exact S.root_mem q hqold
    root_injective := by
      intro q q' hq hq' heq
      by_cases hqn : q = ⟨n, hn⟩
      · subst q
        by_cases hq'n : q' = ⟨n, hn⟩
        · exact hq'n.symm
        · have hq'old : q'.val < n := by
            have hq'le : q'.val ≤ n := by omega
            exact lt_of_le_of_ne hq'le (by
              intro hv
              apply hq'n
              exact Fin.ext hv)
          have hzold : z = S.rootImage q' := by
            change extendedRootImage S.rootImage n hn z ⟨n, hn⟩ =
              extendedRootImage S.rootImage n hn z q' at heq
            rw [extendedRootImage_current,
              extendedRootImage_before S.rootImage n hn z q' hq'old] at heq
            exact heq
          exact False.elim (hzfresh q' hq'old hzold)
      · have hqold : q.val < n := by
          have hqle : q.val ≤ n := by omega
          exact lt_of_le_of_ne hqle (by
            intro hv
            apply hqn
            exact Fin.ext hv)
        by_cases hq'n : q' = ⟨n, hn⟩
        · subst q'
          have holdz : S.rootImage q = z := by
            change extendedRootImage S.rootImage n hn z q =
              extendedRootImage S.rootImage n hn z ⟨n, hn⟩ at heq
            rw [extendedRootImage_current,
              extendedRootImage_before S.rootImage n hn z q hqold] at heq
            exact heq
          exact False.elim (hzfresh q hqold holdz.symm)
        · have hq'old : q'.val < n := by
            have hq'le : q'.val ≤ n := by omega
            exact lt_of_le_of_ne hq'le (by
              intro hv
              apply hq'n
              exact Fin.ext hv)
          apply S.root_injective q q' hqold hq'old
          change extendedRootImage S.rootImage n hn z q =
            extendedRootImage S.rootImage n hn z q' at heq
          rw [extendedRootImage_before S.rootImage n hn z q hqold,
            extendedRootImage_before S.rootImage n hn z q' hq'old] at heq
          exact heq
    edgeState := next
  }

/-- Images of the roots chosen strictly before stage `n`, indexed by the
literal `Fin n`.  This presentation makes the cardinal bound independent of
any injectivity argument. -/
def priorRootImages
    {r b k : ℕ} {B : Type v} [Fintype B] [DecidableEq B]
    {F : OrderedBranchForest r b} {G : SimpleGraph B}
    {assign : Fin b → Fin k} {endpoint : Fin k → Fin 2 → Finset B}
    {rootCandidate : Fin r → Finset B} (n : ℕ) (hn : n < r)
    (S : OnlineOwnerPrefixState F G assign endpoint rootCandidate n) : Finset B :=
  Finset.univ.image fun i : Fin n ↦
    S.rootImage ⟨i.val, lt_trans i.isLt hn⟩

theorem card_priorRootImages_le
    {r b k : ℕ} {B : Type v} [Fintype B] [DecidableEq B]
    {F : OrderedBranchForest r b} {G : SimpleGraph B}
    {assign : Fin b → Fin k} {endpoint : Fin k → Fin 2 → Finset B}
    {rootCandidate : Fin r → Finset B} (n : ℕ) (hn : n < r)
    (S : OnlineOwnerPrefixState F G assign endpoint rootCandidate n) :
    #(priorRootImages n hn S) ≤ n := by
  calc
    #(priorRootImages n hn S) ≤ #((Finset.univ : Finset (Fin n))) :=
      Finset.card_image_le
    _ = n := by simp

theorem mem_priorRootImages_of_before
    {r b k : ℕ} {B : Type v} [Fintype B] [DecidableEq B]
    {F : OrderedBranchForest r b} {G : SimpleGraph B}
    {assign : Fin b → Fin k} {endpoint : Fin k → Fin 2 → Finset B}
    {rootCandidate : Fin r → Finset B} (n : ℕ) (hn : n < r)
    (S : OnlineOwnerPrefixState F G assign endpoint rootCandidate n)
    (q : Fin r) (hq : q.val < n) :
    S.rootImage q ∈ priorRootImages n hn S := by
  rw [priorRootImages, Finset.mem_image]
  refine ⟨⟨q.val, hq⟩, Finset.mem_univ _, ?_⟩
  exact congrArg S.rootImage (Fin.ext rfl)

/-- Build all synchronized owner stages.  At stage `n`, the caller only has
to provide more than `n` eligible roots.  Since at most `n` earlier root
images exist, the construction chooses a fresh one and realizes every
matching-edge batch through the concrete local `OwnerLocalStepData` API. -/
theorem exists_onlineOwnerPrefixState
    {r b k : ℕ} {B : Type v} [Fintype B] [DecidableEq B]
    (F : OrderedBranchForest r b) (G : SimpleGraph B) [DecidableRel G.Adj]
    (assign : Fin b → Fin k)
    (whole endpoint : Fin k → Fin 2 → Finset B)
    (hendpoint : ∀ e c, endpoint e c ⊆ whole e c)
    (hwholeDisjoint : ∀ e, Disjoint (whole e 0) (whole e 1))
    (rho density : Fin k → ℝ)
    (rootCandidate : Fin r → Finset B) (initialRootImage : Fin r → B)
    (eligible : ∀ n (hn : n < r),
      OnlineOwnerPrefixState F G assign endpoint rootCandidate n → Finset B)
    (heligible_card : ∀ n hn S, n < #(eligible n hn S))
    (heligible_subset : ∀ n hn S,
      eligible n hn S ⊆ rootCandidate ⟨n, hn⟩)
    (hsuccessor : ∀ n hn S z,
      z ∈ eligible n hn S →
      (∀ q, q.val < n → z ≠ S.rootImage q) →
      OnlineOwnerSuccessorData F G assign whole endpoint rho density
        rootCandidate n hn S z) :
    Nonempty (OnlineOwnerPrefixState
      F G assign endpoint rootCandidate r) := by
  classical
  have hbuild : ∀ n, n ≤ r → Nonempty (OnlineOwnerPrefixState
      F G assign endpoint rootCandidate n) := by
    intro n hnr
    induction n with
    | zero =>
        exact ⟨emptyOnlineOwnerPrefixState F G assign endpoint rootCandidate
          initialRootImage⟩
    | succ n ih =>
        have hn : n < r := Nat.lt_of_succ_le hnr
        obtain ⟨S⟩ := ih (Nat.le_of_lt hn)
        have hnotSubset : ¬ eligible n hn S ⊆ priorRootImages n hn S := by
          intro hsubset
          have hcard : #(eligible n hn S) ≤ n :=
            (Finset.card_le_card hsubset).trans
              (card_priorRootImages_le n hn S)
          exact (Nat.not_lt_of_ge hcard) (heligible_card n hn S)
        obtain ⟨z, hzeligible, hznot⟩ := Finset.not_subset.mp hnotSubset
        have hzmem : z ∈ rootCandidate ⟨n, hn⟩ :=
          heligible_subset n hn S hzeligible
        have hzfresh : ∀ q, q.val < n → z ≠ S.rootImage q := by
          intro q hq heq
          apply hznot
          rw [heq]
          exact mem_priorRootImages_of_before n hn S q hq
        exact ⟨extendOnlineOwnerPrefixState F G assign whole endpoint
          hendpoint hwholeDisjoint rho density rootCandidate n hn S
          z hzmem hzfresh (hsuccessor n hn S z hzeligible hzfresh)⟩
  exact hbuild r le_rfl

/-- At the terminal stage, the edge state contains every component of its
matching fiber. -/
noncomputable def OnlineOwnerPrefixState.fullEdgeState
    {r b k : ℕ} {B : Type v} [Fintype B] [DecidableEq B]
    (F : OrderedBranchForest r b) (G : SimpleGraph B)
    (assign : Fin b → Fin k) (endpoint : Fin k → Fin 2 → Finset B)
    (rootCandidate : Fin r → Finset B)
    (S : OnlineOwnerPrefixState F G assign endpoint rootCandidate r)
    (e : Fin k) :
    ChosenPartialDynamicEmbedding
      (onlineFiberForest F assign e) G
      (fun i ↦ S.rootImage (onlineFiberOwner F assign e i))
      (endpoint e) Finset.univ := by
  exact castChosenSelected (onlineFiberForest F assign e) G
    (fun i ↦ S.rootImage (onlineFiberOwner F assign e i)) (endpoint e)
    (ownerPrefix_all Finset.univ (onlineFiberOwner F assign e))
    (S.edgeState e)

/-- Forget the terminal partial indexing on one matching edge. -/
theorem OnlineOwnerPrefixState.exists_fullEdgeEmbedding
    {r b k : ℕ} {B : Type v} [Fintype B] [DecidableEq B]
    (F : OrderedBranchForest r b) (G : SimpleGraph B)
    (assign : Fin b → Fin k) (endpoint : Fin k → Fin 2 → Finset B)
    (rootCandidate : Fin r → Finset B)
    (S : OnlineOwnerPrefixState F G assign endpoint rootCandidate r)
    (e : Fin k) :
    ∃ orient : Fin (matchingFiber assign e).card → Fin 2 ≃ Fin 2,
      Nonempty (DynamicAttachedForestEmbedding
        (onlineFiberForest F assign e) G
        (fun i ↦ S.rootImage (onlineFiberOwner F assign e i))
        orient (endpoint e)) := by
  let E := S.fullEdgeState F G assign endpoint rootCandidate e
  exact ⟨E.orient, ⟨E.state.toDynamic
    (onlineFiberForest F assign e) G
    (fun i ↦ S.rootImage (onlineFiberOwner F assign e i))
    E.orient (endpoint e)⟩⟩

end Erdos547b.ZhaoLemma58GlobalOwnerOnlineState

#print axioms Erdos547b.ZhaoLemma58GlobalOwnerOnlineState.emptyOnlineOwnerPrefixState
#print axioms Erdos547b.ZhaoLemma58GlobalOwnerOnlineState.extendOnlineOwnerPrefixState
#print axioms Erdos547b.ZhaoLemma58GlobalOwnerOnlineState.exists_onlineOwnerPrefixState
#print axioms Erdos547b.ZhaoLemma58GlobalOwnerOnlineState.OnlineOwnerPrefixState.exists_fullEdgeEmbedding
