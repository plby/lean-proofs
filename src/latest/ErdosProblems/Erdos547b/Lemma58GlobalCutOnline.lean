/- leanprover/lean4:v4.33.0 -/
import ErdosProblems.Erdos547b.Lemma58GlobalOwnerBranchImage
import ErdosProblems.Erdos547b.Claim617BranchCount
import ErdosProblems.Erdos547b.Lemma59FullOnline
import ErdosProblems.Erdos547b.Claim616HierarchyClassification

/-!
# Online cut-parent certificates for grouped Lemma 5.8

When component `q` is reached, its deleted parent lies in a strictly earlier
component.  Hence its actual host image is already available either as an
earlier distinguished root or as an earlier matching-fiber branch vertex.
This file defines that image and proves that later synchronized owner steps
do not change it.
-/

open scoped SimpleGraph
noncomputable section

namespace Erdos547b.ZhaoLemma58GlobalCutOnline

open Finset Fintype SimpleGraph
open Erdos547b.TreePartition
open Erdos547b.ZhaoClaim68
open Erdos547b.ZhaoClaim68BranchAdapter
open Erdos547b.ZhaoClaim617BranchCount
open Erdos547b.ZhaoLemma59Part2Full
open Erdos547b.ZhaoLemma59FullOnline
open Erdos547b.ZhaoClaim616HierarchyClassification
open Erdos547b.ZhaoLemma58GlobalOwnerOnlineState
open Erdos547b.ZhaoLemma58GlobalOwnerBranchImage

universe u v

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {T : SimpleGraph V} [DecidableRel T.Adj]
variable {globalRoot : V} {small : ℕ}

/-- A non-root cut parent belongs to the literal partition non-root set. -/
theorem cutParent_mem_partitionNonroots
    (P : ZhaoForestPartition T globalRoot small)
    (q : Fin P.numParts) (hq : q.val ≠ 0)
    (hnotroot : P.parent q hq ≠ P.roots (P.parentPart q hq)) :
    P.parent q hq ∈ partitionNonroots P := by
  rw [partitionNonroots, Finset.mem_sdiff]
  refine ⟨Finset.mem_univ _, ?_⟩
  intro hp
  obtain ⟨i, -, hi⟩ := Finset.mem_image.mp hp
  have hipart : i = P.parentPart q hq := by
    calc
      i = P.componentIndex (P.roots i) :=
        (componentIndex_roots P i).symm
      _ = P.componentIndex (P.parent q hq) := congrArg P.componentIndex hi
      _ = P.parentPart q hq := componentIndex_parent P q hq
  subst i
  exact hnotroot hi.symm

/-- Canonical root-deleted branch coordinate of a non-root cut parent. -/
noncomputable def cutParentBranchCoordinate
    (P : ZhaoForestPartition T globalRoot small)
    (q : Fin P.numParts) (hq : q.val ≠ 0)
    (hnotroot : P.parent q hq ≠ P.roots (P.parentPart q hq)) :
    Σ j, Fin ((branchForest P).branches.size j) :=
  (partitionBranchEquivNonroots P).symm
    ⟨P.parent q hq, cutParent_mem_partitionNonroots P q hq hnotroot⟩

@[simp] theorem cutParentBranchCoordinate_value
    (P : ZhaoForestPartition T globalRoot small)
    (q : Fin P.numParts) (hq : q.val ≠ 0)
    (hnotroot : P.parent q hq ≠ P.roots (P.parentPart q hq)) :
    (partitionBranchEquivNonroots P
      (cutParentBranchCoordinate P q hq hnotroot)).1 = P.parent q hq := by
  exact congrArg Subtype.val ((partitionBranchEquivNonroots P).apply_symm_apply
    ⟨P.parent q hq, cutParent_mem_partitionNonroots P q hq hnotroot⟩)

theorem cutParentBranchCoordinate_owner
    (P : ZhaoForestPartition T globalRoot small)
    (q : Fin P.numParts) (hq : q.val ≠ 0)
    (hnotroot : P.parent q hq ≠ P.roots (P.parentPart q hq)) :
    (branchForest P).owner (cutParentBranchCoordinate P q hq hnotroot).1 =
      P.parentPart q hq := by
  have hc := partitionBranchEquivNonroots_component P
    (cutParentBranchCoordinate P q hq hnotroot)
  rw [cutParentBranchCoordinate_value P q hq hnotroot,
    componentIndex_parent P q hq] at hc
  exact hc.symm

/-- The already embedded host image of the deleted parent of component `q`.
The state contains owners `< n`, while `q ≤ n`; strict parent ordering makes
the branch case available. -/
noncomputable def onlineCutParentImage
    {B : Type v} [Fintype B] [DecidableEq B]
    (P : ZhaoForestPartition T globalRoot small)
    (G : SimpleGraph B)
    {k : ℕ}
    (assign : Fin (Fintype.card (ChildKey P.orderedForest)) → Fin k)
    (endpoint : Fin k → Fin 2 → Finset B)
    (rootCandidate : Fin P.numParts → Finset B)
    (n : ℕ)
    (S : OnlineOwnerPrefixState (branchForest P) G assign endpoint
      rootCandidate n)
    (q : Fin P.numParts) (hq : q.val ≠ 0) (hqn : q.val ≤ n) : B :=
  if hroot : P.parent q hq = P.roots (P.parentPart q hq) then
    S.rootImage (P.parentPart q hq)
  else
    let z := cutParentBranchCoordinate P q hq hroot
    OnlineOwnerPrefixState.branchCopy (branchForest P) G assign endpoint
      rootCandidate n S z.1 (by
        rw [cutParentBranchCoordinate_owner P q hq hroot]
        exact lt_of_lt_of_le (P.parent_earlier q hq) hqn) z.2

/-- Extending owner `n` preserves the image of every cut parent belonging to
a component numbered at most `n`. -/
theorem onlineCutParentImage_extend
    {B : Type v} [Fintype B] [DecidableEq B]
    (P : ZhaoForestPartition T globalRoot small)
    (G : SimpleGraph B) [DecidableRel G.Adj]
    {k : ℕ}
    (assign : Fin (Fintype.card (ChildKey P.orderedForest)) → Fin k)
    (whole endpoint : Fin k → Fin 2 → Finset B)
    (hendpoint : ∀ e c, endpoint e c ⊆ whole e c)
    (hwholeDisjoint : ∀ e, Disjoint (whole e 0) (whole e 1))
    (rho density : Fin k → ℝ)
    (rootCandidate : Fin P.numParts → Finset B)
    (n : ℕ) (hn : n < P.numParts)
    (S : OnlineOwnerPrefixState (branchForest P) G assign endpoint
      rootCandidate n)
    (zroot : B) (hzmem : zroot ∈ rootCandidate ⟨n, hn⟩)
    (hzfresh : ∀ q, q.val < n → zroot ≠ S.rootImage q)
    (D : OnlineOwnerSuccessorData (branchForest P) G assign whole endpoint
      rho density rootCandidate n hn S zroot)
    (q : Fin P.numParts) (hq : q.val ≠ 0) (hqn : q.val ≤ n) :
    onlineCutParentImage P G assign endpoint rootCandidate (n + 1)
        (extendOnlineOwnerPrefixState (branchForest P) G assign whole endpoint
          hendpoint hwholeDisjoint rho density rootCandidate n hn S zroot
          hzmem hzfresh D)
        q hq (by omega) =
      onlineCutParentImage P G assign endpoint rootCandidate n S q hq hqn := by
  classical
  unfold onlineCutParentImage
  split_ifs with hroot
  · apply extendedRootImage_before
    exact lt_of_lt_of_le (P.parent_earlier q hq) hqn
  · apply branchCopy_extend_before

/-- A synchronized owner-prefix state together with all deleted cut-edge
adjacencies whose child root has already been selected. -/
structure CutOnlineOwnerPrefixState
    {B : Type v} [Fintype B] [DecidableEq B]
    (P : ZhaoForestPartition T globalRoot small)
    (G : SimpleGraph B) [DecidableRel G.Adj]
    {k : ℕ}
    (assign : Fin (Fintype.card (ChildKey P.orderedForest)) → Fin k)
    (endpoint : Fin k → Fin 2 → Finset B)
    (rootCandidate : Fin P.numParts → Finset B) (n : ℕ) where
  state : OnlineOwnerPrefixState (branchForest P) G assign endpoint
    rootCandidate n
  cut_adj : ∀ q (hq : q.val ≠ 0) (hqn : q.val < n),
    G.Adj
      (onlineCutParentImage P G assign endpoint rootCandidate n state
        q hq (Nat.le_of_lt hqn))
      (state.rootImage q)

/-- Empty synchronized cut-aware state. -/
noncomputable def emptyCutOnlineOwnerPrefixState
    {B : Type v} [Fintype B] [DecidableEq B]
    (P : ZhaoForestPartition T globalRoot small)
    (G : SimpleGraph B) [DecidableRel G.Adj]
    {k : ℕ}
    (assign : Fin (Fintype.card (ChildKey P.orderedForest)) → Fin k)
    (endpoint : Fin k → Fin 2 → Finset B)
    (rootCandidate : Fin P.numParts → Finset B)
    (initialRootImage : Fin P.numParts → B) :
    CutOnlineOwnerPrefixState P G assign endpoint rootCandidate 0 where
  state := emptyOnlineOwnerPrefixState (branchForest P) G assign endpoint
    rootCandidate initialRootImage
  cut_adj := by omega

/-- Extend a cut-aware state by one root and all owner-`n` matching batches.
Only the actual already embedded cut-parent image is required. -/
noncomputable def extendCutOnlineOwnerPrefixState
    {B : Type v} [Fintype B] [DecidableEq B]
    (P : ZhaoForestPartition T globalRoot small)
    (G : SimpleGraph B) [DecidableRel G.Adj]
    {k : ℕ}
    (assign : Fin (Fintype.card (ChildKey P.orderedForest)) → Fin k)
    (whole endpoint : Fin k → Fin 2 → Finset B)
    (hendpoint : ∀ e c, endpoint e c ⊆ whole e c)
    (hwholeDisjoint : ∀ e, Disjoint (whole e 0) (whole e 1))
    (rho density : Fin k → ℝ)
    (rootCandidate : Fin P.numParts → Finset B)
    (n : ℕ) (hn : n < P.numParts)
    (S : CutOnlineOwnerPrefixState P G assign endpoint rootCandidate n)
    (z : B) (hzmem : z ∈ rootCandidate ⟨n, hn⟩)
    (hzfresh : ∀ q, q.val < n → z ≠ S.state.rootImage q)
    (hzparent : ∀ hzero : n ≠ 0,
      G.Adj
        (onlineCutParentImage P G assign endpoint rootCandidate n S.state
          ⟨n, hn⟩ (by simpa using hzero) le_rfl)
        z)
    (D : OnlineOwnerSuccessorData (branchForest P) G assign whole endpoint
      rho density rootCandidate n hn S.state z) :
    CutOnlineOwnerPrefixState P G assign endpoint rootCandidate (n + 1) := by
  classical
  let state' := extendOnlineOwnerPrefixState (branchForest P) G assign
    whole endpoint hendpoint hwholeDisjoint rho density rootCandidate n hn
    S.state z hzmem hzfresh D
  exact {
    state := state'
    cut_adj := by
      intro q hq hqsucc
      by_cases hqn : q.val = n
      · have hqeq : q = ⟨n, hn⟩ := Fin.ext hqn
        subst q
        have hparent := onlineCutParentImage_extend P G assign whole endpoint
          hendpoint hwholeDisjoint rho density rootCandidate n hn S.state z
          hzmem hzfresh D ⟨n, hn⟩ hq le_rfl
        change G.Adj
          (onlineCutParentImage P G assign endpoint rootCandidate (n + 1)
            state' ⟨n, hn⟩ hq (by omega))
          (extendedRootImage S.state.rootImage n hn z ⟨n, hn⟩)
        rw [hparent, extendedRootImage_current]
        exact hzparent (by simpa using hq)
      · have hqold : q.val < n := by omega
        have hold := S.cut_adj q hq hqold
        have hparent := onlineCutParentImage_extend P G assign whole endpoint
          hendpoint hwholeDisjoint rho density rootCandidate n hn S.state z
          hzmem hzfresh D q hq (Nat.le_of_lt hqold)
        change G.Adj
          (onlineCutParentImage P G assign endpoint rootCandidate (n + 1)
            state' q hq (by omega))
          (extendedRootImage S.state.rootImage n hn z q)
        rw [hparent,
          extendedRootImage_before S.state.rootImage n hn z q hqold]
        exact hold
  }

/-- Dynamic eligible roots at owner `n`: for `n=0` this is the whole root
candidate; otherwise it is the neighborhood of the actual embedded cut
parent. -/
def onlineRootEligible
    {B : Type v} [Fintype B] [DecidableEq B]
    (P : ZhaoForestPartition T globalRoot small)
    (G : SimpleGraph B) [DecidableRel G.Adj]
    {k : ℕ}
    (assign : Fin (Fintype.card (ChildKey P.orderedForest)) → Fin k)
    (endpoint : Fin k → Fin 2 → Finset B)
    (rootCandidate : Fin P.numParts → Finset B)
    (n : ℕ) (hn : n < P.numParts)
    (S : CutOnlineOwnerPrefixState P G assign endpoint rootCandidate n) :
    Finset B :=
  if hzero : n = 0 then rootCandidate ⟨n, hn⟩
  else (rootCandidate ⟨n, hn⟩).filter
    (G.Adj (onlineCutParentImage P G assign endpoint rootCandidate n S.state
      ⟨n, hn⟩ (by simpa using hzero) le_rfl))

theorem onlineRootEligible_subset
    {B : Type v} [Fintype B] [DecidableEq B]
    (P : ZhaoForestPartition T globalRoot small)
    (G : SimpleGraph B) [DecidableRel G.Adj]
    {k : ℕ}
    (assign : Fin (Fintype.card (ChildKey P.orderedForest)) → Fin k)
    (endpoint : Fin k → Fin 2 → Finset B)
    (rootCandidate : Fin P.numParts → Finset B)
    (n : ℕ) (hn : n < P.numParts)
    (S : CutOnlineOwnerPrefixState P G assign endpoint rootCandidate n) :
    onlineRootEligible P G assign endpoint rootCandidate n hn S ⊆
      rootCandidate ⟨n, hn⟩ := by
  intro z hz
  by_cases hzero : n = 0
  · simpa [onlineRootEligible, hzero] using hz
  · exact (Finset.mem_filter.mp (by
      simpa [onlineRootEligible, hzero] using hz)).1

theorem onlineRootEligible_parent_adj
    {B : Type v} [Fintype B] [DecidableEq B]
    (P : ZhaoForestPartition T globalRoot small)
    (G : SimpleGraph B) [DecidableRel G.Adj]
    {k : ℕ}
    (assign : Fin (Fintype.card (ChildKey P.orderedForest)) → Fin k)
    (endpoint : Fin k → Fin 2 → Finset B)
    (rootCandidate : Fin P.numParts → Finset B)
    (n : ℕ) (hn : n < P.numParts)
    (S : CutOnlineOwnerPrefixState P G assign endpoint rootCandidate n)
    (z : B) (hz : z ∈ onlineRootEligible P G assign endpoint rootCandidate
      n hn S) (hzero : n ≠ 0) :
    G.Adj
      (onlineCutParentImage P G assign endpoint rootCandidate n S.state
        ⟨n, hn⟩ (by simpa using hzero) le_rfl)
      z := by
  exact (Finset.mem_filter.mp (by
    simpa [onlineRootEligible, hzero] using hz)).2

/-- Execute the full synchronized cut-aware recursion.  The root hypothesis
is exactly on the dynamic eligible set determined by the actual already
embedded parent; no non-neighbour set is deleted from future matching
endpoints. -/
theorem exists_cutOnlineOwnerPrefixState
    {B : Type v} [Fintype B] [DecidableEq B]
    (P : ZhaoForestPartition T globalRoot small)
    (G : SimpleGraph B) [DecidableRel G.Adj]
    {k : ℕ}
    (assign : Fin (Fintype.card (ChildKey P.orderedForest)) → Fin k)
    (whole endpoint : Fin k → Fin 2 → Finset B)
    (hendpoint : ∀ e c, endpoint e c ⊆ whole e c)
    (hwholeDisjoint : ∀ e, Disjoint (whole e 0) (whole e 1))
    (rho density : Fin k → ℝ)
    (rootCandidate : Fin P.numParts → Finset B)
    (initialRootImage : Fin P.numParts → B)
    (heligible : ∀ n hn
      (S : CutOnlineOwnerPrefixState P G assign endpoint rootCandidate n),
      P.numParts ≤
        #(onlineRootEligible P G assign endpoint rootCandidate n hn S))
    (hsuccessor : ∀ n hn
      (S : CutOnlineOwnerPrefixState P G assign endpoint rootCandidate n)
      z,
      z ∈ onlineRootEligible P G assign endpoint rootCandidate n hn S →
      (∀ q, q.val < n → z ≠ S.state.rootImage q) →
      OnlineOwnerSuccessorData (branchForest P) G assign whole endpoint
        rho density rootCandidate n hn S.state z) :
    Nonempty (CutOnlineOwnerPrefixState P G assign endpoint rootCandidate
      P.numParts) := by
  classical
  have hbuild : ∀ n, n ≤ P.numParts →
      Nonempty (CutOnlineOwnerPrefixState P G assign endpoint rootCandidate n) := by
    intro n hnr
    induction n with
    | zero =>
        exact ⟨emptyCutOnlineOwnerPrefixState P G assign endpoint rootCandidate
          initialRootImage⟩
    | succ n ih =>
        have hn : n < P.numParts := Nat.lt_of_succ_le hnr
        obtain ⟨S⟩ := ih (Nat.le_of_lt hn)
        let eligible := onlineRootEligible P G assign endpoint rootCandidate
          n hn S
        have heligibleCard : n < #eligible :=
          lt_of_lt_of_le hn (heligible n hn S)
        have hnotSubset : ¬ eligible ⊆ priorRootImages n hn S.state := by
          intro hsubset
          have hcard : #eligible ≤ n :=
            (Finset.card_le_card hsubset).trans
              (card_priorRootImages_le n hn S.state)
          exact (Nat.not_lt_of_ge hcard) heligibleCard
        obtain ⟨z, hzeligible, hznot⟩ := Finset.not_subset.mp hnotSubset
        have hzmem : z ∈ rootCandidate ⟨n, hn⟩ :=
          onlineRootEligible_subset P G assign endpoint rootCandidate n hn S
            hzeligible
        have hzfresh : ∀ q, q.val < n → z ≠ S.state.rootImage q := by
          intro q hq heq
          apply hznot
          rw [heq]
          exact mem_priorRootImages_of_before n hn S.state q hq
        have hzparent : ∀ hzero : n ≠ 0,
            G.Adj
              (onlineCutParentImage P G assign endpoint rootCandidate n
                S.state ⟨n, hn⟩ (by simpa using hzero) le_rfl)
              z := by
          intro hzero
          exact onlineRootEligible_parent_adj P G assign endpoint
            rootCandidate n hn S z hzeligible hzero
        exact ⟨extendCutOnlineOwnerPrefixState P G assign whole endpoint
          hendpoint hwholeDisjoint rho density rootCandidate n hn S z hzmem
          hzfresh hzparent
          (hsuccessor n hn S z hzeligible hzfresh)⟩
  exact hbuild P.numParts le_rfl

end Erdos547b.ZhaoLemma58GlobalCutOnline

#print axioms Erdos547b.ZhaoLemma58GlobalCutOnline.onlineCutParentImage_extend
#print axioms Erdos547b.ZhaoLemma58GlobalCutOnline.extendCutOnlineOwnerPrefixState
#print axioms Erdos547b.ZhaoLemma58GlobalCutOnline.exists_cutOnlineOwnerPrefixState
