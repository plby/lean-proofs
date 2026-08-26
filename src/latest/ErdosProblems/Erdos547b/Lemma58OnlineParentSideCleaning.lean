/- leanprover/lean4:v4.33.0 -/
import ErdosProblems.Erdos547b.Lemma58OnlineParentCleaning

/-!
# Side-aware target cleaning for future online cut parents

For a fixed Part-1/2 source orientation only one endpoint of a matching edge
can contain a given cut parent.  Appendix batches may allow both.  The bad
set below therefore charges a future child root only on the endpoint sides
allowed by the pre-orientation target plan.
-/

open scoped SimpleGraph
noncomputable section

namespace Erdos547b.ZhaoLemma58OnlineParentSideCleaning

open Finset Fintype SimpleGraph
open Erdos547b.TreePartition
open Erdos547b.ZhaoClaim68BranchAdapter
open Erdos547b.ZhaoClaim617BranchCount
open Erdos547b.ZhaoClaim616SourceBridge
open Erdos547b.ZhaoClaim616SourceBridge.OrderedBranchForest
open Erdos547b.ZhaoLemma58GlobalOwnerOnlineState
open Erdos547b.ZhaoLemma58GlobalOwnerBranchImage
open Erdos547b.ZhaoLemma58GlobalCutOnline
open Erdos547b.ZhaoLemma58OnlineParentCleaning

universe u v

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {T : SimpleGraph V} [DecidableRel T.Adj]
variable {globalRoot : V} {small : ℕ}

/-- Vertices of `(e,c)` which have too few neighbours in a future child-root
candidate whose actual cut-parent coordinate is permitted on side `c`. -/
def onlineParentBadWithSides
    {B : Type v} [Fintype B] [DecidableEq B]
    (P : ZhaoForestPartition T globalRoot small)
    (G : SimpleGraph B) [DecidableRel G.Adj]
    (rootCandidate : Fin P.numParts → Finset B)
    {k : ℕ}
    (assign : Fin (Fintype.card (ChildKey P.orderedForest)) → Fin k)
    (endpoint : Fin k → Fin 2 → Finset B)
    (allowed : (Σ j : Fin (Fintype.card (ChildKey P.orderedForest)),
      Fin ((branchForest P).branches.size j)) → Finset (Fin 2))
    (e : Fin k) (c : Fin 2) : Finset B :=
  (endpoint e c).filter fun x ↦
    ∃ q : Fin P.numParts, ∃ hq : q.val ≠ 0,
      ∃ hnotroot : P.parent q hq ≠ P.roots (P.parentPart q hq),
        let z := cutParentBranchCoordinate P q hq hnotroot
        assign z.1 = e ∧ c ∈ allowed z ∧
          #((rootCandidate q).filter (G.Adj x)) < P.numParts

@[simp] theorem mem_onlineParentBadWithSides
    {B : Type v} [Fintype B] [DecidableEq B]
    (P : ZhaoForestPartition T globalRoot small)
    (G : SimpleGraph B) [DecidableRel G.Adj]
    (rootCandidate : Fin P.numParts → Finset B)
    {k : ℕ}
    (assign : Fin (Fintype.card (ChildKey P.orderedForest)) → Fin k)
    (endpoint : Fin k → Fin 2 → Finset B)
    (allowed : (Σ j : Fin (Fintype.card (ChildKey P.orderedForest)),
      Fin ((branchForest P).branches.size j)) → Finset (Fin 2))
    (e : Fin k) (c : Fin 2) (x : B) :
    x ∈ onlineParentBadWithSides P G rootCandidate assign endpoint allowed e c ↔
      x ∈ endpoint e c ∧
      ∃ q : Fin P.numParts, ∃ hq : q.val ≠ 0,
        ∃ hnotroot : P.parent q hq ≠ P.roots (P.parentPart q hq),
          let z := cutParentBranchCoordinate P q hq hnotroot
          assign z.1 = e ∧ c ∈ allowed z ∧
            #((rootCandidate q).filter (G.Adj x)) < P.numParts := by
  simp [onlineParentBadWithSides]

/-- Matching endpoints after side-aware future-parent cleaning. -/
def onlineSideCleanEndpoint
    {B : Type v} [Fintype B] [DecidableEq B]
    (P : ZhaoForestPartition T globalRoot small)
    (G : SimpleGraph B) [DecidableRel G.Adj]
    (rootCandidate : Fin P.numParts → Finset B)
    {k : ℕ}
    (assign : Fin (Fintype.card (ChildKey P.orderedForest)) → Fin k)
    (endpoint : Fin k → Fin 2 → Finset B)
    (allowed : (Σ j : Fin (Fintype.card (ChildKey P.orderedForest)),
      Fin ((branchForest P).branches.size j)) → Finset (Fin 2))
    (e : Fin k) (c : Fin 2) : Finset B :=
  endpoint e c \
    onlineParentBadWithSides P G rootCandidate assign endpoint allowed e c

theorem onlineSideCleanEndpoint_subset
    {B : Type v} [Fintype B] [DecidableEq B]
    (P : ZhaoForestPartition T globalRoot small)
    (G : SimpleGraph B) [DecidableRel G.Adj]
    (rootCandidate : Fin P.numParts → Finset B)
    {k : ℕ}
    (assign : Fin (Fintype.card (ChildKey P.orderedForest)) → Fin k)
    (endpoint : Fin k → Fin 2 → Finset B)
    (allowed : (Σ j : Fin (Fintype.card (ChildKey P.orderedForest)),
      Fin ((branchForest P).branches.size j)) → Finset (Fin 2))
    (e : Fin k) (c : Fin 2) :
    onlineSideCleanEndpoint P G rootCandidate assign endpoint allowed e c ⊆
      endpoint e c :=
  Finset.sdiff_subset

/-- The side-aware bad set is covered by the same union over child roots. -/
theorem onlineParentBadWithSides_subset_biUnion
    {B : Type v} [Fintype B] [DecidableEq B]
    (P : ZhaoForestPartition T globalRoot small)
    (G : SimpleGraph B) [DecidableRel G.Adj]
    (rootCandidate : Fin P.numParts → Finset B)
    {k : ℕ}
    (assign : Fin (Fintype.card (ChildKey P.orderedForest)) → Fin k)
    (endpoint : Fin k → Fin 2 → Finset B)
    (allowed : (Σ j : Fin (Fintype.card (ChildKey P.orderedForest)),
      Fin ((branchForest P).branches.size j)) → Finset (Fin 2))
    (e : Fin k) (c : Fin 2) :
    onlineParentBadWithSides P G rootCandidate assign endpoint allowed e c ⊆
      (Finset.univ : Finset (Fin P.numParts)).biUnion
        (parentLowDegree P G rootCandidate (endpoint e c)) := by
  intro x hx
  obtain ⟨hxEndpoint, q, hq, hnotroot, _he, _hc, hlow⟩ :=
    (mem_onlineParentBadWithSides P G rootCandidate assign endpoint allowed
      e c x).mp hx
  exact Finset.mem_biUnion.mpr
    ⟨q, Finset.mem_univ _, Finset.mem_filter.mpr ⟨hxEndpoint, hlow⟩⟩

/-- Union bound for the permanent side-aware online-parent cleaning loss. -/
theorem card_onlineParentBadWithSides_le
    {B : Type v} [Fintype B] [DecidableEq B]
    (P : ZhaoForestPartition T globalRoot small)
    (G : SimpleGraph B) [DecidableRel G.Adj]
    (rootCandidate : Fin P.numParts → Finset B)
    {k : ℕ}
    (assign : Fin (Fintype.card (ChildKey P.orderedForest)) → Fin k)
    (endpoint : Fin k → Fin 2 → Finset B)
    (allowed : (Σ j : Fin (Fintype.card (ChildKey P.orderedForest)),
      Fin ((branchForest P).branches.size j)) → Finset (Fin 2))
    (e : Fin k) (c : Fin 2) (loss : ℕ)
    (hlow : ∀ q,
      #(parentLowDegree P G rootCandidate (endpoint e c) q) ≤ loss) :
    #(onlineParentBadWithSides P G rootCandidate assign endpoint allowed e c) ≤
      P.numParts * loss := by
  calc
    #(onlineParentBadWithSides P G rootCandidate assign endpoint allowed e c) ≤
        #((Finset.univ : Finset (Fin P.numParts)).biUnion
          (parentLowDegree P G rootCandidate (endpoint e c))) :=
      Finset.card_le_card
        (onlineParentBadWithSides_subset_biUnion P G rootCandidate assign
          endpoint allowed e c)
    _ ≤ ∑ q : Fin P.numParts,
        #(parentLowDegree P G rootCandidate (endpoint e c) q) := by
      simpa only [Finset.sum_attach, Finset.sum_filter] using
        (Finset.card_biUnion_le
          (s := (Finset.univ : Finset (Fin P.numParts)))
          (t := parentLowDegree P G rootCandidate (endpoint e c)))
    _ ≤ ∑ _q : Fin P.numParts, loss := by
      exact Finset.sum_le_sum fun q _ ↦ hlow q
    _ = P.numParts * loss := by simp

/-- Sharper side-aware union bound: a low-degree estimate is needed only for
child roots whose literal cut-parent coordinate is assigned to `(e,c)` and
whose plan actually permits side `c`. -/
theorem card_onlineParentBadWithSides_le_of_relevant
    {B : Type v} [Fintype B] [DecidableEq B]
    (P : ZhaoForestPartition T globalRoot small)
    (G : SimpleGraph B) [DecidableRel G.Adj]
    (rootCandidate : Fin P.numParts → Finset B)
    {k : ℕ}
    (assign : Fin (Fintype.card (ChildKey P.orderedForest)) → Fin k)
    (endpoint : Fin k → Fin 2 → Finset B)
    (allowed : (Σ j : Fin (Fintype.card (ChildKey P.orderedForest)),
      Fin ((branchForest P).branches.size j)) → Finset (Fin 2))
    (e : Fin k) (c : Fin 2) (loss : ℕ)
    (hlow : ∀ q (hq : q.val ≠ 0)
      (hnotroot : P.parent q hq ≠ P.roots (P.parentPart q hq)),
      let z := cutParentBranchCoordinate P q hq hnotroot
      assign z.1 = e → c ∈ allowed z →
        #(parentLowDegree P G rootCandidate (endpoint e c) q) ≤ loss) :
    #(onlineParentBadWithSides P G rootCandidate assign endpoint allowed e c) ≤
      P.numParts * loss := by
  classical
  let relevant : Fin P.numParts → Prop := fun q ↦
    ∃ hq : q.val ≠ 0,
      ∃ hnotroot : P.parent q hq ≠ P.roots (P.parentPart q hq),
        let z := cutParentBranchCoordinate P q hq hnotroot
        assign z.1 = e ∧ c ∈ allowed z
  let badFor : Fin P.numParts → Finset B := fun q ↦
    if relevant q then parentLowDegree P G rootCandidate (endpoint e c) q
    else ∅
  have hsub :
      onlineParentBadWithSides P G rootCandidate assign endpoint allowed e c ⊆
        (Finset.univ : Finset (Fin P.numParts)).biUnion badFor := by
    intro x hx
    obtain ⟨hxEndpoint, q, hq, hnotroot, he, hc, hdegree⟩ :=
      (mem_onlineParentBadWithSides P G rootCandidate assign endpoint allowed
        e c x).mp hx
    have hrel : relevant q := ⟨hq, hnotroot, he, hc⟩
    apply Finset.mem_biUnion.mpr
    refine ⟨q, Finset.mem_univ _, ?_⟩
    dsimp only [badFor]
    rw [if_pos hrel]
    exact Finset.mem_filter.mpr ⟨hxEndpoint, hdegree⟩
  calc
    #(onlineParentBadWithSides P G rootCandidate assign endpoint allowed e c) ≤
        #((Finset.univ : Finset (Fin P.numParts)).biUnion badFor) :=
      Finset.card_le_card hsub
    _ ≤ ∑ q : Fin P.numParts, #(badFor q) := by
      simpa only [Finset.sum_attach, Finset.sum_filter] using
        (Finset.card_biUnion_le
          (s := (Finset.univ : Finset (Fin P.numParts))) (t := badFor))
    _ ≤ ∑ _q : Fin P.numParts, loss := by
      apply Finset.sum_le_sum
      intro q _
      by_cases hrel : relevant q
      · have hbad : badFor q =
            parentLowDegree P G rootCandidate (endpoint e c) q := by
          simp only [badFor, if_pos hrel]
        rw [hbad]
        obtain ⟨hq, hnotroot, he, hc⟩ := hrel
        exact hlow q hq hnotroot he hc
      · simp only [badFor, if_neg hrel, Finset.card_empty, Nat.zero_le]
    _ = P.numParts * loss := by simp

/-- Deleting the permanent endpoint complement and then the side-aware
future-parent bad set costs at most the sum of their two cardinal bounds. -/
theorem card_whole_sdiff_onlineSideCleanEndpoint_le
    {B : Type v} [Fintype B] [DecidableEq B]
    (P : ZhaoForestPartition T globalRoot small)
    (G : SimpleGraph B) [DecidableRel G.Adj]
    (rootCandidate : Fin P.numParts → Finset B)
    {k : ℕ}
    (assign : Fin (Fintype.card (ChildKey P.orderedForest)) → Fin k)
    (whole endpoint : Fin k → Fin 2 → Finset B)
    (allowed : (Σ j : Fin (Fintype.card (ChildKey P.orderedForest)),
      Fin ((branchForest P).branches.size j)) → Finset (Fin 2))
    (e : Fin k) (c : Fin 2) (permanent loss : ℕ)
    (hpermanent : #(whole e c \ endpoint e c) ≤ permanent)
    (hlow : ∀ q (hq : q.val ≠ 0)
      (hnotroot : P.parent q hq ≠ P.roots (P.parentPart q hq)),
      let z := cutParentBranchCoordinate P q hq hnotroot
      assign z.1 = e → c ∈ allowed z →
        #(parentLowDegree P G rootCandidate (endpoint e c) q) ≤ loss) :
    #(whole e c \
        onlineSideCleanEndpoint P G rootCandidate assign endpoint allowed e c) ≤
      permanent + P.numParts * loss := by
  let bad := onlineParentBadWithSides P G rootCandidate assign endpoint
    allowed e c
  have hsub : whole e c \
      onlineSideCleanEndpoint P G rootCandidate assign endpoint allowed e c ⊆
      (whole e c \ endpoint e c) ∪ bad := by
    intro x hx
    have hx' := Finset.mem_sdiff.mp hx
    by_cases he : x ∈ endpoint e c
    · apply Finset.mem_union_right
      have hnotclean := hx'.2
      rw [onlineSideCleanEndpoint] at hnotclean
      by_contra hb
      exact hnotclean (Finset.mem_sdiff.mpr ⟨he, hb⟩)
    · exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hx'.1, he⟩)
  calc
    #(whole e c \
        onlineSideCleanEndpoint P G rootCandidate assign endpoint allowed e c) ≤
        #((whole e c \ endpoint e c) ∪ bad) :=
      Finset.card_le_card hsub
    _ ≤ #(whole e c \ endpoint e c) + #bad := Finset.card_union_le _ _
    _ ≤ permanent + P.numParts * loss := Nat.add_le_add hpermanent
      (card_onlineParentBadWithSides_le_of_relevant P G rootCandidate assign
        endpoint allowed e c loss hlow)

/-- Dynamic root eligibility from side-aware cleaning.  The only additional
invariant is that the actual already embedded cut parent lies on a side
allowed by the pre-orientation plan. -/
theorem card_onlineRootEligible_sideCleanEndpoint
    {B : Type v} [Fintype B] [DecidableEq B]
    (P : ZhaoForestPartition T globalRoot small)
    (G : SimpleGraph B) [DecidableRel G.Adj]
    (rootCandidate : Fin P.numParts → Finset B)
    {k : ℕ}
    (assign : Fin (Fintype.card (ChildKey P.orderedForest)) → Fin k)
    (endpoint : Fin k → Fin 2 → Finset B)
    (allowed : (Σ j : Fin (Fintype.card (ChildKey P.orderedForest)),
      Fin ((branchForest P).branches.size j)) → Finset (Fin 2))
    (hfirst : P.numParts ≤ #(rootCandidate ⟨0, P.numParts_pos⟩))
    (hrootLink : ∀ q (hq : q.val ≠ 0)
      (_hroot : P.parent q hq = P.roots (P.parentPart q hq))
      x, x ∈ rootCandidate (P.parentPart q hq) →
      P.numParts ≤ #((rootCandidate q).filter (G.Adj x)))
    (n : ℕ) (hn : n < P.numParts)
    (S : CutOnlineOwnerPrefixState P G assign
      (onlineSideCleanEndpoint P G rootCandidate assign endpoint allowed)
      rootCandidate n)
    (hparentSide : ∀ q (hq : q.val ≠ 0)
      (hnotroot : P.parent q hq ≠ P.roots (P.parentPart q hq))
      (hqn : q.val ≤ n),
      let z := cutParentBranchCoordinate P q hq hnotroot
      let hj : ((branchForest P).owner z.1).val < n := by
        rw [cutParentBranchCoordinate_owner P q hq hnotroot]
        exact lt_of_lt_of_le (P.parent_earlier q hq) hqn
      ∃ c,
        OnlineOwnerPrefixState.branchCopy (branchForest P) G assign
            (onlineSideCleanEndpoint P G rootCandidate assign endpoint allowed)
            rootCandidate n S.state z.1 hj z.2 ∈
          onlineSideCleanEndpoint P G rootCandidate assign endpoint allowed
            (assign z.1) c ∧
        c ∈ allowed z) :
    P.numParts ≤
      #(onlineRootEligible P G assign
        (onlineSideCleanEndpoint P G rootCandidate assign endpoint allowed)
        rootCandidate n hn S) := by
  classical
  by_cases hzero : n = 0
  · have hfin : (⟨n, hn⟩ : Fin P.numParts) = ⟨0, P.numParts_pos⟩ :=
      Fin.ext hzero
    simpa [onlineRootEligible, hzero, hfin] using hfirst
  · let q : Fin P.numParts := ⟨n, hn⟩
    have hq : q.val ≠ 0 := by simpa [q] using hzero
    by_cases hroot : P.parent q hq = P.roots (P.parentPart q hq)
    · have hparentMem : S.state.rootImage (P.parentPart q hq) ∈
          rootCandidate (P.parentPart q hq) :=
        S.state.root_mem (P.parentPart q hq) (P.parent_earlier q hq)
      have hcard := hrootLink q hq hroot
        (S.state.rootImage (P.parentPart q hq)) hparentMem
      simpa [onlineRootEligible, hzero, onlineCutParentImage, hroot, q] using hcard
    · let z := cutParentBranchCoordinate P q hq hroot
      have hj : ((branchForest P).owner z.1).val < n := by
        rw [cutParentBranchCoordinate_owner P q hq hroot]
        exact P.parent_earlier q hq
      obtain ⟨c, hparentClean, hcAllowed⟩ :=
        hparentSide q hq hroot le_rfl
      have hparentEndpoint :
          OnlineOwnerPrefixState.branchCopy (branchForest P) G assign
              (onlineSideCleanEndpoint P G rootCandidate assign endpoint
                allowed) rootCandidate n S.state z.1 hj z.2 ∈
            endpoint (assign z.1) c :=
        onlineSideCleanEndpoint_subset P G rootCandidate assign endpoint
          allowed (assign z.1) c hparentClean
      have hparentNotBad :
          OnlineOwnerPrefixState.branchCopy (branchForest P) G assign
              (onlineSideCleanEndpoint P G rootCandidate assign endpoint
                allowed) rootCandidate n S.state z.1 hj z.2 ∉
            onlineParentBadWithSides P G rootCandidate assign endpoint allowed
              (assign z.1) c :=
        (Finset.mem_sdiff.mp hparentClean).2
      have hcard : P.numParts ≤ #((rootCandidate q).filter
          (G.Adj (OnlineOwnerPrefixState.branchCopy (branchForest P) G assign
            (onlineSideCleanEndpoint P G rootCandidate assign endpoint allowed)
            rootCandidate n S.state z.1 hj z.2))) := by
        apply Nat.le_of_not_gt
        intro hlt
        apply hparentNotBad
        exact (mem_onlineParentBadWithSides P G rootCandidate assign endpoint
          allowed (assign z.1) c _).2
          ⟨hparentEndpoint, q, hq, hroot, rfl, hcAllowed, hlt⟩
      simpa [onlineRootEligible, hzero, onlineCutParentImage, hroot, q, z]
        using hcard

/-- Execute the synchronized recursion against side-aware permanent parent
cleaning.  The caller supplies only the source-side coverage invariant for
already embedded branch coordinates and the concrete local step data. -/
theorem exists_cutOnlineOwnerPrefixState_sideCleaning
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
    (allowed : (Σ j : Fin (Fintype.card (ChildKey P.orderedForest)),
      Fin ((branchForest P).branches.size j)) → Finset (Fin 2))
    (initialRootImage : Fin P.numParts → B)
    (hfirst : P.numParts ≤ #(rootCandidate ⟨0, P.numParts_pos⟩))
    (hrootLink : ∀ q (hq : q.val ≠ 0)
      (_hroot : P.parent q hq = P.roots (P.parentPart q hq))
      x, x ∈ rootCandidate (P.parentPart q hq) →
      P.numParts ≤ #((rootCandidate q).filter (G.Adj x)))
    (hparentSide : ∀ n (hn : n < P.numParts)
      (S : CutOnlineOwnerPrefixState P G assign
        (onlineSideCleanEndpoint P G rootCandidate assign endpoint allowed)
        rootCandidate n),
      ∀ q (hq : q.val ≠ 0)
        (hnotroot : P.parent q hq ≠ P.roots (P.parentPart q hq))
        (hqn : q.val ≤ n),
        let z := cutParentBranchCoordinate P q hq hnotroot
        let hj : ((branchForest P).owner z.1).val < n := by
          rw [cutParentBranchCoordinate_owner P q hq hnotroot]
          exact lt_of_lt_of_le (P.parent_earlier q hq) hqn
        ∃ c,
          OnlineOwnerPrefixState.branchCopy (branchForest P) G assign
              (onlineSideCleanEndpoint P G rootCandidate assign endpoint
                allowed) rootCandidate n S.state z.1 hj z.2 ∈
            onlineSideCleanEndpoint P G rootCandidate assign endpoint allowed
              (assign z.1) c ∧
          c ∈ allowed z)
    (hsuccessor : ∀ n hn
      (S : CutOnlineOwnerPrefixState P G assign
        (onlineSideCleanEndpoint P G rootCandidate assign endpoint allowed)
        rootCandidate n)
      z,
      z ∈ onlineRootEligible P G assign
        (onlineSideCleanEndpoint P G rootCandidate assign endpoint allowed)
        rootCandidate n hn S →
      (∀ q, q.val < n → z ≠ S.state.rootImage q) →
      OnlineOwnerSuccessorData (branchForest P) G assign whole
        (onlineSideCleanEndpoint P G rootCandidate assign endpoint allowed)
        rho density rootCandidate n hn S.state z) :
    Nonempty (CutOnlineOwnerPrefixState P G assign
      (onlineSideCleanEndpoint P G rootCandidate assign endpoint allowed)
      rootCandidate P.numParts) := by
  exact exists_cutOnlineOwnerPrefixState P G assign whole
    (onlineSideCleanEndpoint P G rootCandidate assign endpoint allowed)
    (fun e c ↦
      (onlineSideCleanEndpoint_subset P G rootCandidate assign endpoint
        allowed e c).trans (hendpoint e c))
    hwholeDisjoint rho density rootCandidate initialRootImage
    (fun n hn S ↦
      card_onlineRootEligible_sideCleanEndpoint P G rootCandidate assign
        endpoint allowed hfirst hrootLink n hn S (hparentSide n hn S))
    hsuccessor

end Erdos547b.ZhaoLemma58OnlineParentSideCleaning

#print axioms Erdos547b.ZhaoLemma58OnlineParentSideCleaning.card_onlineParentBadWithSides_le
#print axioms Erdos547b.ZhaoLemma58OnlineParentSideCleaning.card_onlineParentBadWithSides_le_of_relevant
#print axioms Erdos547b.ZhaoLemma58OnlineParentSideCleaning.card_onlineRootEligible_sideCleanEndpoint
#print axioms Erdos547b.ZhaoLemma58OnlineParentSideCleaning.card_whole_sdiff_onlineSideCleanEndpoint_le
#print axioms Erdos547b.ZhaoLemma58OnlineParentSideCleaning.exists_cutOnlineOwnerPrefixState_sideCleaning
