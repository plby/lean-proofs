/- leanprover/lean4:v4.33.0 -/
import ErdosProblems.Erdos547b.Lemma58GlobalCutOnline

/-!
# Target-relative cleaning for future online cut parents

For a non-root cut parent we do not delete all non-neighbours of a root fixed
in advance.  Instead, from the matching endpoint containing that parent we
delete only vertices having fewer than `numParts` neighbours in the future
child-root candidate.  Any actually embedded parent that survives this
cleaning then leaves enough choices for the online root step.
-/

open scoped SimpleGraph
noncomputable section

namespace Erdos547b.ZhaoLemma58OnlineParentCleaning

open Finset Fintype SimpleGraph
open Erdos547b.TreePartition
open Erdos547b.RegularPair
open Erdos547b.ZhaoClaim68BranchAdapter
open Erdos547b.ZhaoClaim617BranchCount
open Erdos547b.ZhaoClaim616SourceBridge
open Erdos547b.ZhaoClaim616SourceBridge.OrderedBranchForest
open Erdos547b.ZhaoLemma58MatchingAssembly
open Erdos547b.ZhaoLemma58DynamicBatchAppend
open Erdos547b.ZhaoLemma58GlobalOwnerOnlineState
open Erdos547b.ZhaoLemma58GlobalOwnerBranchImage
open Erdos547b.ZhaoLemma58GlobalCutOnline

universe u v

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {T : SimpleGraph V} [DecidableRel T.Adj]
variable {globalRoot : V} {small : ℕ}

/-- Vertices of physical endpoint `(e,c)` which cannot serve as the actual
embedded parent of at least one future non-root cut child assigned to `e`. -/
def onlineParentBad
    {B : Type v} [Fintype B] [DecidableEq B]
    (P : ZhaoForestPartition T globalRoot small)
    (G : SimpleGraph B) [DecidableRel G.Adj]
    (rootCandidate : Fin P.numParts → Finset B)
    {k : ℕ}
    (assign : Fin (Fintype.card (ChildKey P.orderedForest)) → Fin k)
    (endpoint : Fin k → Fin 2 → Finset B)
    (e : Fin k) (c : Fin 2) : Finset B :=
  (endpoint e c).filter fun x ↦
    ∃ q : Fin P.numParts, ∃ hq : q.val ≠ 0,
      ∃ hnotroot : P.parent q hq ≠ P.roots (P.parentPart q hq),
        assign (cutParentBranchCoordinate P q hq hnotroot).1 = e ∧
        #((rootCandidate q).filter (G.Adj x)) < P.numParts

@[simp] theorem mem_onlineParentBad
    {B : Type v} [Fintype B] [DecidableEq B]
    (P : ZhaoForestPartition T globalRoot small)
    (G : SimpleGraph B) [DecidableRel G.Adj]
    (rootCandidate : Fin P.numParts → Finset B)
    {k : ℕ}
    (assign : Fin (Fintype.card (ChildKey P.orderedForest)) → Fin k)
    (endpoint : Fin k → Fin 2 → Finset B)
    (e : Fin k) (c : Fin 2) (x : B) :
    x ∈ onlineParentBad P G rootCandidate assign endpoint e c ↔
      x ∈ endpoint e c ∧
      ∃ q : Fin P.numParts, ∃ hq : q.val ≠ 0,
        ∃ hnotroot : P.parent q hq ≠ P.roots (P.parentPart q hq),
          assign (cutParentBranchCoordinate P q hq hnotroot).1 = e ∧
          #((rootCandidate q).filter (G.Adj x)) < P.numParts := by
  simp [onlineParentBad]

/-- Matching endpoints after the small target-relative parent cleaning. -/
def onlineCleanEndpoint
    {B : Type v} [Fintype B] [DecidableEq B]
    (P : ZhaoForestPartition T globalRoot small)
    (G : SimpleGraph B) [DecidableRel G.Adj]
    (rootCandidate : Fin P.numParts → Finset B)
    {k : ℕ}
    (assign : Fin (Fintype.card (ChildKey P.orderedForest)) → Fin k)
    (endpoint : Fin k → Fin 2 → Finset B)
    (e : Fin k) (c : Fin 2) : Finset B :=
  endpoint e c \ onlineParentBad P G rootCandidate assign endpoint e c

theorem onlineCleanEndpoint_subset
    {B : Type v} [Fintype B] [DecidableEq B]
    (P : ZhaoForestPartition T globalRoot small)
    (G : SimpleGraph B) [DecidableRel G.Adj]
    (rootCandidate : Fin P.numParts → Finset B)
    {k : ℕ}
    (assign : Fin (Fintype.card (ChildKey P.orderedForest)) → Fin k)
    (endpoint : Fin k → Fin 2 → Finset B) (e : Fin k) (c : Fin 2) :
    onlineCleanEndpoint P G rootCandidate assign endpoint e c ⊆
      endpoint e c :=
  Finset.sdiff_subset

/-- Low-degree target vertices for one future child-root reservoir. -/
def parentLowDegree
    {B : Type v} [Fintype B] [DecidableEq B]
    (P : ZhaoForestPartition T globalRoot small)
    (G : SimpleGraph B) [DecidableRel G.Adj]
    (rootCandidate : Fin P.numParts → Finset B)
    (X : Finset B) (q : Fin P.numParts) : Finset B :=
  X.filter fun x ↦
    #((rootCandidate q).filter (G.Adj x)) < P.numParts

/-- The physical bad set is covered by the union over all child roots. -/
theorem onlineParentBad_subset_biUnion
    {B : Type v} [Fintype B] [DecidableEq B]
    (P : ZhaoForestPartition T globalRoot small)
    (G : SimpleGraph B) [DecidableRel G.Adj]
    (rootCandidate : Fin P.numParts → Finset B)
    {k : ℕ}
    (assign : Fin (Fintype.card (ChildKey P.orderedForest)) → Fin k)
    (endpoint : Fin k → Fin 2 → Finset B)
    (e : Fin k) (c : Fin 2) :
    onlineParentBad P G rootCandidate assign endpoint e c ⊆
      (Finset.univ : Finset (Fin P.numParts)).biUnion
        (parentLowDegree P G rootCandidate (endpoint e c)) := by
  intro x hx
  obtain ⟨hxEndpoint, q, hq, hnotroot, he, hlow⟩ :=
    (mem_onlineParentBad P G rootCandidate assign endpoint e c x).mp hx
  apply Finset.mem_biUnion.mpr
  refine ⟨q, Finset.mem_univ _, ?_⟩
  exact Finset.mem_filter.mpr ⟨hxEndpoint, hlow⟩

/-- Union-bound form of the permanent online-parent cleaning loss. -/
theorem card_onlineParentBad_le
    {B : Type v} [Fintype B] [DecidableEq B]
    (P : ZhaoForestPartition T globalRoot small)
    (G : SimpleGraph B) [DecidableRel G.Adj]
    (rootCandidate : Fin P.numParts → Finset B)
    {k : ℕ}
    (assign : Fin (Fintype.card (ChildKey P.orderedForest)) → Fin k)
    (endpoint : Fin k → Fin 2 → Finset B)
    (e : Fin k) (c : Fin 2) (loss : ℕ)
    (hlow : ∀ q,
      #(parentLowDegree P G rootCandidate (endpoint e c) q) ≤ loss) :
    #(onlineParentBad P G rootCandidate assign endpoint e c) ≤
      P.numParts * loss := by
  calc
    #(onlineParentBad P G rootCandidate assign endpoint e c) ≤
        #((Finset.univ : Finset (Fin P.numParts)).biUnion
          (parentLowDegree P G rootCandidate (endpoint e c))) :=
      Finset.card_le_card
        (onlineParentBad_subset_biUnion P G rootCandidate assign endpoint e c)
    _ ≤ ∑ q : Fin P.numParts,
        #(parentLowDegree P G rootCandidate (endpoint e c) q) := by
      simpa only [Finset.sum_attach, Finset.sum_filter] using
        (Finset.card_biUnion_le
          (s := (Finset.univ : Finset (Fin P.numParts)))
          (t := parentLowDegree P G rootCandidate (endpoint e c)))
    _ ≤ ∑ _q : Fin P.numParts, loss := by
      exact Finset.sum_le_sum fun q _ ↦ hlow q
    _ = P.numParts * loss := by simp

/-- Regularity bounds the low-degree target vertices for one root candidate.
The threshold is the exact online requirement `numParts`. -/
theorem card_parentLowDegree_le_of_uniform
    {B : Type v} [Fintype B] [DecidableEq B]
    (P : ZhaoForestPartition T globalRoot small)
    (G : SimpleGraph B) [DecidableRel G.Adj]
    (rootCandidate : Fin P.numParts → Finset B)
    (q : Fin P.numParts)
    (endpointWhole rootWhole endpointRaw : Finset B)
    (rho : ℝ)
    (hunif : G.IsUniform rho endpointWhole rootWhole)
    (hendpoint : endpointRaw ⊆ endpointWhole)
    (hroot : rootCandidate q ⊆ rootWhole)
    (hendpointLarge : rho * (#endpointWhole : ℝ) ≤ #endpointRaw)
    (hrootLarge : rho * (#rootWhole : ℝ) ≤ #(rootCandidate q))
    (hthreshold : (P.numParts : ℝ) ≤
      (G.edgeDensity endpointWhole rootWhole - rho) * #(rootCandidate q)) :
    (#(parentLowDegree P G rootCandidate endpointRaw q) : ℝ) ≤
      rho * #endpointWhole := by
  let standardBad : Finset B :=
    {x ∈ endpointRaw |
      (#({y ∈ rootCandidate q | G.Adj x y}) : ℝ) <
        (G.edgeDensity endpointWhole rootWhole - rho) * #(rootCandidate q)}
  have hsub : parentLowDegree P G rootCandidate endpointRaw q ⊆
      standardBad := by
    intro x hx
    have hx' := Finset.mem_filter.mp hx
    apply Finset.mem_filter.mpr
    refine ⟨hx'.1, ?_⟩
    have hcast :
        (#((rootCandidate q).filter (G.Adj x)) : ℝ) < P.numParts := by
      exact_mod_cast hx'.2
    exact hcast.trans_le hthreshold
  calc
    (#(parentLowDegree P G rootCandidate endpointRaw q) : ℝ) ≤
        #standardBad := by exact_mod_cast Finset.card_le_card hsub
    _ ≤ rho * #endpointWhole := by
      exact card_lowDegreeVertices_le G hunif hendpoint hroot
        hendpointLarge hrootLarge

/-- The branch image of an already processed non-root cut parent lies in its
literal cleaned physical endpoint. -/
theorem cutParentBranchCopy_mem_cleanEndpoint
    {B : Type v} [Fintype B] [DecidableEq B]
    (P : ZhaoForestPartition T globalRoot small)
    (G : SimpleGraph B) [DecidableRel G.Adj]
    (rootCandidate : Fin P.numParts → Finset B)
    {k : ℕ}
    (assign : Fin (Fintype.card (ChildKey P.orderedForest)) → Fin k)
    (endpoint : Fin k → Fin 2 → Finset B)
    (n : ℕ)
    (S : OnlineOwnerPrefixState (branchForest P) G assign
      (onlineCleanEndpoint P G rootCandidate assign endpoint)
      rootCandidate n)
    (q : Fin P.numParts) (hq : q.val ≠ 0)
    (hnotroot : P.parent q hq ≠ P.roots (P.parentPart q hq))
    (hqn : q.val ≤ n) :
    let z := cutParentBranchCoordinate P q hq hnotroot
    let hj : ((branchForest P).owner z.1).val < n := by
      rw [cutParentBranchCoordinate_owner P q hq hnotroot]
      exact lt_of_lt_of_le (P.parent_earlier q hq) hqn
    ∃ c,
      OnlineOwnerPrefixState.branchCopy (branchForest P) G assign
          (onlineCleanEndpoint P G rootCandidate assign endpoint)
          rootCandidate n S z.1 hj z.2 ∈
        onlineCleanEndpoint P G rootCandidate assign endpoint
          (assign z.1) c := by
  classical
  let z := cutParentBranchCoordinate P q hq hnotroot
  have hj : ((branchForest P).owner z.1).val < n := by
    rw [cutParentBranchCoordinate_owner P q hq hnotroot]
    exact lt_of_lt_of_le (P.parent_earlier q hq) hqn
  let i := assignmentIndex assign z.1
  have hi : i ∈ ownerPrefix Finset.univ
      (onlineFiberOwner (branchForest P) assign (assign z.1)) n :=
    (assignmentIndex_mem_ownerPrefix (branchForest P) assign z.1 n).2 hj
  let c := (S.edgeState (assign z.1)).orient i
    ((onlineFiberForest (branchForest P) assign (assign z.1)).isTree i
      |>.coloringTwoOfVert
        ((onlineFiberForest (branchForest P) assign (assign z.1)).root i)
        (assignmentVertex (branchForest P) assign z.1 z.2))
  refine ⟨c, ?_⟩
  have hm := (S.edgeState (assign z.1)).state.map_side i hi
    (assignmentVertex (branchForest P) assign z.1 z.2)
  simpa only [OnlineOwnerPrefixState.branchCopy] using hm

/-- The dynamic eligible set always has `numParts` vertices once root-root
links satisfy the same bound.  In the non-root case the conclusion follows
directly from survival of the actual branch parent in `onlineCleanEndpoint`.
-/
theorem card_onlineRootEligible_cleanEndpoint
    {B : Type v} [Fintype B] [DecidableEq B]
    (P : ZhaoForestPartition T globalRoot small)
    (G : SimpleGraph B) [DecidableRel G.Adj]
    (rootCandidate : Fin P.numParts → Finset B)
    {k : ℕ}
    (assign : Fin (Fintype.card (ChildKey P.orderedForest)) → Fin k)
    (endpoint : Fin k → Fin 2 → Finset B)
    (hfirst : P.numParts ≤
      #(rootCandidate ⟨0, P.numParts_pos⟩))
    (hrootLink : ∀ q (hq : q.val ≠ 0)
      (hroot : P.parent q hq = P.roots (P.parentPart q hq))
      x, x ∈ rootCandidate (P.parentPart q hq) →
      P.numParts ≤ #((rootCandidate q).filter (G.Adj x)))
    (n : ℕ) (hn : n < P.numParts)
    (S : CutOnlineOwnerPrefixState P G assign
      (onlineCleanEndpoint P G rootCandidate assign endpoint)
      rootCandidate n) :
    P.numParts ≤
      #(onlineRootEligible P G assign
        (onlineCleanEndpoint P G rootCandidate assign endpoint)
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
      obtain ⟨c, hparentClean⟩ :=
        cutParentBranchCopy_mem_cleanEndpoint P G rootCandidate assign endpoint
          n S.state q hq hroot le_rfl
      have hparentEndpoint :
          OnlineOwnerPrefixState.branchCopy (branchForest P) G assign
              (onlineCleanEndpoint P G rootCandidate assign endpoint)
              rootCandidate n S.state z.1 hj z.2 ∈ endpoint (assign z.1) c :=
        onlineCleanEndpoint_subset P G rootCandidate assign endpoint
          (assign z.1) c hparentClean
      have hparentNotBad :
          OnlineOwnerPrefixState.branchCopy (branchForest P) G assign
              (onlineCleanEndpoint P G rootCandidate assign endpoint)
              rootCandidate n S.state z.1 hj z.2 ∉
            onlineParentBad P G rootCandidate assign endpoint
              (assign z.1) c :=
        (Finset.mem_sdiff.mp hparentClean).2
      have hcard : P.numParts ≤ #((rootCandidate q).filter
          (G.Adj (OnlineOwnerPrefixState.branchCopy (branchForest P) G assign
            (onlineCleanEndpoint P G rootCandidate assign endpoint)
            rootCandidate n S.state z.1 hj z.2))) := by
        apply Nat.le_of_not_gt
        intro hlt
        apply hparentNotBad
        exact (mem_onlineParentBad P G rootCandidate assign endpoint
          (assign z.1) c _).2
          ⟨hparentEndpoint, q, hq, hroot, rfl, hlt⟩
      simpa [onlineRootEligible, hzero, onlineCutParentImage, hroot, q, z]
        using hcard

end Erdos547b.ZhaoLemma58OnlineParentCleaning

#print axioms Erdos547b.ZhaoLemma58OnlineParentCleaning.card_onlineRootEligible_cleanEndpoint
