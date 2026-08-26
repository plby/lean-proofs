/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.SourcePendingPlacement
import ErdosProblems.Erdos547b.SourceSortedBranchOrder
import ErdosProblems.Erdos547b.SourceActualPendingPlan

/-!
# A frozen actual pending chunk and its global-owner prefix

The source list, matching edge and orientation plan do not change when
roots are revealed. Only the actual owner prefix grows. Original-index
placement makes preservation of every earlier image explicit.
-/

open scoped SimpleGraph Classical
noncomputable section

namespace Erdos547b.ZhaoSourceActiveChunk

open Finset SimpleGraph Erdos547b.RegularPair
open Erdos547b.ZhaoSourcePendingPlacement Erdos547b.ZhaoSourceSortedBranchOrder
open Erdos547b.ZhaoSourcePendingInterval Erdos547b.ZhaoSourcePendingOwnerInterval
open Erdos547b.ZhaoLemma58DynamicBatchAppend Erdos547b.ZhaoLemma58OnlineOwnerReparent
open Erdos547b.ZhaoSourceOriginalBranchPlacement Erdos547b.ZhaoSourceResidualRootPacking
open Erdos547b.ZhaoSourceSaturatedPacking

theorem prefixSelected_ownerCutoff {b r : ℕ} (items : List (Fin b)) (owner : Fin b → Fin r)
    (hmono : Monotone (listOwner owner items)) (n : ℕ) :
    prefixSelected items (ownerCutoff (listOwner owner items) n) =
      items.toFinset.filter (fun i => (owner i).val < n) := by
  ext j
  constructor
  · intro hj
    have hm := prefixSelected_mem_items hj
    have hp := (mem_branchPrefix _).mp (position_mem_prefix items j hj)
    have ho := (lt_ownerCutoff_iff (listOwner owner items) hmono (position items j hm) n).mp hp
    have hjOwner : (owner j).val < n := by
      simpa only [listOwner, List.get_eq_getElem, get_position] using ho
    exact Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr hm, hjOwner⟩
  · intro hj
    obtain ⟨hm, ho⟩ := Finset.mem_filter.mp hj
    have hm' := List.mem_toFinset.mp hm
    have hpOwner : (listOwner owner items (position items j hm')).val < n := by
      simpa only [listOwner, List.get_eq_getElem, get_position] using ho
    have hp := (lt_ownerCutoff_iff (listOwner owner items) hmono (position items j hm') n).mpr hpOwner
    exact List.mem_toFinset.mpr ((List.mem_take_iff_idxOf_lt hm').mpr hp)

theorem ownerCutoff_succ_eq_of_absent {b r : ℕ} (items : List (Fin b))
    (owner : Fin b → Fin r) (n : Fin r) (habsent : ∀ i ∈ items, owner i ≠ n) :
    ownerCutoff (listOwner owner items) (n.val + 1) = ownerCutoff (listOwner owner items) n.val := by
  unfold ownerCutoff
  congr 1
  ext i
  simp only [ownerPrefix, Finset.mem_filter, Finset.mem_univ, true_and]
  have hne : (listOwner owner items i).val ≠ n.val := by
    intro h
    exact habsent _ (List.get_mem items i) (Fin.ext h)
  omega

open Erdos547b.ZhaoStability Erdos547b.ZhaoDegreeForm Erdos547b.ZhaoEvenReducedPadding
open Erdos547b.ZhaoLemma611Full Erdos547b.ZhaoSourceDegreeFormRootRows
open Erdos547b.ZhaoRichClaim61Lemma611
open Erdos547b.ZhaoSourceEmbeddingHost Erdos547b.ZhaoSourceActualChunkEmbedding
open Erdos547b.ZhaoSourceOnlineMatchingRoot Erdos547b.ZhaoSourceParentCleanup
open Erdos547b.ZhaoSourceActualPendingPlan Erdos547b.ZhaoLemma58ThresholdResidualCapacity

variable {α : ℚ} {hostN q M : ℕ}
variable {G : SimpleGraph (Fin hostN)} [DecidableRel G.Adj]
variable (W : Witness α q M G) (Q : Certificate W)
variable (S : CleanSourceWitness W Q) (C : Index W)
variable {b r : ℕ} (F : OrderedRootedForest b) (owner : Fin b → Fin r)

/-- Immutable source and pair data of one reserved chunk. -/
structure PendingChunk where
  edge : MatchingEdge Q.claim67.M
  edge_away : edge ∈ edgesAwayFromDistinguished Q.claim67.M (padFinset (large W))
    (Sum.inl Q.A) (Sum.inl Q.B)
  items : List (Fin b)
  nodup : items.Nodup
  owner_mono : Monotone (listOwner owner items)
  fits : mass (fun i => (F.size i : ℝ)) items ≤ partOneCapacity W Q S C edge
  plan : ActualPendingPlan W Q S C edge (listForest F items)

variable (D : PendingChunk W Q S C F owner)

abbrev PendingChunk.Prefix (rootImage : Fin r → Fin hostN) (n : ℕ) :=
  PartialDynamicAttachedForestEmbedding (listForest F D.items) (embeddingHost W)
    (fun i => rootImage (listOwner owner D.items i)) D.plan.orient
    (residualSide (edgeWhole W Q D.edge) (deleted W Q D.edge))
    (branchPrefix (ownerCutoff (listOwner owner D.items) n))

def PendingChunk.placement {rootImage : Fin r → Fin hostN} {n : ℕ}
    (E : D.Prefix W Q S C F owner rootImage n) :
    BranchPlacement F (embeddingHost W)
      (prefixSelected D.items (ownerCutoff (listOwner owner D.items) n))
      (fun i => rootImage (owner i)) (fun e => residualSide (edgeWhole W Q e) (deleted W Q e)) :=
  toPlacement F (embeddingHost W) D.items (fun i => rootImage (owner i)) D.plan.orient
    (fun e => residualSide (edgeWhole W Q e) (deleted W Q e)) D.edge E

/-- Advance the actual prefix after the current root has been selected. -/
theorem PendingChunk.exists_advance (rootImage : Fin r → Fin hostN) (n : Fin r)
    (E : D.Prefix W Q S C F owner rootImage n.val) (z : Fin hostN)
    (hz : EligibleRoot W Q S C D.edge z) :
    ∃ E' : D.Prefix W Q S C F owner (Function.update rootImage n z) (n.val + 1),
      ∀ i hi, E'.forestCopy.componentCopy i
          (branchPrefix_mono (ownerCutoff_mono (listOwner owner D.items) (Nat.le_succ n.val)) hi) =
        E.forestCopy.componentCopy i hi := by
  exact exists_owner_extension (listForest F D.items) (embeddingHost W)
    (listOwner owner D.items) D.owner_mono D.plan.orient
    (residualSide (edgeWhole W Q D.edge) (deleted W Q D.edge)) n rootImage E z
    (fun i p E => D.plan.step i p E z hz)

/-- Skipping an owner absent from this chunk changes no branch copy and
needs no eligibility constraint toward this unrelated pending pair. -/
theorem PendingChunk.exists_skip (rootImage : Fin r → Fin hostN) (n : Fin r)
    (E : D.Prefix W Q S C F owner rootImage n.val) (z : Fin hostN)
    (habsent : ∀ i ∈ D.items, owner i ≠ n) :
    ∃ E' : D.Prefix W Q S C F owner (Function.update rootImage n z) (n.val + 1),
      ∀ i hi, E'.forestCopy.componentCopy i
          (branchPrefix_mono (ownerCutoff_mono (listOwner owner D.items) (Nat.le_succ n.val)) hi) =
        E.forestCopy.componentCopy i hi := by
  have hcut := ownerCutoff_succ_eq_of_absent D.items owner n habsent
  have hagrees : ∀ i ∈ branchPrefix (ownerCutoff (listOwner owner D.items) n.val),
      Function.update rootImage n z (listOwner owner D.items i) = rootImage (listOwner owner D.items i) := by
    intro i _
    exact Function.update_of_ne (habsent _ (List.get_mem D.items i)) z rootImage
  let old := partialReparent (listForest F D.items) (embeddingHost W)
    (fun i => rootImage (listOwner owner D.items i))
    (fun i => Function.update rootImage n z (listOwner owner D.items i))
    D.plan.orient (residualSide (edgeWhole W Q D.edge) (deleted W Q D.edge))
    (branchPrefix (ownerCutoff (listOwner owner D.items) n.val)) E hagrees
  let out := castPartialSelected (listForest F D.items) (embeddingHost W)
    (fun i => Function.update rootImage n z (listOwner owner D.items i)) D.plan.orient
    (residualSide (edgeWhole W Q D.edge) (deleted W Q D.edge))
    (congrArg (@branchPrefix D.items.length) hcut.symm) old
  exact ⟨out, fun _ _ => rfl⟩

/-- The immutable chunk data make local image preservation transfer
directly to the original-index placement used by the global state. -/
theorem PendingChunk.placement_preserved
    (rootImage rootImage' : Fin r → Fin hostN) {n m : ℕ} (hnm : n ≤ m)
    (E : D.Prefix W Q S C F owner rootImage n) (E' : D.Prefix W Q S C F owner rootImage' m)
    (hcopy : ∀ i hi, E'.forestCopy.componentCopy i
        (branchPrefix_mono (ownerCutoff_mono (listOwner owner D.items) hnm) hi) =
      E.forestCopy.componentCopy i hi)
    (j : Fin b) (hj : j ∈ prefixSelected D.items (ownerCutoff (listOwner owner D.items) n)) :
    (D.placement W Q S C F owner E').forestCopy.componentCopy j
        (prefixSelected_mono D.items (ownerCutoff_mono (listOwner owner D.items) hnm) hj) =
      (D.placement W Q S C F owner E).forestCopy.componentCopy j hj :=
  toPlacement_copy_of_extension F (embeddingHost W) D.items (fun i => rootImage (owner i))
    D.plan.orient (fun e => residualSide (edgeWhole W Q e) (deleted W Q e)) D.edge
    (ownerCutoff_mono (listOwner owner D.items) hnm) (fun i => rootImage' (owner i)) E E' hcopy j hj

end Erdos547b.ZhaoSourceActiveChunk

#print axioms Erdos547b.ZhaoSourceActiveChunk.prefixSelected_ownerCutoff
#print axioms Erdos547b.ZhaoSourceActiveChunk.PendingChunk.exists_advance
#print axioms Erdos547b.ZhaoSourceActiveChunk.PendingChunk.exists_skip
#print axioms Erdos547b.ZhaoSourceActiveChunk.PendingChunk.placement_preserved
