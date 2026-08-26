/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.SourcePendingPlacement
import ErdosProblems.Erdos547b.SourceSortedBranchOrder
import ErdosProblems.Erdos547b.SourceMatchingPendingPlan
import ErdosProblems.Erdos547b.SourceActiveChunk

/-!
# A frozen actual pending chunk and its global-owner prefix

The source list, matching edge and orientation plan do not change when
roots are revealed. Only the actual owner prefix grows. Original-index
placement makes preservation of every earlier image explicit.
-/

open scoped SimpleGraph Classical
noncomputable section

namespace Erdos547b.ZhaoSourceMatchingActiveChunk

open Finset SimpleGraph Erdos547b.RegularPair
open Erdos547b.ZhaoSourcePendingPlacement Erdos547b.ZhaoSourceSortedBranchOrder
open Erdos547b.ZhaoSourcePendingInterval Erdos547b.ZhaoSourcePendingOwnerInterval
open Erdos547b.ZhaoLemma58DynamicBatchAppend Erdos547b.ZhaoLemma58OnlineOwnerReparent
open Erdos547b.ZhaoSourceOriginalBranchPlacement Erdos547b.ZhaoSourceResidualRootPacking
open Erdos547b.ZhaoSourceSaturatedPacking

open Erdos547b.ZhaoSourceActiveChunk (prefixSelected_ownerCutoff ownerCutoff_succ_eq_of_absent)

open Erdos547b.ZhaoStability Erdos547b.ZhaoDegreeForm Erdos547b.ZhaoEvenReducedPadding
open Erdos547b.ZhaoLemma611Full Erdos547b.ZhaoSourceDegreeFormRootRows
open Erdos547b.ZhaoRichClaim61Lemma611
open Erdos547b.ZhaoSourceEmbeddingHost Erdos547b.ZhaoSourceActualChunkEmbedding
open Erdos547b.ZhaoSourceMatchingRootSelection Erdos547b.ZhaoSourceMatchingParentCleanup
open Erdos547b.ZhaoSourceMatchingGeometry
open Erdos547b.ZhaoSourceMatchingPendingPlan Erdos547b.ZhaoLemma58ThresholdResidualCapacity

variable {α : ℚ} {hostN q M : ℕ}
variable {G : SimpleGraph (Fin hostN)} [DecidableRel G.Adj]
variable (W : Witness α q M G) (Q : Certificate W)
variable (S : CleanSourceWitness W Q) (P : (padGraph (reduced W)).Subgraph) (C : Index W)
variable {b r : ℕ} (F : OrderedRootedForest b) (owner : Fin b → Fin r)

/-- Immutable source and pair data of one reserved chunk. -/
structure PendingChunk where
  edge : MatchingEdge P
  edge_away : edge ∈ edgesAwayFromDistinguished P (padFinset (large W))
    (Sum.inl Q.A) (Sum.inl Q.B)
  items : List (Fin b)
  nodup : items.Nodup
  owner_mono : Monotone (listOwner owner items)
  fits : mass (fun i => (F.size i : ℝ)) items ≤ capacity W Q P S C edge
  plan : ActualPendingPlan W Q P S C edge (listForest F items)

variable (D : PendingChunk W Q S P C F owner)

abbrev PendingChunk.Prefix (rootImage : Fin r → Fin hostN) (n : ℕ) :=
  PartialDynamicAttachedForestEmbedding (listForest F D.items) (embeddingHost W)
    (fun i => rootImage (listOwner owner D.items i)) D.plan.orient
    (residualSide (pairWhole W P D.edge) (deleted W Q P D.edge))
    (branchPrefix (ownerCutoff (listOwner owner D.items) n))

def PendingChunk.placement {rootImage : Fin r → Fin hostN} {n : ℕ}
    (E : D.Prefix W Q S P C F owner rootImage n) :
    BranchPlacement F (embeddingHost W)
      (prefixSelected D.items (ownerCutoff (listOwner owner D.items) n))
      (fun i => rootImage (owner i)) (fun e => residualSide (pairWhole W P e) (deleted W Q P e)) :=
  toPlacement F (embeddingHost W) D.items (fun i => rootImage (owner i)) D.plan.orient
    (fun e => residualSide (pairWhole W P e) (deleted W Q P e)) D.edge E

/-- Advance the actual prefix after the current root has been selected. -/
theorem PendingChunk.exists_advance (rootImage : Fin r → Fin hostN) (n : Fin r)
    (E : D.Prefix W Q S P C F owner rootImage n.val) (z : Fin hostN)
    (hz : EligibleRoot W Q S P C D.edge z) :
    ∃ E' : D.Prefix W Q S P C F owner (Function.update rootImage n z) (n.val + 1),
      ∀ i hi, E'.forestCopy.componentCopy i
          (branchPrefix_mono (ownerCutoff_mono (listOwner owner D.items) (Nat.le_succ n.val)) hi) =
        E.forestCopy.componentCopy i hi := by
  exact exists_owner_extension (listForest F D.items) (embeddingHost W)
    (listOwner owner D.items) D.owner_mono D.plan.orient
    (residualSide (pairWhole W P D.edge) (deleted W Q P D.edge)) n rootImage E z
    (fun i p E => D.plan.step i p E z hz)

/-- Skipping an owner absent from this chunk changes no branch copy and
needs no eligibility constraint toward this unrelated pending pair. -/
theorem PendingChunk.exists_skip (rootImage : Fin r → Fin hostN) (n : Fin r)
    (E : D.Prefix W Q S P C F owner rootImage n.val) (z : Fin hostN)
    (habsent : ∀ i ∈ D.items, owner i ≠ n) :
    ∃ E' : D.Prefix W Q S P C F owner (Function.update rootImage n z) (n.val + 1),
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
    D.plan.orient (residualSide (pairWhole W P D.edge) (deleted W Q P D.edge))
    (branchPrefix (ownerCutoff (listOwner owner D.items) n.val)) E hagrees
  let out := castPartialSelected (listForest F D.items) (embeddingHost W)
    (fun i => Function.update rootImage n z (listOwner owner D.items i)) D.plan.orient
    (residualSide (pairWhole W P D.edge) (deleted W Q P D.edge))
    (congrArg (@branchPrefix D.items.length) hcut.symm) old
  exact ⟨out, fun _ _ => rfl⟩

/-- The immutable chunk data make local image preservation transfer
directly to the original-index placement used by the global state. -/
theorem PendingChunk.placement_preserved
    (rootImage rootImage' : Fin r → Fin hostN) {n m : ℕ} (hnm : n ≤ m)
    (E : D.Prefix W Q S P C F owner rootImage n) (E' : D.Prefix W Q S P C F owner rootImage' m)
    (hcopy : ∀ i hi, E'.forestCopy.componentCopy i
        (branchPrefix_mono (ownerCutoff_mono (listOwner owner D.items) hnm) hi) =
      E.forestCopy.componentCopy i hi)
    (j : Fin b) (hj : j ∈ prefixSelected D.items (ownerCutoff (listOwner owner D.items) n)) :
    (D.placement W Q S P C F owner E').forestCopy.componentCopy j
        (prefixSelected_mono D.items (ownerCutoff_mono (listOwner owner D.items) hnm) hj) =
      (D.placement W Q S P C F owner E).forestCopy.componentCopy j hj :=
  toPlacement_copy_of_extension F (embeddingHost W) D.items (fun i => rootImage (owner i))
    D.plan.orient (fun e => residualSide (pairWhole W P e) (deleted W Q P e)) D.edge
    (ownerCutoff_mono (listOwner owner D.items) hnm) (fun i => rootImage' (owner i)) E E' hcopy j hj

end Erdos547b.ZhaoSourceMatchingActiveChunk

#print axioms Erdos547b.ZhaoSourceMatchingActiveChunk.PendingChunk.exists_advance
#print axioms Erdos547b.ZhaoSourceMatchingActiveChunk.PendingChunk.exists_skip
#print axioms Erdos547b.ZhaoSourceMatchingActiveChunk.PendingChunk.placement_preserved
