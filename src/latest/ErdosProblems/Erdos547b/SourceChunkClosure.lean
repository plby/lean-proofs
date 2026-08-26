/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.SourceReservationFamilyState

/-!
# Closing actual chunks while retaining their source support

A fully processed active prefix becomes a completed original-index
placement without changing any image. Fresh closed chunks are built from
the actual fixed plan, so they retain positive source density at their
branch-root endpoints rather than only arbitrary attachment edges.
-/

open scoped SimpleGraph Classical
noncomputable section

namespace Erdos547b.ZhaoSourceActiveChunk

open Finset SimpleGraph Erdos547b.RegularPair
open Erdos547b.ZhaoSourceOriginalBranchPlacement Erdos547b.ZhaoSourcePendingPlacement
open Erdos547b.ZhaoSourceSortedBranchOrder Erdos547b.ZhaoSourcePendingOwnerInterval
open Erdos547b.ZhaoSourceActiveChunk Erdos547b.ZhaoSourceReservationFamilyState
open Erdos547b.ZhaoSourceSaturatedPacking Erdos547b.ZhaoSourceResidualRootPacking
open Erdos547b.ZhaoStability Erdos547b.ZhaoDegreeForm Erdos547b.ZhaoEvenReducedPadding
open Erdos547b.ZhaoLemma611Full Erdos547b.ZhaoRichClaim61Lemma611
open Erdos547b.ZhaoSourceDegreeFormRootRows Erdos547b.ZhaoSourceDegreeFormBounds
open Erdos547b.ZhaoSourceEmbeddingHost Erdos547b.ZhaoSourceOnlineMatchingRoot
open Erdos547b.ZhaoSourceParentCleanup Erdos547b.ZhaoSourceActualChunkEmbedding
open Erdos547b.ZhaoSourceActualPendingPlan Erdos547b.ZhaoSourceFreshChunkBounds
open Erdos547b.ZhaoSourcePendingInterval Erdos547b.ZhaoLemma58DynamicBatchAppend
open Erdos547b.ZhaoLemma58ThresholdResidualCapacity

variable {α : ℚ} {hostN q M : ℕ}
variable {G : SimpleGraph (Fin hostN)} [DecidableRel G.Adj]
variable (W : Witness α q M G) (Q : Certificate W)
variable (S : CleanSourceWitness W Q) (C : Index W)
variable {b r : ℕ} (F : OrderedRootedForest b) (owner : Fin b → Fin r)
variable (D : PendingChunk W Q S C F owner)

theorem PendingChunk.closedDomain (n : ℕ) (howners : ∀ i ∈ D.items, (owner i).val < n) :
    prefixSelected D.items (ownerCutoff (listOwner owner D.items) n) = D.items.toFinset := by
  rw [prefixSelected_ownerCutoff D.items owner D.owner_mono n]
  exact Finset.filter_eq_self.mpr (fun i hi => howners i (List.mem_toFinset.mp hi))

/-- Closing changes only the domain proof, not the underlying copy maps. -/
def PendingChunk.closePlacement (rootImage : Fin r → Fin hostN) (n : ℕ)
    (E : D.Prefix W Q S C F owner rootImage n) (howners : ∀ i ∈ D.items, (owner i).val < n) :
    BranchPlacement F (embeddingHost W) D.items.toFinset (fun i => rootImage (owner i))
      (fun e => residualSide (edgeWhole W Q e) (deleted W Q e)) :=
  castPlacement W Q F owner (D.closedDomain W Q S C F owner n howners) (D.placement W Q S C F owner E)

theorem PendingChunk.close_copy (rootImage : Fin r → Fin hostN) (n : ℕ)
    (E : D.Prefix W Q S C F owner rootImage n) (howners : ∀ i ∈ D.items, (owner i).val < n)
    (i : Fin b) (hi : i ∈ D.items.toFinset) :
    (D.closePlacement W Q S C F owner rootImage n E howners).forestCopy.componentCopy i hi =
      (D.placement W Q S C F owner E).forestCopy.componentCopy i
        ((D.closedDomain W Q S C F owner n howners).symm ▸ hi) := rfl

theorem PendingChunk.close_edge (rootImage : Fin r → Fin hostN) (n : ℕ)
    (E : D.Prefix W Q S C F owner rootImage n) (howners : ∀ i ∈ D.items, (owner i).val < n)
    (i : {i // i ∈ D.items.toFinset}) :
    (D.closePlacement W Q S C F owner rootImage n E howners).edge i = D.edge := rfl

theorem PendingChunk.close_root_positive (rootImage : Fin r → Fin hostN) (n : ℕ)
    (E : D.Prefix W Q S C F owner rootImage n) (howners : ∀ i ∈ D.items, (owner i).val < n)
    (i : {i // i ∈ D.items.toFinset}) :
    let P := D.closePlacement W Q S C F owner rootImage n E howners
    0 < rootDensity W S (Sum.inl C) (edgeVertex W Q (P.edge i) (P.orient i 0)) := by
  exact D.plan.root_positive (position D.items i.1 (List.mem_toFinset.mp i.2))

/-- Build a fresh closed chunk using the actual source parameters and one
already chosen root, retaining the root-endpoint support in the output. -/
theorem exists_fresh_closed_placement
    (hα : 0 < α) (hα1 : α ≤ 1 / 4)
    (hhost : hostN = 2 * q) (horder : orderThreshold α M ≤ q)
    (hC : C = Q.A ∨ C = Q.B)
    (e : MatchingEdge Q.claim67.M)
    (he : e ∈ edgesAwayFromDistinguished Q.claim67.M (padFinset (large W))
      (Sum.inl Q.A) (Sum.inl Q.B))
    (items : List (Fin b)) (hnd : items.Nodup)
    (hmono : Monotone (listOwner owner items))
    (hsmall : ∀ i, F.size i ≤ freshBranchBound α W.clusterSize)
    (hmass : mass (fun i => (F.size i : ℝ)) items ≤ partOneCapacity W Q S C e)
    (rootImage : Fin r → Fin hostN) (z : Fin hostN) (hz : EligibleRoot W Q S C e z)
    (hparent : ∀ i ∈ items, rootImage (owner i) = z) :
    ∃ P : BranchPlacement F (embeddingHost W) items.toFinset (fun i => rootImage (owner i))
        (fun e => residualSide (edgeWhole W Q e) (deleted W Q e)),
      (∀ i, P.edge i = e) ∧
      ∀ i, 0 < rootDensity W S (Sum.inl C) (edgeVertex W Q (P.edge i) (P.orient i 0)) := by
  obtain ⟨plan⟩ := exists_actual_pending_plan W Q hα hα1 hhost horder S C hC e
    (listForest F items) (fun i => hsmall items[i.val]) (by rw [listForest_order]; exact hmass)
  let D : PendingChunk W Q S C F owner := ⟨e, he, items, hnd, hmono, hmass, plan⟩
  let parent := fun i : Fin items.length => rootImage (listOwner owner items i)
  let available := residualSide (edgeWhole W Q e) (deleted W Q e)
  let initial := castPartialSelected (listForest F items) (embeddingHost W) parent plan.orient available
    (branchPrefix_zero items.length).symm
    (emptyPartial (listForest F items) (embeddingHost W) parent plan.orient available)
  obtain ⟨E, _⟩ := plan.extend_interval W Q parent 0 items.length (Nat.zero_le _) le_rfl initial z hz
    (by intro i _ _; exact hparent _ (List.get_mem items i))
  have hE : D.Prefix W Q S C F owner rootImage r := by
    simpa only [PendingChunk.Prefix, D, ownerCutoff_full] using E
  let P := D.closePlacement W Q S C F owner rootImage r hE (fun i _ => (owner i).isLt)
  exact ⟨P, fun _ => rfl, D.close_root_positive W Q S C F owner rootImage r hE (fun i _ => (owner i).isLt)⟩

end Erdos547b.ZhaoSourceActiveChunk

#print axioms Erdos547b.ZhaoSourceActiveChunk.PendingChunk.close_copy
#print axioms Erdos547b.ZhaoSourceActiveChunk.PendingChunk.close_edge
#print axioms Erdos547b.ZhaoSourceActiveChunk.PendingChunk.close_root_positive
#print axioms Erdos547b.ZhaoSourceActiveChunk.exists_fresh_closed_placement
