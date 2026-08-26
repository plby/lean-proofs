/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.SourceOwnerListSplit
import ErdosProblems.Erdos547b.SourceMatchingReservation
import ErdosProblems.Erdos547b.SourceMatchingFamilyState

/-!
# Converting a fresh look-ahead reservation to the global-owner state

The current tail has owner `n`, while every future branch has a later
owner. Its already constructed tail copy is therefore exactly the active
chunk's global prefix at `n+1`. No future root image is constrained.
-/

open scoped SimpleGraph Classical
noncomputable section

namespace Erdos547b.ZhaoSourceMatchingReservationToActive

open Finset SimpleGraph Erdos547b.RegularPair
open Erdos547b.ZhaoSourceOwnerListSplit Erdos547b.ZhaoSourceMatchingReservation
open Erdos547b.ZhaoSourcePendingReservation Erdos547b.ZhaoSourcePendingInterval
open Erdos547b.ZhaoSourceSortedBranchOrder Erdos547b.ZhaoSourcePendingOwnerInterval
open Erdos547b.ZhaoSourceMatchingActiveChunk Erdos547b.ZhaoSourceMatchingFamilyState
open Erdos547b.ZhaoSourceSaturatedPacking Erdos547b.ZhaoSourceResidualRootPacking
open Erdos547b.ZhaoStability Erdos547b.ZhaoDegreeForm Erdos547b.ZhaoEvenReducedPadding
open Erdos547b.ZhaoLemma611Full Erdos547b.ZhaoRichClaim61Lemma611
open Erdos547b.ZhaoSourceDegreeFormRootRows Erdos547b.ZhaoSourceDegreeFormBounds
open Erdos547b.ZhaoSourceEmbeddingHost Erdos547b.ZhaoSourceMatchingRootSelection
open Erdos547b.ZhaoSourceMatchingParentCleanup Erdos547b.ZhaoSourceMatchingGeometry
open Erdos547b.ZhaoSourceMatchingPendingPlan
open Erdos547b.ZhaoSourceFreshChunkBounds Erdos547b.ZhaoLemma58ThresholdResidualCapacity

variable {α : ℚ} {hostN q M : ℕ}
variable {G : SimpleGraph (Fin hostN)} [DecidableRel G.Adj]
variable (W : Witness α q M G) (Q : Certificate W)
variable (S : CleanSourceWitness W Q) (P : (padGraph (reduced W)).Subgraph) (C : Index W)
variable {b r : ℕ} (F : OrderedRootedForest b) (owner : Fin b → Fin r)

/-- Construct a fresh active chunk with its actual current-owner prefix.
The returned remaining source suffix has only strictly later owners. -/
theorem exists_lookahead_active
    (hα : 0 < α) (hα1 : α ≤ 1 / 4)
    (hhost : hostN = 2 * q) (horder : orderThreshold α M ≤ q)
    (hC : C = Q.A ∨ C = Q.B)
    (e : MatchingEdge P)
    (he : e ∈ edgesAwayFromDistinguished P (padFinset (large W))
      (Sum.inl Q.A) (Sum.inl Q.B))
    (rootImage : Fin r → Fin hostN) (n : Fin r) (pending future : List (Fin b))
    (hnd : (pending ++ future).Nodup)
    (hordered : (pending ++ future).Pairwise (fun i j => owner i ≤ owner j))
    (hcurrent : ∀ i ∈ pending, owner i = n)
    (hfuture : ∀ i ∈ future, n.val < (owner i).val)
    (hsmall : ∀ i, F.size i ≤ freshBranchBound α W.clusterSize)
    (hcap : (freshBranchBound α W.clusterSize : ℝ) < capacity W Q P S C e)
    (hpending : mass (fun i => (F.size i : ℝ)) pending ≤
      capacity W Q P S C e - freshBranchBound α W.clusterSize)
    (hz : EligibleRoot W Q S P C e (rootImage n)) :
    ∃ R : PendingReservation (fun i => (F.size i : ℝ)) pending future
        (capacity W Q P S C e) (freshBranchBound α W.clusterSize),
      ∃ X : Active W Q S P C F owner rootImage (n.val + 1),
        X.1.items = R.reserved ∧ X.1.edge = e ∧
        ∀ i ∈ R.remaining, n.val < (owner i).val := by
  obtain ⟨A⟩ := exists_actualReservation W Q P hα hα1 hhost horder S C hC e F
    (fun i => rootImage (owner i)) pending future hsmall hcap hpending (rootImage n) hz
    (by intro i hi; rw [hcurrent i hi])
  let R := A.reservation
  have hndR : R.reserved.Nodup :=
    (List.nodup_append.mp (R.flatten.symm ▸ hnd)).1
  have horderR : R.reserved.Pairwise (fun i j => owner i ≤ owner j) :=
    (List.pairwise_append.mp (R.flatten.symm ▸ hordered)).1
  let D : PendingChunk W Q S P C F owner := {
    edge := e
    edge_away := he
    items := R.reserved
    nodup := hndR
    owner_mono := monotone_listOwner_of_pairwise owner R.reserved horderR
    fits := R.fits
    plan := A.plan }
  have hcut : ownerCutoff (listOwner owner R.reserved) (n.val + 1) = pending.length :=
    ownerCutoff_current_append owner n pending (future.take R.count) hcurrent
      (fun i hi => hfuture i (List.mem_of_mem_take hi))
  let E : D.Prefix W Q S P C F owner rootImage (n.val + 1) :=
    castPartialSelected (listForest F R.reserved) (embeddingHost W)
      (fun i => rootImage (owner R.reserved[i.val])) D.plan.orient
      (residualSide (pairWhole W P e) (deleted W Q P e))
      (congrArg (@branchPrefix R.reserved.length) hcut.symm) A.currentCopy
  refine ⟨R, ⟨D, E⟩, rfl, rfl, ?_⟩
  intro i hi
  exact hfuture i (List.mem_of_mem_drop hi)

end Erdos547b.ZhaoSourceMatchingReservationToActive

#print axioms Erdos547b.ZhaoSourceMatchingReservationToActive.exists_lookahead_active
