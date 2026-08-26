/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.SourcePendingReservation
import ErdosProblems.Erdos547b.SourceMatchingPendingPlan
import ErdosProblems.Erdos547b.SourceResidualRootPacking

/-!
# An actual fresh reservation with only its current tail embedded

Look ahead in source indices to freeze the whole chunk, construct its
actual source pending plan, and copy just the current owner's tail with
the already selected root. Future parent-map values are unconstrained and
no graph copies or degree certificates for future owners are inputs.
-/

open scoped SimpleGraph Classical
noncomputable section

namespace Erdos547b.ZhaoSourceMatchingReservation

open Finset SimpleGraph Erdos547b.RegularPair
open Erdos547b.ZhaoStability Erdos547b.ZhaoDegreeForm Erdos547b.ZhaoEvenReducedPadding
open Erdos547b.ZhaoLemma611Full Erdos547b.ZhaoSourceParameterSchedule
open Erdos547b.ZhaoSourceDegreeFormBounds Erdos547b.ZhaoSourceDegreeFormRootRows
open Erdos547b.ZhaoSourceEmbeddingHost Erdos547b.ZhaoSourceMatchingGeometry
open Erdos547b.ZhaoSourceMatchingRootSelection Erdos547b.ZhaoSourceMatchingParentCleanup
open Erdos547b.ZhaoSourceFreshChunkBounds Erdos547b.ZhaoSourceMatchingPendingPlan
open Erdos547b.ZhaoSourcePendingReservation Erdos547b.ZhaoSourcePendingInterval
open Erdos547b.ZhaoSourceResidualRootPacking Erdos547b.ZhaoSourceSaturatedPacking
open Erdos547b.ZhaoLemma58DynamicBatchAppend Erdos547b.ZhaoLemma58ThresholdResidualCapacity

variable {α : ℚ} {hostN q M : ℕ}
variable {G : SimpleGraph (Fin hostN)} [DecidableRel G.Adj]
variable (W : Witness α q M G) (Q : Certificate W)
variable (P : (padGraph (reduced W)).Subgraph)

structure ActualReservation (S : CleanSourceWitness W Q) (C : Index W)
    (e : MatchingEdge P) {b : ℕ} (F : OrderedRootedForest b)
    (parent : Fin b → Fin hostN) (pending future : List (Fin b)) where
  reservation : PendingReservation (fun i => (F.size i : ℝ)) pending future
    (capacity W Q P S C e) (freshBranchBound α W.clusterSize)
  plan : ActualPendingPlan W Q P S C e (listForest F reservation.reserved)
  currentCopy : PartialDynamicAttachedForestEmbedding (listForest F reservation.reserved)
    (embeddingHost W) (fun i => parent reservation.reserved[i.val]) plan.orient
    (residualSide (pairWhole W P e) (deleted W Q P e)) (branchPrefix pending.length)

/-- Construct the reserved list and its fixed plan before copying the
current tail. Only the currently chosen root needs actual eligibility. -/
theorem exists_actualReservation
    (hα : 0 < α) (hα1 : α ≤ 1 / 4)
    (hhost : hostN = 2 * q) (horder : orderThreshold α M ≤ q)
    (S : CleanSourceWitness W Q) (C : Index W) (hC : C = Q.A ∨ C = Q.B)
    (e : MatchingEdge P) {b : ℕ} (F : OrderedRootedForest b)
    (parent : Fin b → Fin hostN) (pending future : List (Fin b))
    (hsmall : ∀ i, F.size i ≤ freshBranchBound α W.clusterSize)
    (hcap : (freshBranchBound α W.clusterSize : ℝ) < capacity W Q P S C e)
    (hpending : mass (fun i => (F.size i : ℝ)) pending ≤
      capacity W Q P S C e - freshBranchBound α W.clusterSize)
    (z : Fin hostN) (hz : EligibleRoot W Q S P C e z)
    (hparent : ∀ i ∈ pending, parent i = z) :
    Nonempty (ActualReservation W Q P S C e F parent pending future) := by
  obtain ⟨R⟩ := exists_pendingReservation (fun i => (F.size i : ℝ)) pending future
    (capacity W Q P S C e) (freshBranchBound α W.clusterSize)
    (Nat.cast_nonneg _) hcap (fun i _ => ⟨Nat.cast_nonneg _, by exact_mod_cast hsmall i⟩) hpending
  have hmass : ((listForest F R.reserved).order : ℝ) ≤ capacity W Q P S C e := by
    rw [listForest_order]
    exact R.fits
  obtain ⟨pendingPlan⟩ := exists_actual_pending_plan W Q P hα hα1 hhost horder S C hC e
    (listForest F R.reserved) (fun i => hsmall R.reserved[i.val]) hmass
  let p := fun i : Fin R.reserved.length => parent R.reserved[i.val]
  let available := residualSide (pairWhole W P e) (deleted W Q P e)
  let initial := castPartialSelected (listForest F R.reserved) (embeddingHost W) p pendingPlan.orient available
    (branchPrefix_zero R.reserved.length).symm
    (emptyPartial (listForest F R.reserved) (embeddingHost W) p pendingPlan.orient available)
  have hlength : pending.length ≤ R.reserved.length := by
    simp only [PendingReservation.reserved, List.length_append]
    omega
  have hcurrent : ∀ i : Fin R.reserved.length, 0 ≤ i.val → i.val < pending.length → p i = z := by
    intro i _ hi
    change parent ((pending ++ future.take R.count)[i.val]) = z
    rw [List.getElem_append_left hi]
    exact hparent _ (List.getElem_mem hi)
  obtain ⟨E, _⟩ := pendingPlan.extend_interval W Q P p 0 pending.length (Nat.zero_le _) hlength initial z hz hcurrent
  exact ⟨⟨R, pendingPlan, E⟩⟩

end Erdos547b.ZhaoSourceMatchingReservation

#print axioms Erdos547b.ZhaoSourceMatchingReservation.exists_actualReservation
