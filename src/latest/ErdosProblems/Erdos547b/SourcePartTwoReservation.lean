/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.SourceActualPartTwoPlan
import ErdosProblems.Erdos547b.SourceActualReservation
import ErdosProblems.Erdos547b.SourceChunkClosure

/-!
# Actual balanced reservations and closed branch placements

Source look-ahead retains the larger Part-2 capacity. Only the current
tail is copied, with future outer roots unconstrained. Closed chunks use
the same plan and retain positive source support on original indices.
-/

open scoped SimpleGraph Classical
noncomputable section

namespace Erdos547b.ZhaoSourcePartTwoReservation

open Finset SimpleGraph Erdos547b.RegularPair
open Erdos547b.ZhaoStability Erdos547b.ZhaoDegreeForm Erdos547b.ZhaoEvenReducedPadding
open Erdos547b.ZhaoLemma611Full Erdos547b.ZhaoSourceParameterSchedule
open Erdos547b.ZhaoSourceDegreeFormBounds Erdos547b.ZhaoSourceDegreeFormRootRows
open Erdos547b.ZhaoSourceEmbeddingHost Erdos547b.ZhaoSourceActualChunkEmbedding
open Erdos547b.ZhaoSourceOnlineMatchingRoot Erdos547b.ZhaoSourceParentCleanup
open Erdos547b.ZhaoSourceFreshChunkBounds Erdos547b.ZhaoSourceActualPendingPlan
open Erdos547b.ZhaoSourcePendingReservation Erdos547b.ZhaoSourcePendingInterval
open Erdos547b.ZhaoSourceResidualRootPacking Erdos547b.ZhaoSourceSaturatedPacking
open Erdos547b.ZhaoLemma58DynamicBatchAppend Erdos547b.ZhaoLemma58ThresholdResidualCapacity
open Erdos547b.ZhaoSourceActualPartTwoPlan Erdos547b.ZhaoLemma58GroupedSmallForest
open Erdos547b.ZhaoSourcePendingPlacement Erdos547b.ZhaoSourceOriginalBranchPlacement
open Erdos547b.ZhaoSourceReservationFamilyState

variable {α : ℚ} {hostN q M : ℕ}
variable {G : SimpleGraph (Fin hostN)} [DecidableRel G.Adj]
variable (W : Witness α q M G) (Q : Certificate W)

/-- Source reservation and actual current prefix, with an explicit
capacity instead of a hidden Part-1 restriction. -/
structure CapacityReservation (S : CleanSourceWitness W Q) (C : Index W)
    (e : MatchingEdge Q.claim67.M) {b : ℕ} (F : OrderedRootedForest b)
    (parent : Fin b → Fin hostN) (pending future : List (Fin b)) (capacity : ℝ) where
  reservation : PendingReservation (fun i => (F.size i : ℝ)) pending future
    capacity (freshBranchBound α W.clusterSize)
  plan : ActualPendingPlan W Q S C e (listForest F reservation.reserved)
  currentCopy : PartialDynamicAttachedForestEmbedding (listForest F reservation.reserved)
    (embeddingHost W) (fun i => parent reservation.reserved[i.val]) plan.orient
    (residualSide (edgeWhole W Q e) (deleted W Q e)) (branchPrefix pending.length)

/-- Initializing a literal prefix needs eligibility only for its one
current parent. This helper is independent of the capacity proof. -/
theorem exists_initial_prefix
    (S : CleanSourceWitness W Q) (C : Index W) (e : MatchingEdge Q.claim67.M)
    {b : ℕ} (F : OrderedRootedForest b) (P : ActualPendingPlan W Q S C e F)
    (parent : Fin b → Fin hostN) (n : ℕ) (hn : n ≤ b)
    (z : Fin hostN) (hz : EligibleRoot W Q S C e z)
    (hparent : ∀ i : Fin b, i.val < n → parent i = z) :
    Nonempty (PartialDynamicAttachedForestEmbedding F (embeddingHost W) parent P.orient
      (residualSide (edgeWhole W Q e) (deleted W Q e)) (branchPrefix n)) := by
  let available := residualSide (edgeWhole W Q e) (deleted W Q e)
  let initial := castPartialSelected F (embeddingHost W) parent P.orient available
    (branchPrefix_zero b).symm (emptyPartial F (embeddingHost W) parent P.orient available)
  obtain ⟨E, _⟩ := P.extend_interval W Q parent 0 n (Nat.zero_le _) hn initial z hz
    (fun i _ hi => hparent i hi)
  exact ⟨E⟩

/-- The stronger mass bound constructs a real look-ahead reservation and
its current graph prefix. Ratios are required only on this source family. -/
theorem exists_partTwoReservation
    (hα : 0 < α) (hα1 : α ≤ 1 / 4)
    (hhost : hostN = 2 * q) (horder : orderThreshold α M ≤ q)
    (S : CleanSourceWitness W Q) (C : Index W) (hC : C = Q.A ∨ C = Q.B)
    (e : MatchingEdge Q.claim67.M) {b : ℕ} (F : OrderedRootedForest b)
    (parent : Fin b → Fin hostN) (pending future : List (Fin b))
    (ratio : ℝ) (hratio : 0 ≤ ratio) (hratioHalf : ratio ≤ 1 / 2)
    (hlower : ∀ i ∈ pending ++ future, ratio ≤ (#(colourClass F i 0) : ℝ) / F.size i)
    (hupper : ∀ i ∈ pending ++ future, (#(colourClass F i 0) : ℝ) / F.size i ≤ 1 - ratio)
    (hsmall : ∀ i, F.size i ≤ freshBranchBound α W.clusterSize)
    (hcap : (freshBranchBound α W.clusterSize : ℝ) < partTwoCapacity W Q S C ratio e)
    (hpending : mass (fun i => (F.size i : ℝ)) pending ≤
      partTwoCapacity W Q S C ratio e - freshBranchBound α W.clusterSize)
    (z : Fin hostN) (hz : EligibleRoot W Q S C e z)
    (hparent : ∀ i ∈ pending, parent i = z) :
    Nonempty (CapacityReservation W Q S C e F parent pending future
      (partTwoCapacity W Q S C ratio e)) := by
  obtain ⟨R⟩ := exists_pendingReservation (fun i => (F.size i : ℝ)) pending future
    (partTwoCapacity W Q S C ratio e) (freshBranchBound α W.clusterSize)
    (Nat.cast_nonneg _) hcap (fun i _ => ⟨Nat.cast_nonneg _, by exact_mod_cast hsmall i⟩) hpending
  have hmem (i : Fin R.reserved.length) : R.reserved[i.val] ∈ pending ++ future := by
    have hi := List.getElem_mem (i.isLt)
    change R.reserved[i.val] ∈ pending ++ future
    change R.reserved[i.val] ∈ pending ++ future.take R.count at hi
    rcases List.mem_append.mp hi with h | h
    · exact List.mem_append_left _ h
    · exact List.mem_append_right _ (List.mem_of_mem_take h)
  obtain ⟨P⟩ := exists_actual_partTwo_plan W Q hα hα1 hhost horder S C hC e
    (listForest F R.reserved) ratio hratio hratioHalf
    (fun i => hlower _ (hmem i)) (fun i => hupper _ (hmem i))
    (fun i => hsmall R.reserved[i.val]) (by rw [listForest_order]; exact R.fits)
  have hlength : pending.length ≤ R.reserved.length := by
    simp only [PendingReservation.reserved, List.length_append]
    omega
  obtain ⟨E⟩ := exists_initial_prefix W Q S C e (listForest F R.reserved) P
    (fun i => parent R.reserved[i.val]) pending.length hlength z hz (by
      intro i hi
      change parent ((pending ++ future.take R.count)[i.val]) = z
      rw [List.getElem_append_left hi]
      exact hparent _ (List.getElem_mem hi))
  exact ⟨⟨R, P, E⟩⟩

/-- A saturated balanced chunk can be fully copied at the current root.
The returned original-index placement keeps its positive source support. -/
theorem exists_partTwo_closed_placement
    (hα : 0 < α) (hα1 : α ≤ 1 / 4)
    (hhost : hostN = 2 * q) (horder : orderThreshold α M ≤ q)
    (S : CleanSourceWitness W Q) (C : Index W) (hC : C = Q.A ∨ C = Q.B)
    (e : MatchingEdge Q.claim67.M) {b : ℕ} (F : OrderedRootedForest b)
    (items : List (Fin b)) (parent : Fin b → Fin hostN)
    (ratio : ℝ) (hratio : 0 ≤ ratio) (hratioHalf : ratio ≤ 1 / 2)
    (hlower : ∀ i ∈ items, ratio ≤ (#(colourClass F i 0) : ℝ) / F.size i)
    (hupper : ∀ i ∈ items, (#(colourClass F i 0) : ℝ) / F.size i ≤ 1 - ratio)
    (hsmall : ∀ i, F.size i ≤ freshBranchBound α W.clusterSize)
    (hmass : mass (fun i => (F.size i : ℝ)) items ≤ partTwoCapacity W Q S C ratio e)
    (z : Fin hostN) (hz : EligibleRoot W Q S C e z)
    (hparent : ∀ i ∈ items, parent i = z) :
    ∃ P : BranchPlacement F (embeddingHost W) items.toFinset parent
        (fun e => residualSide (edgeWhole W Q e) (deleted W Q e)),
      (∀ i, P.edge i = e) ∧
      ∀ i, 0 < rootDensity W S (Sum.inl C) (edgeVertex W Q (P.edge i) (P.orient i 0)) := by
  obtain ⟨plan⟩ := exists_actual_partTwo_plan W Q hα hα1 hhost horder S C hC e
    (listForest F items) ratio hratio hratioHalf
    (fun i => hlower _ (List.get_mem items i)) (fun i => hupper _ (List.get_mem items i))
    (fun i => hsmall items[i.val]) (by rw [listForest_order]; exact hmass)
  obtain ⟨E⟩ := exists_initial_prefix W Q S C e (listForest F items) plan
    (fun i => parent items[i.val]) items.length le_rfl z hz
    (fun i _ => hparent _ (List.get_mem items i))
  let original := toPlacement F (embeddingHost W) items parent plan.orient
    (fun e => residualSide (edgeWhole W Q e) (deleted W Q e)) e E
  let P := castPlacement W Q F (fun i => i) (prefixSelected_length items) original
  refine ⟨P, fun _ => rfl, ?_⟩
  intro i
  exact plan.root_positive (position items i.1 (List.mem_toFinset.mp i.2))

end Erdos547b.ZhaoSourcePartTwoReservation

#print axioms Erdos547b.ZhaoSourcePartTwoReservation.exists_initial_prefix
#print axioms Erdos547b.ZhaoSourcePartTwoReservation.exists_partTwoReservation
#print axioms Erdos547b.ZhaoSourcePartTwoReservation.exists_partTwo_closed_placement
