/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.SourceCapacityClosedPacking
import ErdosProblems.Erdos547b.SourceCapacityReservationToActive
import ErdosProblems.Erdos547b.SourceActualPlacementExtension

/-!
# Actual fresh family state for threshold and Appendix capacities

All closed chunks are copied on distinct assigned edges. A pending tail
receives a source-only look-ahead reservation and its actual current-owner
prefix. The nonterminal ledger charges the full reserved source mass.
-/

open scoped SimpleGraph BigOperators Classical
noncomputable section

namespace Erdos547b.ZhaoSourceFreshCapacityFamilyState

open Finset SimpleGraph Erdos547b.RegularPair
open Erdos547b.ZhaoStability Erdos547b.ZhaoDegreeForm Erdos547b.ZhaoEvenReducedPadding
open Erdos547b.ZhaoLemma611Full Erdos547b.ZhaoRichClaim61Lemma611
open Erdos547b.ZhaoSourceDegreeFormRootRows Erdos547b.ZhaoSourceDegreeFormBounds
open Erdos547b.ZhaoSourceParameterSchedule Erdos547b.ZhaoSourceFreshChunkBounds
open Erdos547b.ZhaoSourceFamilyCapacity Erdos547b.ZhaoSourceCapacityFamilyState
open Erdos547b.ZhaoSourceCapacityClosedPacking Erdos547b.ZhaoSourceCapacityReservationToActive
open Erdos547b.ZhaoSourceMixedRootRequirements Erdos547b.ZhaoSourceSaturatedPacking
open Erdos547b.ZhaoSourceResidualRootPacking Erdos547b.ZhaoSourceSortedBranchOrder
open Erdos547b.ZhaoSourceOriginalBranchPlacement Erdos547b.ZhaoSourceActualPlacementExtension
open Erdos547b.ZhaoSourceEmbeddingHost Erdos547b.ZhaoSourceActualChunkEmbedding
open Erdos547b.ZhaoSourceParentCleanup Erdos547b.ZhaoLemma58ThresholdResidualCapacity
open Erdos547b.ZhaoSourcePendingReservation

variable {α : ℚ} {hostN q M : ℕ}
variable {G : SimpleGraph (Fin hostN)} [DecidableRel G.Adj]
variable (W : Witness α q M G) (Q : Certificate W)
variable (S : CleanSourceWitness W Q) (C : Index W)
variable {b r : ℕ} (F : OrderedRootedForest b) (owner : Fin b → Fin r) (kind : FamilyKind)

theorem exists_fresh_familyState
    (hα : 0 < α) (hα1 : α ≤ 1 / 4) (hhost : hostN = 2 * q)
    (horder : orderThreshold α M ≤ q) (hC : C = Q.A ∨ C = Q.B) (hkind : kind.Valid α)
    (rootImage : Fin r → Fin hostN) (n : Fin r)
    (bins : List (MatchingEdge Q.claim67.M)) (current future : List (Fin b))
    (P : SaturatedPacking bins current (fun i => (F.size i : ℝ))
      (capacity W Q S C kind) (freshBranchBound α W.clusterSize))
    (hnd : (current ++ future).Nodup)
    (hordered : (current ++ future).Pairwise (fun i j => owner i ≤ owner j))
    (hcurrent : ∀ i ∈ current, owner i = n)
    (hfuture : ∀ i ∈ future, n.val < (owner i).val)
    (hbranch : ∀ i ∈ current ++ future, kind.BranchValid F i)
    (hsmall : ∀ i, F.size i ≤ freshBranchBound α W.clusterSize)
    (haway : ∀ e ∈ bins, e ∈ edgesAwayFromDistinguished Q.claim67.M
      (padFinset (large W)) (Sum.inl Q.A) (Sum.inl Q.B))
    (hedge : ∀ e ∈ bins, edgeValid W Q S C kind e)
    (hcap : ∀ e ∈ bins, (freshBranchBound α W.clusterSize : ℝ) < capacity W Q S C kind e)
    (hz : ∀ e ∈ bins, requirementGood W Q S C (initialRequirement W Q kind e) (rootImage n)) :
    Nonempty (FamilyState W Q S C F owner kind bins.toFinset (current ++ future)
      rootImage (n.val + 1)) := by
  obtain ⟨closed, hclosedEdges, hclosedPos⟩ := exists_supported_closed_packing W Q S C F owner kind
    hα hα1 hhost horder hC hkind rootImage n bins current P (List.nodup_append.mp hnd).1
    (List.pairwise_append.mp hordered).1 hcurrent
    (fun i hi => hbranch i (List.mem_append_left future hi)) hsmall haway hedge hz
  let closedEdges := (P.closed.map Prod.fst).toFinset
  have hclosedSubset : closedEdges ⊆ bins.toFinset := by
    intro e he
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp he)
    exact List.mem_toFinset.mpr (P.bins_mem p (List.mem_append_left _ hp))
  have hclosedBefore : ∀ i ∈ P.closed.flatMap Prod.snd, (owner i).val < n.val + 1 := by
    intro i hi
    obtain ⟨p, hp, hip⟩ := List.mem_flatMap.mp hi
    have hc := hcurrent i
      (Erdos547b.ZhaoSourceResidualRootPacking.SaturatedPacking.chunk_mem P (List.mem_append_left _ hp) hip)
    rw [hc]
    exact Nat.lt_succ_self _
  have hledger := closed_saturation_mass P
  cases hpending : P.pending with
  | none =>
      have hflat : P.closed.flatMap Prod.snd = current := by
        simpa only [hpending, Option.toList_none, List.flatMap_nil, List.append_nil] using P.flatten
      refine ⟨{
        family_nodup := hnd
        family_order := hordered
        completed := P.closed.flatMap Prod.snd
        active := none
        remaining := future
        flatten := ?_
        completed_before := hclosedBefore
        remaining_after := fun i hi => hfuture i hi
        closedEdges := closedEdges
        closed_subset := hclosedSubset
        active_subset := by simp [activeEdges]
        edge_disjoint := by simp [activeEdges]
        closed := closed
        closed_edge_mem := hclosedEdges
        closed_root_positive := hclosedPos
        reserved_ledger := ?_ }⟩
      · simpa only [activeItems, List.append_nil] using congrArg (fun l => l ++ future) hflat
      · intro _
        simpa only [activeEdges, Finset.union_empty, activeItems, List.append_nil] using hledger
  | some p =>
      have hp : p ∈ P.closed ++ P.pending.toList := by
        simp only [hpending, Option.toList_some, List.mem_append, List.mem_singleton]
        exact Or.inr trivial
      have hbin := P.bins_mem p hp
      have hflat : P.closed.flatMap Prod.snd ++ p.2 = current := by
        simpa only [hpending, Option.toList_some, List.flatMap_cons, List.flatMap_nil,
          List.append_nil] using P.flatten
      have hsub : (p.2 ++ future).Sublist (current ++ future) :=
        (packing_chunk_sublist P p hp).append (List.Sublist.refl future)
      obtain ⟨R, X, hXitems, hXedge, hRafter⟩ := exists_lookahead_active W Q S C F owner kind
        hα hα1 hhost horder hC hkind p.1 (haway p.1 hbin) (hedge p.1 hbin) rootImage n p.2 future
        (hnd.sublist hsub) (hordered.sublist hsub)
        (fun i hi => hcurrent i
          (Erdos547b.ZhaoSourceResidualRootPacking.SaturatedPacking.chunk_mem P hp hi))
        hfuture (fun i hi => hbranch i (hsub.subset hi)) hsmall (hcap p.1 hbin)
        (P.pending_small p hpending) (hz p.1 hbin)
      have hpNotClosed : p.1 ∉ closedEdges := by
        have hn := P.bins_nodup
        simp only [hpending, List.map_append, Option.toList_some, List.map_cons, List.map_nil] at hn
        intro he
        exact (List.nodup_append.mp hn).2.2 p.1 (List.mem_toFinset.mp he) p.1 List.mem_cons_self rfl
      refine ⟨{
        family_nodup := hnd
        family_order := hordered
        completed := P.closed.flatMap Prod.snd
        active := some X
        remaining := R.remaining
        flatten := ?_
        completed_before := hclosedBefore
        remaining_after := fun i hi => hRafter i hi
        closedEdges := closedEdges
        closed_subset := hclosedSubset
        active_subset := ?_
        edge_disjoint := ?_
        closed := closed
        closed_edge_mem := hclosedEdges
        closed_root_positive := hclosedPos
        reserved_ledger := ?_ }⟩
      · change (P.closed.flatMap Prod.snd ++ X.source.items) ++ R.remaining = current ++ future
        rw [hXitems, List.append_assoc, R.flatten, ← List.append_assoc, hflat]
      · simpa only [activeEdges, hXedge, Finset.singleton_subset_iff] using List.mem_toFinset.mpr hbin
      · simpa only [activeEdges, hXedge, Finset.disjoint_singleton_right] using hpNotClosed
      · intro hremaining
        have hl := R.extend_ledger (capacity W Q S C kind) closedEdges p.1 hpNotClosed
          (mass (fun i => (F.size i : ℝ)) (P.closed.flatMap Prod.snd)) hledger hremaining
        simpa only [activeEdges, hXedge, Finset.union_singleton, activeItems, hXitems,
          mass, List.map_append, List.sum_append] using hl

end Erdos547b.ZhaoSourceFreshCapacityFamilyState

#print axioms Erdos547b.ZhaoSourceFreshCapacityFamilyState.exists_fresh_familyState
