/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.SourceMatchingChunkAssembly
import ErdosProblems.Erdos547b.SourceMatchingReservationToActive
import ErdosProblems.Erdos547b.SourceActualPlacementExtension

/-!
# Constructing a fresh family state from the current-owner packing

Closed chunks are actually embedded with positive source support. A small
pending tail is extended by a source-only look-ahead reservation, whose
current prefix is actually embedded. The terminal unsaturated case is
kept separate from the nonterminal reservation ledger.
-/

open scoped SimpleGraph BigOperators Classical
noncomputable section

namespace Erdos547b.ZhaoSourceMatchingFreshFamily

open Finset SimpleGraph Erdos547b.RegularPair
open Erdos547b.ZhaoSourceMatchingChunkAssembly Erdos547b.ZhaoSourceMatchingReservationToActive
open Erdos547b.ZhaoSourceOriginalBranchPlacement Erdos547b.ZhaoSourceMatchingActiveChunk
open Erdos547b.ZhaoSourceMatchingFamilyState Erdos547b.ZhaoSourceSortedBranchOrder
open Erdos547b.ZhaoSourcePendingReservation Erdos547b.ZhaoSourceActualPlacementExtension
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

/-- Realize the new suffix state, including both possible pending cases.
Only the current prescribed root is required to be eligible. -/
theorem exists_fresh_familyState (hP : P.IsMatching)
    (hα : 0 < α) (hα1 : α ≤ 1 / 4)
    (hhost : hostN = 2 * q) (horder : orderThreshold α M ≤ q)
    (hC : C = Q.A ∨ C = Q.B)
    (rootImage : Fin r → Fin hostN) (n : Fin r)
    (bins : List (MatchingEdge P)) (current future : List (Fin b))
    (packing : SaturatedPacking bins current (fun i => (F.size i : ℝ))
      (capacity W Q P S C) (freshBranchBound α W.clusterSize))
    (hnd : (current ++ future).Nodup)
    (hordered : (current ++ future).Pairwise (fun i j => owner i ≤ owner j))
    (hcurrent : ∀ i ∈ current, owner i = n)
    (hfuture : ∀ i ∈ future, n.val < (owner i).val)
    (hsmall : ∀ i, F.size i ≤ freshBranchBound α W.clusterSize)
    (haway : ∀ e ∈ bins, e ∈ edgesAwayFromDistinguished P
      (padFinset (large W)) (Sum.inl Q.A) (Sum.inl Q.B))
    (hcap : ∀ e ∈ bins, (freshBranchBound α W.clusterSize : ℝ) < capacity W Q P S C e)
    (hz : ∀ e ∈ bins, EligibleRoot W Q S P C e (rootImage n)) :
    Nonempty (FamilyState W Q S P C F owner bins.toFinset (current ++ future)
      rootImage (n.val + 1)) := by
  obtain ⟨closed, hclosedEdges, hclosedPos⟩ := exists_supported_closed_packing W Q S P C F owner
    rootImage hP hα hα1 hhost horder hC bins current packing (List.nodup_append.mp hnd).1
    (List.pairwise_append.mp hordered).1 hsmall haway (rootImage n) hz
    (by intro i hi; rw [hcurrent i hi])
  let closedEdges := (packing.closed.map Prod.fst).toFinset
  have hclosedSubset : closedEdges ⊆ bins.toFinset := by
    intro e he
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp he)
    exact List.mem_toFinset.mpr (packing.bins_mem p (List.mem_append_left _ hp))
  have hclosedBefore : ∀ i ∈ packing.closed.flatMap Prod.snd, (owner i).val < n.val + 1 := by
    intro i hi
    obtain ⟨p, hp, hip⟩ := List.mem_flatMap.mp hi
    have hc := hcurrent i
      (Erdos547b.ZhaoSourceResidualRootPacking.SaturatedPacking.chunk_mem packing (List.mem_append_left _ hp) hip)
    rw [hc]
    exact Nat.lt_succ_self _
  have hledger := closed_saturation_mass packing
  cases hpending : packing.pending with
  | none =>
    have hflat : packing.closed.flatMap Prod.snd = current := by
      simpa only [hpending, Option.toList_none, List.flatMap_nil, List.append_nil] using packing.flatten
    refine ⟨{
      matching := hP
      family_nodup := hnd
      family_order := hordered
      completed := packing.closed.flatMap Prod.snd
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
    have hp : p ∈ packing.closed ++ packing.pending.toList := by
      simp only [hpending, Option.toList_some, List.mem_append, List.mem_singleton]
      exact Or.inr trivial
    have hbin := packing.bins_mem p hp
    have hflat : packing.closed.flatMap Prod.snd ++ p.2 = current := by
      simpa only [hpending, Option.toList_some, List.flatMap_cons, List.flatMap_nil,
        List.append_nil] using packing.flatten
    have hsub : (p.2 ++ future).Sublist (current ++ future) := by
      exact (packing_chunk_sublist packing p hp).append (List.Sublist.refl future)
    obtain ⟨R, X, hXitems, hXedge, hRafter⟩ := exists_lookahead_active W Q S P C F owner
      hα hα1 hhost horder hC p.1 (haway p.1 hbin) rootImage n p.2 future
      (hnd.sublist hsub) (hordered.sublist hsub)
      (fun i hi => hcurrent i
        (Erdos547b.ZhaoSourceResidualRootPacking.SaturatedPacking.chunk_mem packing hp hi))
      hfuture hsmall (hcap p.1 hbin)
      (packing.pending_small p hpending) (hz p.1 hbin)
    have hpNotClosed : p.1 ∉ closedEdges := by
      have hn := packing.bins_nodup
      simp only [hpending, List.map_append, Option.toList_some, List.map_cons,
        List.map_nil] at hn
      intro he
      exact (List.nodup_append.mp hn).2.2 p.1 (List.mem_toFinset.mp he)
        p.1 List.mem_cons_self rfl
    refine ⟨{
      matching := hP
      family_nodup := hnd
      family_order := hordered
      completed := packing.closed.flatMap Prod.snd
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
    · change (packing.closed.flatMap Prod.snd ++ X.1.items) ++ R.remaining = current ++ future
      rw [hXitems, List.append_assoc, R.flatten, ← List.append_assoc, hflat]
    · simpa only [activeEdges, hXedge, Finset.singleton_subset_iff] using
        List.mem_toFinset.mpr hbin
    · simpa only [activeEdges, hXedge, Finset.disjoint_singleton_right] using hpNotClosed
    · intro hremaining
      have hl := R.extend_ledger (capacity W Q P S C) closedEdges p.1 hpNotClosed
        (mass (fun i => (F.size i : ℝ)) (packing.closed.flatMap Prod.snd)) hledger hremaining
      simpa only [activeEdges, hXedge, Finset.union_singleton, activeItems, hXitems,
        mass, List.map_append, List.sum_append] using hl

end Erdos547b.ZhaoSourceMatchingFreshFamily

#print axioms Erdos547b.ZhaoSourceMatchingFreshFamily.exists_fresh_familyState
