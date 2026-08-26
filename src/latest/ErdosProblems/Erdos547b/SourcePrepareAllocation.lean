/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.SourceFamilySourceFacts
import ErdosProblems.Erdos547b.SourceFamilyOwnerAdvance

/-!
# Completing the old reserved prefix before fresh allocation

A current-owner branch in the unreserved suffix forces every old reserved
owner to be at most the current one. Advance the old active prefix, join
it to the reparented completed placement, and retain the source ledger
and every earlier original-index image.
-/

open scoped SimpleGraph BigOperators Classical
noncomputable section

namespace Erdos547b.ZhaoSourcePrepareAllocation

open Finset SimpleGraph Erdos547b.RegularPair
open Erdos547b.ZhaoSourceOriginalBranchPlacement Erdos547b.ZhaoSourcePendingPlacement
open Erdos547b.ZhaoSourceReservationFamilyState Erdos547b.ZhaoSourceFamilyOwnerAdvance
open Erdos547b.ZhaoSourceSaturatedPacking Erdos547b.ZhaoSourceResidualRootPacking
open Erdos547b.ZhaoStability Erdos547b.ZhaoDegreeForm Erdos547b.ZhaoEvenReducedPadding
open Erdos547b.ZhaoLemma611Full Erdos547b.ZhaoSourceDegreeFormRootRows
open Erdos547b.ZhaoSourceEmbeddingHost Erdos547b.ZhaoSourceOnlineMatchingRoot
open Erdos547b.ZhaoSourceParentCleanup Erdos547b.ZhaoSourceActualChunkEmbedding
open Erdos547b.ZhaoSourceFreshChunkBounds Erdos547b.ZhaoLemma58ThresholdResidualCapacity

variable {α : ℚ} {hostN q M : ℕ}
variable {G : SimpleGraph (Fin hostN)} [DecidableRel G.Adj]
variable (W : Witness α q M G) (Q : Certificate W)
variable (S : CleanSourceWitness W Q) (C : Index W)
variable {b r : ℕ} (F : OrderedRootedForest b) (owner : Fin b → Fin r)
variable {all : Finset (MatchingEdge Q.claim67.M)} {family : List (Fin b)}
variable (rootImage : Fin r → Fin hostN) (n : Fin r)
variable (A : FamilyState W Q S C F owner all family rootImage n.val)

structure PreparedAllocation (z : Fin hostN) where
  placement : BranchPlacement F (embeddingHost W) (A.reservedItems W Q S C F owner).toFinset
    (fun i => Function.update rootImage n z (owner i))
    (fun e => residualSide (edgeWhole W Q e) (deleted W Q e))
  edge_mem : ∀ i, placement.edge i ∈ A.reservedEdges W Q S C F owner
  root_positive : ∀ i, 0 < rootDensity W S (Sum.inl C)
    (edgeVertex W Q (placement.edge i) (placement.orient i 0))
  old_mem : family.toFinset.filter (fun i => (owner i).val < n.val) ⊆
    (A.reservedItems W Q S C F owner).toFinset
  old_copies : ∀ i hi, placement.forestCopy.componentCopy i (old_mem hi) =
    (A.currentPlacement W Q S C F owner).forestCopy.componentCopy i hi
  owners_before : ∀ i ∈ A.reservedItems W Q S C F owner, (owner i).val < n.val + 1
  ledger : (∑ e ∈ A.reservedEdges W Q S C F owner,
    (partOneCapacity W Q S C e - freshBranchBound α W.clusterSize)) ≤
      mass (fun i => (F.size i : ℝ)) (A.reservedItems W Q S C F owner)

/-- Finish all old reservations before placing unreserved branches of the
current owner. The graph output is constructed, not an input certificate. -/
theorem exists_preparedAllocation (z : Fin hostN)
    (hcurrent : ∃ i ∈ A.remaining, owner i = n)
    (heligible : ∀ x, A.active = some x → (∃ i ∈ x.1.items, owner i = n) →
      EligibleRoot W Q S C x.1.edge z) :
    Nonempty (PreparedAllocation W Q S C F owner rootImage n A z) := by
  obtain ⟨R⟩ := exists_activeAdvance W Q S C F owner rootImage n z A.active heligible
  let root' := Function.update rootImage n z
  have hbefore := A.reserved_before_succ_of_current W Q S C F owner n hcurrent
  have hactiveFull : activeSelected W Q S C F owner R.after =
      (activeItems W Q S C F owner A.active).toFinset := by
    rw [activeSelected_eq_filter, R.items_eq]
    apply Finset.filter_eq_self.mpr
    intro i hi
    exact hbefore i (List.mem_append_right _ (List.mem_toFinset.mp hi))
  have hagrees : ∀ i ∈ A.completed.toFinset, root' (owner i) = rootImage (owner i) := by
    intro i hi
    have hlt := A.completed_before i (List.mem_toFinset.mp hi)
    exact Function.update_of_ne (fun h => (Nat.ne_of_lt hlt) (congrArg Fin.val h)) z rootImage
  let closed := A.closed.reparent (fun i => root' (owner i)) hagrees
  let active := activePlacement W Q S C F owner R.after
  have hsupport : ∀ i : {i // i ∈ A.completed.toFinset},
      ∀ j : {j // j ∈ activeSelected W Q S C F owner R.after}, ∀ c d,
        Disjoint (residualSide (edgeWhole W Q (closed.edge i)) (deleted W Q (closed.edge i)) c)
          (residualSide (edgeWhole W Q (active.edge j)) (deleted W Q (active.edge j)) d) := by
    intro i j c d
    have hi := A.closed_edge_mem i
    have hj := activePlacement_edge_mem W Q S C F owner R.after j
    rw [R.edges_eq] at hj
    have hne : closed.edge i ≠ active.edge j := by
      intro heq
      exact Finset.disjoint_left.mp A.edge_disjoint hi (heq.symm ▸ hj)
    exact (edgeWhole_cross_disjoint W Q _ _ hne c d).mono Finset.sdiff_subset Finset.sdiff_subset
  let joined := closed.append active hsupport
  have hdomain : A.completed.toFinset ∪ activeSelected W Q S C F owner R.after =
      (A.reservedItems W Q S C F owner).toFinset := by
    simp only [FamilyState.reservedItems, List.toFinset_append, hactiveFull]
  let P := castPlacement W Q F owner (rootImage := root') hdomain joined
  have hsourceDisjoint : Disjoint A.completed.toFinset (activeSelected W Q S C F owner R.after) := by
    rw [hactiveFull]
    exact A.completed_active_items_disjoint W Q S C F owner
  have hOldMem : family.toFinset.filter (fun i => (owner i).val < n.val) ⊆
      (A.reservedItems W Q S C F owner).toFinset := by
    intro i hi
    have hm : i ∈ A.completed.toFinset ∪ activeSelected W Q S C F owner A.active :=
      (A.domain_eq W Q S C F owner).symm ▸ hi
    rcases Finset.mem_union.mp hm with hc | ha
    · exact hdomain ▸ Finset.mem_union_left _ hc
    · exact hdomain ▸ Finset.mem_union_right _ (R.selected_mono ha)
  refine ⟨{
    placement := P
    edge_mem := ?_
    root_positive := ?_
    old_mem := hOldMem
    old_copies := ?_
    owners_before := hbefore
    ledger := A.ledger_of_current W Q S C F owner n hcurrent }⟩
  · intro i
    have hi : i.1 ∈ A.completed.toFinset ∪ activeSelected W Q S C F owner R.after := hdomain.symm ▸ i.2
    by_cases hc : i.1 ∈ A.completed.toFinset
    · have he := Finset.mem_union_left (activeEdges W Q S C F owner A.active) (A.closed_edge_mem ⟨i.1, hc⟩)
      simpa only [P, castPlacement, joined, BranchPlacement.append, dif_pos hc,
        closed, BranchPlacement.reparent] using he
    · have ha := (Finset.mem_union.mp hi).resolve_left hc
      have he := activePlacement_edge_mem W Q S C F owner R.after ⟨i.1, ha⟩
      rw [R.edges_eq] at he
      simpa only [P, castPlacement, joined, BranchPlacement.append, dif_neg hc, active] using
        Finset.mem_union_right A.closedEdges he
  · intro i
    have hi : i.1 ∈ A.completed.toFinset ∪ activeSelected W Q S C F owner R.after := hdomain.symm ▸ i.2
    by_cases hc : i.1 ∈ A.completed.toFinset
    · simpa only [P, castPlacement, joined, BranchPlacement.append, dif_pos hc,
        closed, BranchPlacement.reparent] using A.closed_root_positive ⟨i.1, hc⟩
    · have ha := (Finset.mem_union.mp hi).resolve_left hc
      simpa only [P, castPlacement, joined, BranchPlacement.append, dif_neg hc, active] using
        activePlacement_root_positive W Q S C F owner R.after ⟨i.1, ha⟩
  · intro i hi
    have hm : i ∈ A.completed.toFinset ∪ activeSelected W Q S C F owner A.active :=
      (A.domain_eq W Q S C F owner).symm ▸ hi
    rcases Finset.mem_union.mp hm with hc | ha
    · calc
        _ = closed.forestCopy.componentCopy i hc := closed.append_copy_left active hsupport i hc
        _ = A.closed.forestCopy.componentCopy i hc := rfl
        _ = _ := (A.current_copy_completed W Q S C F owner i hc).symm
    · calc
        _ = active.forestCopy.componentCopy i (R.selected_mono ha) :=
          closed.append_copy_right active hsupport hsourceDisjoint i (R.selected_mono ha)
        _ = (activePlacement W Q S C F owner A.active).forestCopy.componentCopy i ha := R.copies_eq i ha
        _ = _ := (A.current_copy_active W Q S C F owner i ha).symm

end Erdos547b.ZhaoSourcePrepareAllocation

#print axioms Erdos547b.ZhaoSourcePrepareAllocation.exists_preparedAllocation
