/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.SourceCapacityOwnerAdvance

/-!
# Completing the old capacity-aware reservation before fresh allocation

Sorted source owners force every old reserved branch to be current or
earlier when a current branch remains unreserved. Complete the active
prefix, reparent the earlier closed copies, and preserve their exact maps.
-/

open scoped SimpleGraph BigOperators Classical
noncomputable section

namespace Erdos547b.ZhaoSourceCapacityFamilyState

open Finset Erdos547b.RegularPair Erdos547b.ZhaoSourceFamilyCapacity
open Erdos547b.ZhaoLemma611Full Erdos547b.ZhaoSourceDegreeFormRootRows

variable {α : ℚ} {hostN q M : ℕ}
variable {G : SimpleGraph (Fin hostN)} [DecidableRel G.Adj]
variable (W : Witness α q M G) (Q : Certificate W) (S : CleanSourceWitness W Q) (C : Index W)
variable {b r : ℕ} (F : OrderedRootedForest b) (owner : Fin b → Fin r) (kind : FamilyKind)
variable {all : Finset (MatchingEdge Q.claim67.M)} {family : List (Fin b)}
variable {rootImage : Fin r → Fin hostN} {stage : ℕ}
variable (A : FamilyState W Q S C F owner kind all family rootImage stage)

theorem FamilyState.reserved_nodup : (A.reservedItems W Q S C F owner kind).Nodup := by
  have h : (A.completed ++ activeItems W Q S C F owner kind A.active ++ A.remaining).Nodup :=
    A.flatten.symm ▸ A.family_nodup
  exact (List.nodup_append.mp h).1

theorem FamilyState.completed_active_items_disjoint :
    Disjoint A.completed.toFinset (activeItems W Q S C F owner kind A.active).toFinset := by
  have h := (List.nodup_append.mp (A.reserved_nodup W Q S C F owner kind)).2.2
  apply Finset.disjoint_left.mpr
  intro i hi hj
  exact h i (List.mem_toFinset.mp hi) i (List.mem_toFinset.mp hj) rfl

theorem FamilyState.reserved_before_succ_of_current (n : Fin r)
    (hcurrent : ∃ i ∈ A.remaining, owner i = n) :
    ∀ i ∈ A.reservedItems W Q S C F owner kind, (owner i).val < n.val + 1 := by
  obtain ⟨j, hj, howner⟩ := hcurrent
  intro i hi
  have h := A.reserved_before_remaining W Q S C F owner kind i hi j hj
  rw [howner] at h
  exact Nat.lt_succ_of_le h

end Erdos547b.ZhaoSourceCapacityFamilyState

namespace Erdos547b.ZhaoSourceCapacityPrepareAllocation

open Finset SimpleGraph Erdos547b.RegularPair
open Erdos547b.ZhaoSourceOriginalBranchPlacement Erdos547b.ZhaoSourcePendingPlacement
open Erdos547b.ZhaoSourceCapacityFamilyState Erdos547b.ZhaoSourceCapacityOwnerAdvance
open Erdos547b.ZhaoSourceSaturatedPacking Erdos547b.ZhaoSourceResidualRootPacking
open Erdos547b.ZhaoLemma611Full Erdos547b.ZhaoSourceDegreeFormRootRows
open Erdos547b.ZhaoSourceEmbeddingHost Erdos547b.ZhaoSourceActualChunkEmbedding
open Erdos547b.ZhaoSourceParentCleanup Erdos547b.ZhaoSourceFreshChunkBounds
open Erdos547b.ZhaoLemma58ThresholdResidualCapacity Erdos547b.ZhaoSourceFamilyCapacity
open Erdos547b.ZhaoSourceParameterSchedule Erdos547b.ZhaoSourceDegreeFormBounds
open Erdos547b.ZhaoSourceMixedRootRequirements
open Erdos547b.ZhaoSourceReservationFamilyState (castPlacement)

variable {α : ℚ} {hostN q M : ℕ}
variable {G : SimpleGraph (Fin hostN)} [DecidableRel G.Adj]
variable (W : Witness α q M G) (Q : Certificate W) (S : CleanSourceWitness W Q) (C : Index W)
variable {b r : ℕ} (F : OrderedRootedForest b) (owner : Fin b → Fin r) (kind : FamilyKind)
variable {all : Finset (MatchingEdge Q.claim67.M)} {family : List (Fin b)}
variable (rootImage : Fin r → Fin hostN) (n : Fin r)
variable (A : FamilyState W Q S C F owner kind all family rootImage n.val)

structure PreparedAllocation (z : Fin hostN) where
  placement : BranchPlacement F (embeddingHost W) (A.reservedItems W Q S C F owner kind).toFinset
    (fun i => Function.update rootImage n z (owner i))
    (fun e => residualSide (edgeWhole W Q e) (deleted W Q e))
  edge_mem : ∀ i, placement.edge i ∈ A.reservedEdges W Q S C F owner kind
  root_positive : ∀ i, 0 < rootDensity W S (Sum.inl C)
    (edgeVertex W Q (placement.edge i) (placement.orient i 0))
  old_mem : family.toFinset.filter (fun i => (owner i).val < n.val) ⊆
    (A.reservedItems W Q S C F owner kind).toFinset
  old_copies : ∀ i hi, placement.forestCopy.componentCopy i (old_mem hi) =
    (A.currentPlacement W Q S C F owner kind).forestCopy.componentCopy i hi
  owners_before : ∀ i ∈ A.reservedItems W Q S C F owner kind, (owner i).val < n.val + 1
  ledger : (∑ e ∈ A.reservedEdges W Q S C F owner kind,
    (capacity W Q S C kind e - freshBranchBound α W.clusterSize)) ≤
      mass (fun i => (F.size i : ℝ)) (A.reservedItems W Q S C F owner kind)

theorem exists_preparedAllocation
    (hα : 0 < α) (hα1 : α ≤ 1 / 4) (hhost : hostN = 2 * q)
    (horder : orderThreshold α M ≤ q) (hkind : kind.Valid α)
    (z : Fin hostN) (hcurrent : ∃ i ∈ A.remaining, owner i = n)
    (heligible : ∀ x, A.active = some x → (∃ i ∈ x.source.items, owner i = n) →
      requirementGood W Q S C (x.source.requirement W Q S C F owner kind x.copyPrefix) z) :
    Nonempty (PreparedAllocation W Q S C F owner kind rootImage n A z) := by
  obtain ⟨R⟩ := exists_activeAdvance W Q S C F owner kind hα hα1 hhost horder hkind
    rootImage n z A.active heligible
  let root' := Function.update rootImage n z
  have hbefore := A.reserved_before_succ_of_current W Q S C F owner kind n hcurrent
  have hactiveFull : activeSelected W Q S C F owner kind R.after =
      (activeItems W Q S C F owner kind A.active).toFinset := by
    rw [activeSelected_eq_filter, R.items_eq]
    apply Finset.filter_eq_self.mpr
    intro i hi
    exact hbefore i (List.mem_append_right _ (List.mem_toFinset.mp hi))
  have hagrees : ∀ i ∈ A.completed.toFinset, root' (owner i) = rootImage (owner i) := by
    intro i hi
    have hlt := A.completed_before i (List.mem_toFinset.mp hi)
    exact Function.update_of_ne (fun h => (Nat.ne_of_lt hlt) (congrArg Fin.val h)) z rootImage
  let closed := A.closed.reparent (fun i => root' (owner i)) hagrees
  let active := activePlacement W Q S C F owner kind R.after
  have hsupport : ∀ i : {i // i ∈ A.completed.toFinset},
      ∀ j : {j // j ∈ activeSelected W Q S C F owner kind R.after}, ∀ c d,
        Disjoint (residualSide (edgeWhole W Q (closed.edge i)) (deleted W Q (closed.edge i)) c)
          (residualSide (edgeWhole W Q (active.edge j)) (deleted W Q (active.edge j)) d) := by
    intro i j c d
    have hi := A.closed_edge_mem i
    have hj := activePlacement_edge_mem W Q S C F owner kind R.after j
    rw [R.edges_eq] at hj
    have hne : closed.edge i ≠ active.edge j := by
      intro heq
      exact Finset.disjoint_left.mp A.edge_disjoint hi (heq.symm ▸ hj)
    exact (edgeWhole_cross_disjoint W Q _ _ hne c d).mono Finset.sdiff_subset Finset.sdiff_subset
  let joined := closed.append active hsupport
  have hdomain : A.completed.toFinset ∪ activeSelected W Q S C F owner kind R.after =
      (A.reservedItems W Q S C F owner kind).toFinset := by
    simp only [FamilyState.reservedItems, List.toFinset_append, hactiveFull]
  let P := castPlacement W Q F owner (rootImage := root') hdomain joined
  have hsourceDisjoint : Disjoint A.completed.toFinset (activeSelected W Q S C F owner kind R.after) := by
    rw [hactiveFull]
    exact A.completed_active_items_disjoint W Q S C F owner kind
  have hOldMem : family.toFinset.filter (fun i => (owner i).val < n.val) ⊆
      (A.reservedItems W Q S C F owner kind).toFinset := by
    intro i hi
    have hm : i ∈ A.completed.toFinset ∪ activeSelected W Q S C F owner kind A.active :=
      (A.domain_eq W Q S C F owner kind).symm ▸ hi
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
    ledger := A.ledger_of_current W Q S C F owner kind n hcurrent }⟩
  · intro i
    have hi : i.1 ∈ A.completed.toFinset ∪ activeSelected W Q S C F owner kind R.after := hdomain.symm ▸ i.2
    by_cases hc : i.1 ∈ A.completed.toFinset
    · have he := Finset.mem_union_left (activeEdges W Q S C F owner kind A.active) (A.closed_edge_mem ⟨i.1, hc⟩)
      simpa only [P, castPlacement, joined, BranchPlacement.append, dif_pos hc,
        closed, BranchPlacement.reparent] using he
    · have ha := (Finset.mem_union.mp hi).resolve_left hc
      have he := activePlacement_edge_mem W Q S C F owner kind R.after ⟨i.1, ha⟩
      rw [R.edges_eq] at he
      simpa only [P, castPlacement, joined, BranchPlacement.append, dif_neg hc, active] using
        Finset.mem_union_right A.closedEdges he
  · intro i
    have hi : i.1 ∈ A.completed.toFinset ∪ activeSelected W Q S C F owner kind R.after := hdomain.symm ▸ i.2
    by_cases hc : i.1 ∈ A.completed.toFinset
    · simpa only [P, castPlacement, joined, BranchPlacement.append, dif_pos hc,
        closed, BranchPlacement.reparent] using A.closed_root_positive ⟨i.1, hc⟩
    · have ha := (Finset.mem_union.mp hi).resolve_left hc
      simpa only [P, castPlacement, joined, BranchPlacement.append, dif_neg hc, active] using
        activePlacement_root_positive W Q S C F owner kind R.after ⟨i.1, ha⟩
  · intro i hi
    have hm : i ∈ A.completed.toFinset ∪ activeSelected W Q S C F owner kind A.active :=
      (A.domain_eq W Q S C F owner kind).symm ▸ hi
    rcases Finset.mem_union.mp hm with hc | ha
    · calc
        _ = closed.forestCopy.componentCopy i hc := closed.append_copy_left active hsupport i hc
        _ = A.closed.forestCopy.componentCopy i hc := rfl
        _ = _ := (A.current_copy_completed W Q S C F owner kind i hc).symm
    · calc
        _ = active.forestCopy.componentCopy i (R.selected_mono ha) :=
          closed.append_copy_right active hsupport hsourceDisjoint i (R.selected_mono ha)
        _ = (activePlacement W Q S C F owner kind A.active).forestCopy.componentCopy i ha := R.copies_eq i ha
        _ = _ := (A.current_copy_active W Q S C F owner kind i ha).symm

end Erdos547b.ZhaoSourceCapacityPrepareAllocation

#print axioms Erdos547b.ZhaoSourceCapacityFamilyState.FamilyState.reserved_before_succ_of_current
#print axioms Erdos547b.ZhaoSourceCapacityPrepareAllocation.exists_preparedAllocation
