/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.SourceMatchingPrepareAllocation
import ErdosProblems.Erdos547b.SourceMatchingFreshFamily

/-!
# The actual family successor when fresh allocation is needed

Prepend the now-complete old reservation to the freshly constructed suffix
state. The disjoint matching supports preserve injectivity and all old
images. The exact source concatenation and the two disjoint reservation
ledgers give the full successor invariant.
-/

open scoped SimpleGraph BigOperators Classical
noncomputable section

namespace Erdos547b.ZhaoSourceMatchingAllocationAdvance

open Finset SimpleGraph Erdos547b.RegularPair
open Erdos547b.ZhaoSourceMatchingPrepareAllocation Erdos547b.ZhaoSourceMatchingFreshFamily
open Erdos547b.ZhaoSourceMatchingFamilyOwnerAdvance Erdos547b.ZhaoSourceOwnerListSplit
open Erdos547b.ZhaoSourceOriginalBranchPlacement Erdos547b.ZhaoSourceMatchingActiveChunk
open Erdos547b.ZhaoSourceMatchingFamilyState Erdos547b.ZhaoSourceSortedBranchOrder
open Erdos547b.ZhaoSourceSaturatedPacking Erdos547b.ZhaoSourceResidualRootPacking
open Erdos547b.ZhaoStability Erdos547b.ZhaoDegreeForm Erdos547b.ZhaoEvenReducedPadding
open Erdos547b.ZhaoLemma611Full Erdos547b.ZhaoRichClaim61Lemma611
open Erdos547b.ZhaoSourceDegreeFormRootRows Erdos547b.ZhaoSourceDegreeFormBounds
open Erdos547b.ZhaoSourceEmbeddingHost Erdos547b.ZhaoSourceMatchingRootSelection
open Erdos547b.ZhaoSourceMatchingParentCleanup Erdos547b.ZhaoSourceMatchingGeometry
open Erdos547b.ZhaoSourceMatchingPendingPlan
open Erdos547b.ZhaoSourceFamilyOwnerAdvance (processedFamily_mono)
open Erdos547b.ZhaoSourceFreshChunkBounds Erdos547b.ZhaoLemma58ThresholdResidualCapacity

variable {α : ℚ} {hostN q M : ℕ}
variable {G : SimpleGraph (Fin hostN)} [DecidableRel G.Adj]
variable (W : Witness α q M G) (Q : Certificate W)
variable (S : CleanSourceWitness W Q) (P : (padGraph (reduced W)).Subgraph) (C : Index W)
variable {b r : ℕ} (F : OrderedRootedForest b) (owner : Fin b → Fin r)
variable {all : Finset (MatchingEdge P)} {family : List (Fin b)}
variable (rootImage : Fin r → Fin hostN) (n : Fin r)
variable (A : FamilyState W Q S P C F owner all family rootImage n.val)

/-- Paste the constructed old and new states, keeping every earlier image
and adding only disjoint effective-capacity ledgers. -/
theorem exists_prepend_prepared (z : Fin hostN)
    (E : PreparedAllocation W Q S P C F owner rootImage n A z)
    (freshEdges : Finset (MatchingEdge P)) (freshFamily : List (Fin b))
    (B : FamilyState W Q S P C F owner freshEdges freshFamily
      (Function.update rootImage n z) (n.val + 1))
    (hedges : freshEdges ⊆ all \ A.reservedEdges W Q S P C F owner)
    (hfamily : freshFamily = A.remaining) :
    ∃ D : FamilyState W Q S P C F owner all family
        (Function.update rootImage n z) (n.val + 1),
      ∀ i hi, (D.currentPlacement W Q S P C F owner).forestCopy.componentCopy i
          (processedFamily_mono owner (Nat.le_succ n.val) family hi) =
        (A.currentPlacement W Q S P C F owner).forestCopy.componentCopy i hi := by
  let oldItems := A.reservedItems W Q S P C F owner
  let oldEdges := A.reservedEdges W Q S P C F owner
  have holdnew : Disjoint oldEdges (B.closedEdges ∪ activeEdges W Q S P C F owner B.active) := by
    apply Finset.disjoint_left.mpr
    intro e he hn
    have hf : e ∈ freshEdges := by
      rcases Finset.mem_union.mp hn with hc | ha
      · exact B.closed_subset hc
      · exact B.active_subset ha
    exact (Finset.mem_sdiff.mp (hedges hf)).2 he
  have hsupport : ∀ i : {i // i ∈ oldItems.toFinset},
      ∀ j : {j // j ∈ B.completed.toFinset}, ∀ c d,
        Disjoint (residualSide (pairWhole W P (E.placement.edge i))
          (deleted W Q P (E.placement.edge i)) c)
        (residualSide (pairWhole W P (B.closed.edge j)) (deleted W Q P (B.closed.edge j)) d) := by
    intro i j c d
    have hne : E.placement.edge i ≠ B.closed.edge j := by
      intro heq
      exact Finset.disjoint_left.mp holdnew (E.edge_mem i)
        (heq.symm ▸ Finset.mem_union_left _ (B.closed_edge_mem j))
    exact (pairWhole_cross_disjoint W P A.matching _ _ hne c d).mono
      Finset.sdiff_subset Finset.sdiff_subset
  let joined := E.placement.append B.closed hsupport
  have hdomain : oldItems.toFinset ∪ B.completed.toFinset =
      (oldItems ++ B.completed).toFinset := List.toFinset_append.symm
  let closed := castPlacement W Q P F owner
    (rootImage := Function.update rootImage n z) hdomain joined
  have hclosedMem : ∀ i, closed.edge i ∈ oldEdges ∪ B.closedEdges := by
    intro i
    have hi : i.1 ∈ oldItems.toFinset ∪ B.completed.toFinset := hdomain.symm ▸ i.2
    by_cases ho : i.1 ∈ (A.reservedItems W Q S P C F owner).toFinset
    · simpa only [closed, castPlacement, joined, BranchPlacement.append, dif_pos ho] using
        Finset.mem_union_left B.closedEdges (E.edge_mem ⟨i.1, ho⟩)
    · have hb := (Finset.mem_union.mp hi).resolve_left ho
      simpa only [closed, castPlacement, joined, BranchPlacement.append, dif_neg ho] using
        Finset.mem_union_right oldEdges (B.closed_edge_mem ⟨i.1, hb⟩)
  have hclosedPos : ∀ i, 0 < rootDensity W S (Sum.inl C)
      (pairVertex W P (closed.edge i) (closed.orient i 0)) := by
    intro i
    have hi : i.1 ∈ oldItems.toFinset ∪ B.completed.toFinset := hdomain.symm ▸ i.2
    by_cases ho : i.1 ∈ (A.reservedItems W Q S P C F owner).toFinset
    · simpa only [closed, castPlacement, joined, BranchPlacement.append, dif_pos ho] using
        E.root_positive ⟨i.1, ho⟩
    · have hb := (Finset.mem_union.mp hi).resolve_left ho
      simpa only [closed, castPlacement, joined, BranchPlacement.append, dif_neg ho] using
        B.closed_root_positive ⟨i.1, hb⟩
  let D : FamilyState W Q S P C F owner all family
      (Function.update rootImage n z) (n.val + 1) := {
    matching := A.matching
    family_nodup := A.family_nodup
    family_order := A.family_order
    completed := oldItems ++ B.completed
    active := B.active
    remaining := B.remaining
    flatten := by
      rw [List.append_assoc, List.append_assoc, ← List.append_assoc B.completed,
        B.flatten, hfamily]
      exact A.flatten
    completed_before := by
      intro i hi
      rcases List.mem_append.mp hi with ho | hb
      · exact E.owners_before i ho
      · exact B.completed_before i hb
    remaining_after := B.remaining_after
    closedEdges := oldEdges ∪ B.closedEdges
    closed_subset := Finset.union_subset (A.reserved_edges_subset W Q S P C F owner)
      (fun e he => (Finset.mem_sdiff.mp (hedges (B.closed_subset he))).1)
    active_subset := fun e he => (Finset.mem_sdiff.mp (hedges (B.active_subset he))).1
    edge_disjoint := by
      apply Finset.disjoint_left.mpr
      intro e he ha
      rcases Finset.mem_union.mp he with ho | hc
      · exact Finset.disjoint_left.mp holdnew ho (Finset.mem_union_right _ ha)
      · exact Finset.disjoint_left.mp B.edge_disjoint hc ha
    closed := closed
    closed_edge_mem := hclosedMem
    closed_root_positive := hclosedPos
    reserved_ledger := by
      intro hremaining
      rw [Finset.union_assoc, Finset.sum_union holdnew]
      have hl := add_le_add E.ledger (B.reserved_ledger hremaining)
      simpa only [oldItems, oldEdges, FamilyState.reservedItems, mass,
        List.map_append, List.sum_append, add_assoc] using hl }
  refine ⟨D, ?_⟩
  intro i hi
  have ho := E.old_mem hi
  have hd : i ∈ D.completed.toFinset :=
    List.mem_toFinset.mpr (List.mem_append_left _ (List.mem_toFinset.mp ho))
  calc
    _ = D.closed.forestCopy.componentCopy i hd := D.current_copy_completed W Q S P C F owner i hd
    _ = E.placement.forestCopy.componentCopy i ho :=
      E.placement.append_copy_left B.closed hsupport i ho
    _ = _ := E.old_copies i hi

/-- A complete fresh-allocation successor from a finite saturated packing.
All graph copies, including the next active prefix, are constructed here. -/
theorem exists_familyAdvance_withPacking
    (hα : 0 < α) (hα1 : α ≤ 1 / 4)
    (hhost : hostN = 2 * q) (horder : orderThreshold α M ≤ q)
    (hC : C = Q.A ∨ C = Q.B)
    (z : Fin hostN) (hcurrent : ∃ i ∈ A.remaining, owner i = n)
    (heligible : ∀ x, A.active = some x → (∃ i ∈ x.1.items, owner i = n) →
      EligibleRoot W Q S P C x.1.edge z)
    (R : OwnerSplit owner n A.remaining)
    (bins : List (MatchingEdge P))
    (packing : SaturatedPacking bins R.current (fun i => (F.size i : ℝ))
      (capacity W Q P S C) (freshBranchBound α W.clusterSize))
    (hsmall : ∀ i, F.size i ≤ freshBranchBound α W.clusterSize)
    (hunused : bins.toFinset ⊆ all \ A.reservedEdges W Q S P C F owner)
    (haway : ∀ e ∈ bins, e ∈ edgesAwayFromDistinguished P
      (padFinset (large W)) (Sum.inl Q.A) (Sum.inl Q.B))
    (hcap : ∀ e ∈ bins, (freshBranchBound α W.clusterSize : ℝ) < capacity W Q P S C e)
    (hz : ∀ e ∈ bins, EligibleRoot W Q S P C e z) :
    ∃ D : FamilyState W Q S P C F owner all family
        (Function.update rootImage n z) (n.val + 1),
      ∀ i hi, (D.currentPlacement W Q S P C F owner).forestCopy.componentCopy i
          (processedFamily_mono owner (Nat.le_succ n.val) family hi) =
        (A.currentPlacement W Q S P C F owner).forestCopy.componentCopy i hi := by
  obtain ⟨E⟩ := exists_preparedAllocation W Q S P C F owner rootImage n A z hcurrent heligible
  have hnd : A.remaining.Nodup := by
    have hh : (A.reservedItems W Q S P C F owner ++ A.remaining).Nodup :=
      A.flatten.symm ▸ A.family_nodup
    exact (List.nodup_append.mp hh).2.1
  obtain ⟨B⟩ := exists_fresh_familyState W Q S P C F owner A.matching hα hα1 hhost horder hC
    (Function.update rootImage n z) n bins R.current R.future packing
    (R.flatten.symm ▸ hnd) (R.flatten.symm ▸ A.remaining_order W Q S P C F owner)
    R.current_owner R.future_after hsmall haway hcap
    (by intro e he; simpa only [Function.update_self] using hz e he)
  exact exists_prepend_prepared W Q S P C F owner rootImage n A z E bins.toFinset
    (R.current ++ R.future) B hunused R.flatten

end Erdos547b.ZhaoSourceMatchingAllocationAdvance

#print axioms Erdos547b.ZhaoSourceMatchingAllocationAdvance.exists_prepend_prepared
#print axioms Erdos547b.ZhaoSourceMatchingAllocationAdvance.exists_familyAdvance_withPacking
