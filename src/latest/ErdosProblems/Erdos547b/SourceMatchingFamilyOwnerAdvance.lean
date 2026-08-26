/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.SourceMatchingFamilyState
import ErdosProblems.Erdos547b.SourceFamilyOwnerAdvance

/-!
# Actual family-owner advancement without new allocation

If this owner's branches are already reserved, its step advances the
active prefix (or skips an irrelevant chunk) and reparents completed
copies. Source lists and the reservation ledger are unchanged, and every
earlier original-index image is preserved.
-/

open scoped SimpleGraph Classical
noncomputable section

namespace Erdos547b.ZhaoSourceMatchingFamilyOwnerAdvance

open Finset SimpleGraph Erdos547b.RegularPair
open Erdos547b.ZhaoSourceOriginalBranchPlacement Erdos547b.ZhaoSourcePendingPlacement
open Erdos547b.ZhaoSourceSortedBranchOrder Erdos547b.ZhaoSourcePendingOwnerInterval
open Erdos547b.ZhaoSourceMatchingActiveChunk Erdos547b.ZhaoSourceMatchingFamilyState
open Erdos547b.ZhaoStability Erdos547b.ZhaoDegreeForm Erdos547b.ZhaoEvenReducedPadding
open Erdos547b.ZhaoLemma611Full Erdos547b.ZhaoSourceDegreeFormRootRows
open Erdos547b.ZhaoSourceEmbeddingHost Erdos547b.ZhaoSourceMatchingRootSelection
open Erdos547b.ZhaoSourceMatchingParentCleanup Erdos547b.ZhaoSourceMatchingGeometry
open Erdos547b.ZhaoLemma58ThresholdResidualCapacity

variable {α : ℚ} {hostN q M : ℕ}
variable {G : SimpleGraph (Fin hostN)} [DecidableRel G.Adj]
variable (W : Witness α q M G) (Q : Certificate W)
variable (S : CleanSourceWitness W Q) (P : (padGraph (reduced W)).Subgraph) (C : Index W)
variable {b r : ℕ} (F : OrderedRootedForest b) (owner : Fin b → Fin r)

structure ActiveAdvance (rootImage : Fin r → Fin hostN) (n : Fin r) (z : Fin hostN)
    (before : Option (Active W Q S P C F owner rootImage n.val)) where
  after : Option (Active W Q S P C F owner (Function.update rootImage n z) (n.val + 1))
  items_eq : activeItems W Q S P C F owner after = activeItems W Q S P C F owner before
  edges_eq : activeEdges W Q S P C F owner after = activeEdges W Q S P C F owner before
  selected_mono : activeSelected W Q S P C F owner before ⊆ activeSelected W Q S P C F owner after
  copies_eq : ∀ i hi, (activePlacement W Q S P C F owner after).forestCopy.componentCopy i (selected_mono hi) =
    (activePlacement W Q S P C F owner before).forestCopy.componentCopy i hi

theorem exists_activeAdvance (rootImage : Fin r → Fin hostN) (n : Fin r) (z : Fin hostN)
    (before : Option (Active W Q S P C F owner rootImage n.val))
    (heligible : ∀ x, before = some x → (∃ i ∈ x.1.items, owner i = n) →
      EligibleRoot W Q S P C x.1.edge z) :
    Nonempty (ActiveAdvance W Q S P C F owner rootImage n z before) := by
  cases before with
  | none =>
      exact ⟨{
        after := none
        items_eq := rfl
        edges_eq := rfl
        selected_mono := Finset.Subset.refl _
        copies_eq := fun i hi => (Finset.notMem_empty i hi).elim }⟩
  | some x =>
      have hnext : ∃ E' : x.1.Prefix W Q S P C F owner (Function.update rootImage n z) (n.val + 1),
          ∀ i hi, E'.forestCopy.componentCopy i
              (Erdos547b.ZhaoSourcePendingInterval.branchPrefix_mono
                (ownerCutoff_mono (listOwner owner x.1.items) (Nat.le_succ n.val)) hi) =
            x.2.forestCopy.componentCopy i hi := by
        by_cases hc : ∃ i ∈ x.1.items, owner i = n
        · exact x.1.exists_advance W Q S P C F owner rootImage n x.2 z (heligible x rfl hc)
        · apply x.1.exists_skip W Q S P C F owner rootImage n x.2 z
          intro i hi howner
          exact hc ⟨i, hi, howner⟩
      obtain ⟨E', hE'⟩ := hnext
      refine ⟨{
        after := some ⟨x.1, E'⟩
        items_eq := rfl
        edges_eq := rfl
        selected_mono := prefixSelected_mono x.1.items
          (ownerCutoff_mono (listOwner owner x.1.items) (Nat.le_succ n.val))
        copies_eq := ?_ }⟩
      exact x.1.placement_preserved W Q S P C F owner rootImage (Function.update rootImage n z)
        (Nat.le_succ n.val) x.2 E' hE'

open Erdos547b.ZhaoSourceFamilyOwnerAdvance (processedFamily_mono)

/-- A complete actual family transition when no current-owner branches
remain unreserved. In particular, root-only steps are genuine transitions. -/
theorem exists_familyAdvance_noAllocation
    {all : Finset (MatchingEdge P)} {family : List (Fin b)}
    (rootImage : Fin r → Fin hostN) (n : Fin r)
    (A : FamilyState W Q S P C F owner all family rootImage n.val) (z : Fin hostN)
    (hremaining : ∀ i ∈ A.remaining, owner i ≠ n)
    (heligible : ∀ x, A.active = some x → (∃ i ∈ x.1.items, owner i = n) →
      EligibleRoot W Q S P C x.1.edge z) :
    ∃ B : FamilyState W Q S P C F owner all family (Function.update rootImage n z) (n.val + 1),
      B.completed = A.completed ∧ B.remaining = A.remaining ∧ B.closedEdges = A.closedEdges ∧
      activeItems W Q S P C F owner B.active = activeItems W Q S P C F owner A.active ∧
      activeEdges W Q S P C F owner B.active = activeEdges W Q S P C F owner A.active ∧
      ∀ i hi, (B.currentPlacement W Q S P C F owner).forestCopy.componentCopy i
          (processedFamily_mono owner (Nat.le_succ n.val) family hi) =
        (A.currentPlacement W Q S P C F owner).forestCopy.componentCopy i hi := by
  obtain ⟨R⟩ := exists_activeAdvance W Q S P C F owner rootImage n z A.active heligible
  let parent' := fun i => Function.update rootImage n z (owner i)
  have hagrees : ∀ i ∈ A.completed.toFinset, parent' i = rootImage (owner i) := by
    intro i hi
    have hlt := A.completed_before i (List.mem_toFinset.mp hi)
    have hne : owner i ≠ n := fun h => (Nat.ne_of_lt hlt) (congrArg Fin.val h)
    exact Function.update_of_ne hne z rootImage
  let B : FamilyState W Q S P C F owner all family (Function.update rootImage n z) (n.val + 1) := {
    matching := A.matching
    family_nodup := A.family_nodup
    family_order := A.family_order
    completed := A.completed
    active := R.after
    remaining := A.remaining
    flatten := by rw [R.items_eq]; exact A.flatten
    completed_before := fun i hi => Nat.lt_succ_of_lt (A.completed_before i hi)
    remaining_after := by
      intro i hi
      have hle := A.remaining_after i hi
      have hne : (owner i).val ≠ n.val := fun h => hremaining i hi (Fin.ext h)
      omega
    closedEdges := A.closedEdges
    closed_subset := A.closed_subset
    active_subset := by rw [R.edges_eq]; exact A.active_subset
    edge_disjoint := by rw [R.edges_eq]; exact A.edge_disjoint
    closed := A.closed.reparent parent' hagrees
    closed_edge_mem := A.closed_edge_mem
    closed_root_positive := A.closed_root_positive
    reserved_ledger := by
      intro hne
      rw [R.items_eq, R.edges_eq]
      exact A.reserved_ledger hne }
  refine ⟨B, rfl, rfl, rfl, R.items_eq, R.edges_eq, ?_⟩
  intro i hi
  have hdomain : i ∈ A.completed.toFinset ∪ activeSelected W Q S P C F owner A.active :=
    (A.domain_eq W Q S P C F owner).symm ▸ hi
  rcases Finset.mem_union.mp hdomain with hclosed | hactive
  · calc
      _ = B.closed.forestCopy.componentCopy i hclosed :=
        B.current_copy_completed W Q S P C F owner i hclosed
      _ = A.closed.forestCopy.componentCopy i hclosed := rfl
      _ = _ := (A.current_copy_completed W Q S P C F owner i hclosed).symm
  · calc
      _ = (activePlacement W Q S P C F owner R.after).forestCopy.componentCopy i
          (R.selected_mono hactive) :=
        B.current_copy_active W Q S P C F owner i (R.selected_mono hactive)
      _ = (activePlacement W Q S P C F owner A.active).forestCopy.componentCopy i hactive :=
        R.copies_eq i hactive
      _ = _ := (A.current_copy_active W Q S P C F owner i hactive).symm

end Erdos547b.ZhaoSourceMatchingFamilyOwnerAdvance

#print axioms Erdos547b.ZhaoSourceMatchingFamilyOwnerAdvance.exists_activeAdvance
#print axioms Erdos547b.ZhaoSourceMatchingFamilyOwnerAdvance.exists_familyAdvance_noAllocation
