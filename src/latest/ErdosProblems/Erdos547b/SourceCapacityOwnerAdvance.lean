/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.SourceCapacityFamilyRequirements
import ErdosProblems.Erdos547b.SourceFamilyOwnerAdvance

/-!
# Capacity-aware family advancement without fresh allocation

The actual active chunk is advanced or skipped; completed copies are
reparented without changing their maps. Source lists, assigned edges and
the capacity-specific reservation ledger are preserved.
-/

open scoped SimpleGraph Classical
noncomputable section

namespace Erdos547b.ZhaoSourceCapacityOwnerAdvance

open Finset SimpleGraph Erdos547b.RegularPair
open Erdos547b.ZhaoSourceOriginalBranchPlacement Erdos547b.ZhaoSourcePendingPlacement
open Erdos547b.ZhaoSourceSortedBranchOrder Erdos547b.ZhaoSourcePendingOwnerInterval
open Erdos547b.ZhaoSourcePendingInterval Erdos547b.ZhaoSourceCapacityFamilyState
open Erdos547b.ZhaoLemma611Full Erdos547b.ZhaoSourceDegreeFormRootRows
open Erdos547b.ZhaoSourceEmbeddingHost Erdos547b.ZhaoSourceActualChunkEmbedding
open Erdos547b.ZhaoSourceParentCleanup Erdos547b.ZhaoSourceFamilyCapacity
open Erdos547b.ZhaoSourceGeneralizedChunk Erdos547b.ZhaoSourceMixedRootRequirements
open Erdos547b.ZhaoSourceParameterSchedule Erdos547b.ZhaoSourceDegreeFormBounds
open Erdos547b.ZhaoLemma58ThresholdResidualCapacity

variable {α : ℚ} {hostN q M : ℕ}
variable {G : SimpleGraph (Fin hostN)} [DecidableRel G.Adj]
variable (W : Witness α q M G) (Q : Certificate W)
variable (S : CleanSourceWitness W Q) (C : Index W)
variable {b r : ℕ} (F : OrderedRootedForest b) (owner : Fin b → Fin r) (kind : FamilyKind)

structure ActiveAdvance (rootImage : Fin r → Fin hostN) (n : Fin r) (z : Fin hostN)
    (before : Option (ActiveState W Q S C F owner kind rootImage n.val)) where
  after : Option (ActiveState W Q S C F owner kind (Function.update rootImage n z) (n.val + 1))
  items_eq : activeItems W Q S C F owner kind after = activeItems W Q S C F owner kind before
  edges_eq : activeEdges W Q S C F owner kind after = activeEdges W Q S C F owner kind before
  selected_mono : activeSelected W Q S C F owner kind before ⊆ activeSelected W Q S C F owner kind after
  copies_eq : ∀ i hi, (activePlacement W Q S C F owner kind after).forestCopy.componentCopy i (selected_mono hi) =
    (activePlacement W Q S C F owner kind before).forestCopy.componentCopy i hi
  orient_eq : ∀ i hi, (activePlacement W Q S C F owner kind after).orient ⟨i, selected_mono hi⟩ =
    (activePlacement W Q S C F owner kind before).orient ⟨i, hi⟩

theorem exists_activeAdvance
    (hα : 0 < α) (hα1 : α ≤ 1 / 4) (hhost : hostN = 2 * q)
    (horder : orderThreshold α M ≤ q) (hkind : kind.Valid α)
    (rootImage : Fin r → Fin hostN) (n : Fin r) (z : Fin hostN)
    (before : Option (ActiveState W Q S C F owner kind rootImage n.val))
    (heligible : ∀ x, before = some x → (∃ i ∈ x.source.items, owner i = n) →
      requirementGood W Q S C (x.source.requirement W Q S C F owner kind x.copyPrefix) z) :
    Nonempty (ActiveAdvance W Q S C F owner kind rootImage n z before) := by
  cases before with
  | none =>
      exact ⟨{
        after := none
        items_eq := rfl
        edges_eq := rfl
        selected_mono := Finset.Subset.refl _
        copies_eq := fun i hi => (Finset.notMem_empty i hi).elim
        orient_eq := fun i hi => (Finset.notMem_empty i hi).elim }⟩
  | some x =>
      have hnext : ∃ E' : x.source.Prefix W Q S C F owner kind x.backend
          (Function.update rootImage n z) (n.val + 1),
          (∀ i hi, (x.source.chosen W Q S C F owner kind E').state.forestCopy.componentCopy i
              (branchPrefix_mono (ownerCutoff_mono (listOwner owner x.source.items) (Nat.le_succ n.val)) hi) =
            (x.source.chosen W Q S C F owner kind x.copyPrefix).state.forestCopy.componentCopy i hi) ∧
          ∀ i ∈ branchPrefix (ownerCutoff (listOwner owner x.source.items) n.val),
            (x.source.chosen W Q S C F owner kind E').orient i =
              (x.source.chosen W Q S C F owner kind x.copyPrefix).orient i := by
        by_cases hc : ∃ i ∈ x.source.items, owner i = n
        · exact x.source.exists_advance W Q S C F owner kind hα hα1 hhost horder hkind
            rootImage n x.copyPrefix z (heligible x rfl hc)
        · obtain ⟨E', hcopy, horient⟩ := x.source.exists_skip W Q S C F owner kind rootImage n x.copyPrefix z
            (fun i hi he => hc ⟨i, hi, he⟩)
          exact ⟨E', hcopy, fun i _ => horient i⟩
      obtain ⟨E', hcopy, horient⟩ := hnext
      refine ⟨{
        after := some (activeStateOfPrefix W Q S C F owner kind hα hkind x.source x.backend E')
        items_eq := rfl
        edges_eq := rfl
        selected_mono := prefixSelected_mono x.source.items
          (ownerCutoff_mono (listOwner owner x.source.items) (Nat.le_succ n.val))
        copies_eq := ?_
        orient_eq := ?_ }⟩
      · exact x.source.placement_preserved W Q S C F owner kind rootImage (Function.update rootImage n z)
          (Nat.le_succ n.val) x.copyPrefix E' hcopy
      · exact x.source.placement_orient_preserved W Q S C F owner kind rootImage (Function.update rootImage n z)
          (Nat.le_succ n.val) x.copyPrefix E' horient

theorem exists_familyAdvance_noAllocation
    (hα : 0 < α) (hα1 : α ≤ 1 / 4) (hhost : hostN = 2 * q)
    (horder : orderThreshold α M ≤ q) (hkind : kind.Valid α)
    {all : Finset (MatchingEdge Q.claim67.M)} {family : List (Fin b)}
    (rootImage : Fin r → Fin hostN) (n : Fin r)
    (A : FamilyState W Q S C F owner kind all family rootImage n.val) (z : Fin hostN)
    (hremaining : ∀ i ∈ A.remaining, owner i ≠ n)
    (heligible : ∀ x, A.active = some x → (∃ i ∈ x.source.items, owner i = n) →
      requirementGood W Q S C (x.source.requirement W Q S C F owner kind x.copyPrefix) z) :
    ∃ B : FamilyState W Q S C F owner kind all family (Function.update rootImage n z) (n.val + 1),
      B.completed = A.completed ∧ B.remaining = A.remaining ∧ B.closedEdges = A.closedEdges ∧
      activeItems W Q S C F owner kind B.active = activeItems W Q S C F owner kind A.active ∧
      activeEdges W Q S C F owner kind B.active = activeEdges W Q S C F owner kind A.active ∧
      ∀ i hi, (B.currentPlacement W Q S C F owner kind).forestCopy.componentCopy i
          (Erdos547b.ZhaoSourceFamilyOwnerAdvance.processedFamily_mono owner (Nat.le_succ n.val) family hi) =
        (A.currentPlacement W Q S C F owner kind).forestCopy.componentCopy i hi := by
  obtain ⟨R⟩ := exists_activeAdvance W Q S C F owner kind hα hα1 hhost horder hkind
    rootImage n z A.active heligible
  let parent' := fun i => Function.update rootImage n z (owner i)
  have hagrees : ∀ i ∈ A.completed.toFinset, parent' i = rootImage (owner i) := by
    intro i hi
    have hlt := A.completed_before i (List.mem_toFinset.mp hi)
    have hne : owner i ≠ n := fun h => (Nat.ne_of_lt hlt) (congrArg Fin.val h)
    exact Function.update_of_ne hne z rootImage
  let B : FamilyState W Q S C F owner kind all family (Function.update rootImage n z) (n.val + 1) := {
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
  have hdomain : i ∈ A.completed.toFinset ∪ activeSelected W Q S C F owner kind A.active :=
    (A.domain_eq W Q S C F owner kind).symm ▸ hi
  rcases Finset.mem_union.mp hdomain with hclosed | hactive
  · calc
      _ = B.closed.forestCopy.componentCopy i hclosed := B.current_copy_completed W Q S C F owner kind i hclosed
      _ = A.closed.forestCopy.componentCopy i hclosed := rfl
      _ = _ := (A.current_copy_completed W Q S C F owner kind i hclosed).symm
  · calc
      _ = (activePlacement W Q S C F owner kind R.after).forestCopy.componentCopy i
          (R.selected_mono hactive) := B.current_copy_active W Q S C F owner kind i (R.selected_mono hactive)
      _ = (activePlacement W Q S C F owner kind A.active).forestCopy.componentCopy i hactive := R.copies_eq i hactive
      _ = _ := (A.current_copy_active W Q S C F owner kind i hactive).symm

end Erdos547b.ZhaoSourceCapacityOwnerAdvance

#print axioms Erdos547b.ZhaoSourceCapacityOwnerAdvance.exists_activeAdvance
#print axioms Erdos547b.ZhaoSourceCapacityOwnerAdvance.exists_familyAdvance_noAllocation
