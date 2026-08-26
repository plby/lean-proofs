/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.SourceBranchPlacementExtension
import ErdosProblems.Erdos547b.SourcePendingInterval

/-!
# Original-index placement of an actual active pending prefix

Use each original branch's fixed first occurrence in the reserved list.
This transports copies, roots and colours without selecting new images.
The occurrence is independent of prefix length, so an image-preserving
prefix extension induces an image-preserving original-index extension.
-/

open scoped SimpleGraph Classical
noncomputable section

namespace Erdos547b.ZhaoSourcePendingPlacement

open Finset SimpleGraph Erdos547b.RegularPair
open Erdos547b.ZhaoSourceOriginalBranchPlacement Erdos547b.ZhaoSourceResidualRootPacking
open Erdos547b.ZhaoSourcePendingInterval Erdos547b.ZhaoLemma58DynamicBatchAppend

def prefixSelected {b : ℕ} (items : List (Fin b)) (n : ℕ) : Finset (Fin b) :=
  (items.take n).toFinset

theorem prefixSelected_mem_items {b n : ℕ} {items : List (Fin b)} {i : Fin b}
    (hi : i ∈ prefixSelected items n) : i ∈ items :=
  List.mem_of_mem_take (List.mem_toFinset.mp hi)

theorem prefixSelected_mono {b a c : ℕ} (items : List (Fin b)) (h : a ≤ c) :
    prefixSelected items a ⊆ prefixSelected items c := by
  intro i hi
  have hm := prefixSelected_mem_items hi
  apply List.mem_toFinset.mpr
  apply (List.mem_take_iff_idxOf_lt hm).mpr
  exact ((List.mem_take_iff_idxOf_lt hm).mp (List.mem_toFinset.mp hi)).trans_le h

@[simp] theorem prefixSelected_length {b : ℕ} (items : List (Fin b)) :
    prefixSelected items items.length = items.toFinset := by simp [prefixSelected]

def position {b : ℕ} (items : List (Fin b)) (i : Fin b) (hi : i ∈ items) : Fin items.length :=
  ⟨items.idxOf i, List.idxOf_lt_length_iff.mpr hi⟩

theorem get_position {b : ℕ} (items : List (Fin b)) (i : Fin b) (hi : i ∈ items) :
    items[(position items i hi).val] = i := by
  exact List.getElem_idxOf _

theorem position_mem_prefix {b n : ℕ} (items : List (Fin b)) (i : Fin b)
    (hi : i ∈ prefixSelected items n) :
    position items i (prefixSelected_mem_items hi) ∈ branchPrefix n := by
  rw [mem_branchPrefix]
  exact (List.mem_take_iff_idxOf_lt (prefixSelected_mem_items hi)).mp (List.mem_toFinset.mp hi)

private def castBranchCopy {b : ℕ} {V : Type*} (F : OrderedRootedForest b) (H : SimpleGraph V)
    {i j : Fin b} (h : i = j) (f : (F.tree i).Copy H) : (F.tree j).Copy H := h ▸ f

private theorem castBranchCopy_apply {b : ℕ} {V : Type*}
    (F : OrderedRootedForest b) (H : SimpleGraph V)
    {i j : Fin b} (h : i = j) (f : (F.tree i).Copy H) (a : Fin (F.size j)) :
    castBranchCopy F H h f a = f (Fin.cast (congrArg F.size h.symm) a) := by
  subst j
  rfl

private theorem castBranchCopy_attach {b : ℕ} {V : Type*}
    (F : OrderedRootedForest b) (H : SimpleGraph V) (parent : Fin b → V)
    {i j : Fin b} (h : i = j) (f : (F.tree i).Copy H)
    (hattach : H.Adj (parent i) (f (F.root i))) :
    H.Adj (parent j) (castBranchCopy F H h f (F.root j)) := by
  subst j
  exact hattach

private theorem castBranchCopy_map_side {b : ℕ} {V : Type*}
    (F : OrderedRootedForest b) (H : SimpleGraph V)
    {i j : Fin b} (h : i = j) (f : (F.tree i).Copy H)
    (orient : Fin 2 ≃ Fin 2) (available : Fin 2 → Finset V)
    (hside : ∀ a, f a ∈ available (orient ((F.isTree i).coloringTwoOfVert (F.root i) a))) :
    ∀ a, castBranchCopy F H h f a ∈ available (orient ((F.isTree j).coloringTwoOfVert (F.root j) a)) := by
  subst j
  exact hside

variable {b : ℕ} {V K : Type*} [Fintype V] [DecidableEq V]
variable (F : OrderedRootedForest b) (H : SimpleGraph V)
variable (items : List (Fin b)) (parent : Fin b → V)
variable (orient : Fin items.length → Fin 2 ≃ Fin 2) (endpoint : K → Fin 2 → Finset V) (e : K)

def originalCopy {n : ℕ}
    (E : PartialDynamicAttachedForestEmbedding (listForest F items) H
      (fun i => parent items[i.val]) orient (endpoint e) (branchPrefix n))
    (i : Fin b) (hi : i ∈ prefixSelected items n) : (F.tree i).Copy H :=
  castBranchCopy F H (get_position items i (prefixSelected_mem_items hi))
    (E.forestCopy.componentCopy (position items i (prefixSelected_mem_items hi))
      (position_mem_prefix items i hi))

theorem originalCopy_apply {n : ℕ}
    (E : PartialDynamicAttachedForestEmbedding (listForest F items) H
      (fun i => parent items[i.val]) orient (endpoint e) (branchPrefix n))
    (i : Fin b) (hi : i ∈ prefixSelected items n) (a : Fin (F.size i)) :
    originalCopy F H items parent orient endpoint e E i hi a =
      E.forestCopy.componentCopy (position items i (prefixSelected_mem_items hi))
        (position_mem_prefix items i hi)
        (Fin.cast (congrArg F.size (get_position items i (prefixSelected_mem_items hi)).symm) a) :=
  castBranchCopy_apply F H _ _ a

/-- Pull the active prefix back to original branches with a constant
actual matching-edge assignment and unchanged graph images. -/
def toPlacement {n : ℕ}
    (E : PartialDynamicAttachedForestEmbedding (listForest F items) H
      (fun i => parent items[i.val]) orient (endpoint e) (branchPrefix n)) :
    BranchPlacement F H (prefixSelected items n) parent endpoint where
  edge := fun _ => e
  orient := fun i => orient (position items i.1 (prefixSelected_mem_items i.2))
  forestCopy := {
    componentCopy := originalCopy F H items parent orient endpoint e E
    disjoint_ranges := by
      intro i hi j hj hij
      have hne : position items i (prefixSelected_mem_items hi) ≠
          position items j (prefixSelected_mem_items hj) := by
        intro h
        apply hij
        calc
          i = items[(position items i (prefixSelected_mem_items hi)).val] := (get_position _ _ _).symm
          _ = items[(position items j (prefixSelected_mem_items hj)).val] :=
            congrArg (fun p : Fin items.length => items[p.val]) h
          _ = j := get_position _ _ _
      rw [Set.disjoint_left]
      rintro x ⟨a, rfl⟩ ⟨d, hd⟩
      rw [originalCopy_apply, originalCopy_apply] at hd
      exact Set.disjoint_left.mp (E.forestCopy.disjoint_ranges _ (position_mem_prefix items i hi)
        _ (position_mem_prefix items j hj) hne) ⟨_, rfl⟩ ⟨_, hd⟩ }
  attach := by
    intro i hi
    exact castBranchCopy_attach F H parent (get_position items i (prefixSelected_mem_items hi)) _
      (E.attach (position items i (prefixSelected_mem_items hi)) (position_mem_prefix items i hi))
  map_side := by
    intro i hi a
    exact castBranchCopy_map_side F H (get_position items i (prefixSelected_mem_items hi)) _
      (orient (position items i (prefixSelected_mem_items hi))) (endpoint e)
      (E.map_side (position items i (prefixSelected_mem_items hi)) (position_mem_prefix items i hi)) a

theorem toPlacement_edge {n : ℕ}
    (E : PartialDynamicAttachedForestEmbedding (listForest F items) H
      (fun i => parent items[i.val]) orient (endpoint e) (branchPrefix n))
    (i : {i // i ∈ prefixSelected items n}) :
    (toPlacement F H items parent orient endpoint e E).edge i = e := rfl

/-- Copy preservation is literal after original-index transport, even
when the total parent map changes outside the already placed prefix. -/
theorem toPlacement_copy_of_extension {n m : ℕ} (hnm : n ≤ m) (parent' : Fin b → V)
    (E : PartialDynamicAttachedForestEmbedding (listForest F items) H
      (fun i => parent items[i.val]) orient (endpoint e) (branchPrefix n))
    (E' : PartialDynamicAttachedForestEmbedding (listForest F items) H
      (fun i => parent' items[i.val]) orient (endpoint e) (branchPrefix m))
    (hcopy : ∀ i hi, E'.forestCopy.componentCopy i (branchPrefix_mono hnm hi) =
      E.forestCopy.componentCopy i hi)
    (j : Fin b) (hj : j ∈ prefixSelected items n) :
    (toPlacement F H items parent' orient endpoint e E').forestCopy.componentCopy j
        (prefixSelected_mono items hnm hj) =
      (toPlacement F H items parent orient endpoint e E).forestCopy.componentCopy j hj := by
  ext a
  change originalCopy F H items parent' orient endpoint e E' j (prefixSelected_mono items hnm hj) a =
    originalCopy F H items parent orient endpoint e E j hj a
  rw [originalCopy_apply, originalCopy_apply]
  exact congrArg (fun f => f (Fin.cast
    (congrArg F.size (get_position items j (prefixSelected_mem_items hj)).symm) a))
      (hcopy (position items j (prefixSelected_mem_items hj)) (position_mem_prefix items j hj))

end Erdos547b.ZhaoSourcePendingPlacement

#print axioms Erdos547b.ZhaoSourcePendingPlacement.toPlacement
#print axioms Erdos547b.ZhaoSourcePendingPlacement.toPlacement_edge
#print axioms Erdos547b.ZhaoSourcePendingPlacement.toPlacement_copy_of_extension
