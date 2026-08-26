/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.SourcePendingOwnerInterval
import ErdosProblems.Erdos547b.SourceSaturatedPacking
import Mathlib.Data.List.NodupEquivFin
import Mathlib.Data.List.Sort

/-!
# Owner-sorted source branches and their packed sublists

The arbitrary finite enumeration in the original source adapter need not
preserve owners. Sorting its literal branch indices gives a proved
nondecreasing owner sequence, without modifying any branch. Every chunk
of the saturated packing inherits this order from the flattening identity.
-/

open scoped Classical
noncomputable section

namespace Erdos547b.ZhaoSourceSortedBranchOrder

open Finset Erdos547b.ZhaoSourceSaturatedPacking

def ownerSortedList {b r : ℕ} (owner : Fin b → Fin r) : List (Fin b) :=
  (Finset.univ : Finset (Fin b)).toList.mergeSort (fun i j => decide (owner i ≤ owner j))

theorem ownerSortedList_perm {b r : ℕ} (owner : Fin b → Fin r) :
    (ownerSortedList owner).Perm (Finset.univ : Finset (Fin b)).toList :=
  List.mergeSort_perm _ _

theorem ownerSortedList_nodup {b r : ℕ} (owner : Fin b → Fin r) :
    (ownerSortedList owner).Nodup :=
  (ownerSortedList_perm owner).nodup_iff.mpr (Finset.nodup_toList _)

theorem mem_ownerSortedList {b r : ℕ} (owner : Fin b → Fin r) (i : Fin b) :
    i ∈ ownerSortedList owner :=
  (ownerSortedList_perm owner).mem_iff.mpr (Finset.mem_toList.mpr (Finset.mem_univ _))

@[simp] theorem length_ownerSortedList {b r : ℕ} (owner : Fin b → Fin r) :
    (ownerSortedList owner).length = b := by
  rw [(ownerSortedList_perm owner).length_eq]
  simp

theorem pairwise_ownerSortedList {b r : ℕ} (owner : Fin b → Fin r) :
    (ownerSortedList owner).Pairwise (fun i j => owner i ≤ owner j) := by
  have h := List.pairwise_mergeSort (le := fun i j : Fin b => decide (owner i ≤ owner j))
    (fun i j k hij hjk => by
      simp only [decide_eq_true_eq] at hij hjk ⊢
      exact hij.trans hjk)
    (fun i j => by simp only [Bool.or_eq_true, decide_eq_true_eq]; exact le_total _ _)
    (Finset.univ : Finset (Fin b)).toList
  simpa only [ownerSortedList, decide_eq_true_eq] using h

/-- The sorted list is a genuine equivalence with the original branches. -/
def ownerSortedEquiv {b r : ℕ} (owner : Fin b → Fin r) :
    Fin (ownerSortedList owner).length ≃ Fin b :=
  List.Nodup.getEquivOfForallMemList (ownerSortedList owner)
    (ownerSortedList_nodup owner) (mem_ownerSortedList owner)

def listOwner {b r : ℕ} (owner : Fin b → Fin r) (items : List (Fin b)) :
    Fin items.length → Fin r := fun i => owner (items.get i)

theorem monotone_listOwner_of_pairwise {b r : ℕ} (owner : Fin b → Fin r)
    (items : List (Fin b)) (h : items.Pairwise (fun i j => owner i ≤ owner j)) :
    Monotone (listOwner owner items) := by
  intro i j hij
  rcases lt_or_eq_of_le hij with hlt | rfl
  · exact h.rel_get_of_lt hlt
  · exact le_rfl

theorem monotone_ownerSortedList {b r : ℕ} (owner : Fin b → Fin r) :
    Monotone (listOwner owner (ownerSortedList owner)) :=
  monotone_listOwner_of_pairwise owner _ (pairwise_ownerSortedList owner)

private theorem chunk_sublist_flatMap {Bin Item : Type*}
    (chunks : List (Bin × List Item)) (p : Bin × List Item) (hp : p ∈ chunks) :
    p.2.Sublist (chunks.flatMap Prod.snd) := by
  induction chunks with
  | nil => simp at hp
  | cons a l ih =>
      rcases List.mem_cons.mp hp with h | h
      · subst p
        exact List.sublist_append_left _ _
      · exact (ih h).trans (List.sublist_append_right _ _)

/-- Each packed chunk preserves the literal order of the original list. -/
theorem packing_chunk_sublist
    {Bin Item : Type*} {bins : List Bin} {items : List Item}
    {weight : Item → ℝ} {capacity : Bin → ℝ} {slack : ℝ}
    (P : SaturatedPacking bins items weight capacity slack)
    (p : Bin × List Item) (hp : p ∈ P.closed ++ P.pending.toList) : p.2.Sublist items := by
  have hflat : (P.closed ++ P.pending.toList).flatMap Prod.snd = items := by
    rw [List.flatMap_append]
    exact P.flatten
  rw [← hflat]
  exact chunk_sublist_flatMap _ p hp

/-- The actual closed and pending chunk owner functions are nondecreasing
whenever the source item list was ordered by owner. -/
theorem monotone_packing_chunk_owner
    {Bin : Type*} {b r : ℕ} {bins : List Bin} {items : List (Fin b)}
    {weight : Fin b → ℝ} {capacity : Bin → ℝ} {slack : ℝ}
    (P : SaturatedPacking bins items weight capacity slack)
    (owner : Fin b → Fin r) (horder : items.Pairwise (fun i j => owner i ≤ owner j))
    (p : Bin × List (Fin b)) (hp : p ∈ P.closed ++ P.pending.toList) :
    Monotone (listOwner owner p.2) :=
  monotone_listOwner_of_pairwise owner p.2 (horder.sublist (packing_chunk_sublist P p hp))

end Erdos547b.ZhaoSourceSortedBranchOrder

#print axioms Erdos547b.ZhaoSourceSortedBranchOrder.ownerSortedEquiv
#print axioms Erdos547b.ZhaoSourceSortedBranchOrder.monotone_ownerSortedList
#print axioms Erdos547b.ZhaoSourceSortedBranchOrder.packing_chunk_sublist
#print axioms Erdos547b.ZhaoSourceSortedBranchOrder.monotone_packing_chunk_owner
