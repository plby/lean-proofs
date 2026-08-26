import ErdosProblems.Erdos118.Reused591.AtomicReplay
import Mathlib.Data.List.Forall2

namespace Erdos118.Reused591

/-!
# Retaining the numerical budget after deleting labels

Coarsening an atomic block keeps its side and word coordinate and only
deletes label values. The entire input list is a subsequence of the
original input. More importantly, its spacing certificate retains the
original finite history set and original label-size budget.
-/

namespace Erdos591.Positive.Game.Atomic

structure Atom.Coarsens (a A : Atom) : Prop where
  side_eq : a.side = A.side
  value_eq : a.value = A.value
  label_subset : a.label ⊆ A.label

theorem Atom.Coarsens.inputs_subset {a A : Atom} (h : a.Coarsens A) :
    a.inputs ⊆ A.inputs := by
  intro x hx
  rcases List.mem_append.mp hx with hx | hx
  · apply List.mem_append_left
    simpa only [Finset.mem_sort] using h.label_subset (by simpa only [Finset.mem_sort] using hx)
  · have heq : x = a.value := by simpa using hx
    exact heq ▸ h.value_eq.symm ▸ A.value_mem

theorem Atom.Coarsens.inputs_sublist {a A : Atom} (h : a.Coarsens A) :
    List.Sublist a.inputs A.inputs := by
  have hsub : a.label.sort (· ≤ ·) ⊆ A.label.sort (· ≤ ·) := by
    intro x hx
    simpa only [Finset.mem_sort] using h.label_subset (by simpa only [Finset.mem_sort] using hx)
  have hlist : List.Sublist (a.label.sort (· ≤ ·)) (A.label.sort (· ≤ ·)) :=
    List.sublist_of_subperm_of_pairwise
      (List.subperm_of_subset (Finset.sortedLT_sort a.label).pairwise.nodup hsub)
      (Finset.sortedLT_sort a.label).pairwise (Finset.sortedLT_sort A.label).pairwise
  exact hlist.append (by simp [h.value_eq])

def Coarsens (xs ys : List Atom) : Prop := List.Forall₂ Atom.Coarsens xs ys

theorem Coarsens.inputs_sublist {xs ys : List Atom} (h : Coarsens xs ys) :
    List.Sublist (inputs xs) (inputs ys) := by
  induction h with
  | nil => exact List.Sublist.refl []
  | cons hab _ ih => exact hab.inputs_sublist.append ih

theorem Coarsens.inputs_subset {xs ys : List Atom} (h : Coarsens xs ys) :
    (inputs xs).toFinset ⊆ (inputs ys).toFinset := by
  intro x hx
  exact List.mem_toFinset.mpr (h.inputs_sublist.subset (List.mem_toFinset.mp hx))

theorem Coarsens.increasing {xs ys : List Atom} (h : Coarsens xs ys)
    (hy : (inputs ys).Pairwise (· < ·)) : (inputs xs).Pairwise (· < ·) :=
  hy.sublist h.inputs_sublist

theorem spaced_nil {N : Set ℕ} (bound : Concrete.Hist N → ℕ) (F : Finset ℕ) :
    Spaced bound F [] := by
  intro front a tail heq
  have hn := congrArg List.length heq
  simp at hn

theorem spaced_cons {N : Set ℕ} {bound : Concrete.Hist N → ℕ}
    {F : Finset ℕ} {a : Atom} {xs : List Atom}
    (hhead : ∃ F' q, F ⊆ F' ∧ a.label.card ≤ q ∧
      ∀ x ∈ a.inputs, ReplayBudget.bound N bound F' q < x)
    (htail : Spaced bound (F ∪ a.inputs.toFinset) xs) : Spaced bound F (a :: xs) := by
  intro front b tail heq
  cases front with
  | nil =>
      have hab : a = b := (List.cons.inj heq).1
      subst b
      simpa using hhead
  | cons c front =>
      have hh : a = c ∧ xs = front ++ b :: tail := List.cons.inj heq
      obtain ⟨rfl, hh⟩ := hh
      obtain ⟨F', q, hF, hq, hx⟩ := htail front b tail hh
      refine ⟨F', q, ?_, hq, hx⟩
      simpa [Finset.union_assoc] using hF

/-- Deleted label values do not invalidate the original retrospective
bound: the coarsened history uses fewer old numbers and asks for no
more labels than the original atomic block. -/
theorem Coarsens.spaced {N : Set ℕ} {bound : Concrete.Hist N → ℕ}
    {xs ys : List Atom} (h : Coarsens xs ys) {F E : Finset ℕ} (hFE : F ⊆ E)
    (hy : Spaced bound E ys) : Spaced bound F xs := by
  induction h generalizing F E with
  | nil => exact spaced_nil bound F
  | @cons a A xs ys ha htail ih =>
      obtain ⟨E', q, hE, hq, hx⟩ := hy [] A ys rfl
      have hEE' : E ⊆ E' := by simpa using hE
      apply spaced_cons
      · refine ⟨E', q, hFE.trans hEE', (Finset.card_le_card ha.label_subset).trans hq, ?_⟩
        intro x hxa
        exact hx x (ha.inputs_subset hxa)
      · apply ih
          (Finset.union_subset_union hFE (fun x hx =>
            List.mem_toFinset.mpr (ha.inputs_subset (List.mem_toFinset.mp hx))))
        simpa using Spaced.tail (front := [A]) hy

/-- Retain a subsequence of construction atoms, deleting arbitrary
label values in each retained atom. This also omits construction work
on branches that do not belong to the pair being replayed. -/
inductive Selects : List Atom → List Atom → Prop
  | nil : Selects [] []
  | drop (A : Atom) {xs ys : List Atom} (h : Selects xs ys) : Selects xs (A :: ys)
  | keep {a A : Atom} {xs ys : List Atom} (ha : a.Coarsens A) (h : Selects xs ys) :
      Selects (a :: xs) (A :: ys)

theorem Selects.inputs_sublist {xs ys : List Atom} (h : Selects xs ys) :
    List.Sublist (inputs xs) (inputs ys) := by
  induction h with
  | nil => exact List.Sublist.refl []
  | drop A _ ih =>
      exact ih.trans (List.sublist_append_right A.inputs (inputs _))
  | keep ha _ ih => exact ha.inputs_sublist.append ih

theorem Selects.spaced {N : Set ℕ} {bound : Concrete.Hist N → ℕ}
    {xs ys : List Atom} (h : Selects xs ys) {F E : Finset ℕ} (hFE : F ⊆ E)
    (hy : Spaced bound E ys) : Spaced bound F xs := by
  induction h generalizing F E with
  | nil => exact spaced_nil bound F
  | @drop A xs ys h ih =>
      apply ih (hFE.trans Finset.subset_union_left)
      simpa using Spaced.tail (front := [A]) hy
  | @keep a A xs ys ha h ih =>
      obtain ⟨E', q, hE, hq, hx⟩ := hy [] A ys rfl
      have hEE' : E ⊆ E' := by simpa using hE
      apply spaced_cons
      · refine ⟨E', q, hFE.trans hEE', (Finset.card_le_card ha.label_subset).trans hq, ?_⟩
        exact fun x hxa => hx x (ha.inputs_subset hxa)
      · apply ih
          (Finset.union_subset_union hFE (fun x hx =>
            List.mem_toFinset.mpr (ha.inputs_subset (List.mem_toFinset.mp hx))))
        simpa using Spaced.tail (front := [A]) hy

#print axioms Coarsens.inputs_sublist
#print axioms Coarsens.spaced
#print axioms Selects.spaced

end Erdos591.Positive.Game.Atomic

end Erdos118.Reused591
