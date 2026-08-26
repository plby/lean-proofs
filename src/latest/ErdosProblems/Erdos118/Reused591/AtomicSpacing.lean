import ErdosProblems.Erdos118.Reused591.MacroExtension
import ErdosProblems.Erdos118.Reused591.AtomicCoarsening
import ErdosProblems.Erdos118.Reused591.GameSupport

namespace Erdos118.Reused591

/-!
# Composing chronological input certificates

The side of an atom does not affect its numerical input. This lets a
single global construction log be retagged later for any selected pair
of root branches. Concatenation records every newly chosen number once.
-/

namespace Erdos591.Positive.Game

namespace Atomic

theorem inputs_tag (side : Bool) (xs : List (Finset ℕ × ℕ)) :
    inputs (tag side xs) = xs.flatMap (fun a => a.1.sort (· ≤ ·) ++ [a.2]) := by
  simp [tag, inputs, List.flatMap_map, Atom.inputs]

theorem inputs_tag_eq (side side' : Bool) (xs : List (Finset ℕ × ℕ)) :
    inputs (tag side xs) = inputs (tag side' xs) := by rw [inputs_tag, inputs_tag]

theorem Spaced.mono {N : Set ℕ} {b : Concrete.Hist N → ℕ}
    {F E : Finset ℕ} {xs : List Atom} (h : Spaced b E xs) (hFE : F ⊆ E) :
    Spaced b F xs := by
  intro front a tail heq
  obtain ⟨E', q, hE, hq, hx⟩ := h front a tail heq
  exact ⟨E', q, (Finset.union_subset_union hFE (Finset.Subset.refl _)).trans hE, hq, hx⟩

theorem Spaced.append {N : Set ℕ} {b : Concrete.Hist N → ℕ}
    {F : Finset ℕ} {xs ys : List Atom} (hx : Spaced b F xs)
    (hy : Spaced b (F ∪ (inputs xs).toFinset) ys) : Spaced b F (xs ++ ys) := by
  induction xs generalizing F with
  | nil => simpa using hy
  | cons a xs ih =>
      apply spaced_cons
      · simpa using hx [] a xs rfl
      · apply ih (by simpa using hx.tail (front := [a]))
        simpa [Finset.union_assoc] using hy

/-- Relabel the sides without changing any numerical information. -/
def retag (f : Atom → Bool) (xs : List Atom) : List Atom :=
  xs.map fun a => { a with side := f a }

@[simp] theorem inputs_retag (f : Atom → Bool) (xs : List Atom) :
    inputs (retag f xs) = inputs xs := by
  simp only [retag, inputs, List.flatMap_map]
  rfl

theorem Spaced.retag {N : Set ℕ} {b : Concrete.Hist N → ℕ}
    {F : Finset ℕ} {xs : List Atom} (h : Spaced b F xs) (f : Atom → Bool) :
    Spaced b F (retag f xs) := by
  induction xs generalizing F with
  | nil => exact spaced_nil b F
  | cons a xs ih =>
      apply spaced_cons
      · simpa [Atom.inputs] using h [] a xs rfl
      · apply ih
        simpa [Atom.inputs] using h.tail (front := [a])

theorem Spaced.of_retag {N : Set ℕ} {b : Concrete.Hist N → ℕ}
    {F : Finset ℕ} {xs : List Atom} (f : Atom → Bool)
    (h : Spaced b F (Atomic.retag f xs)) : Spaced b F xs := by
  induction xs generalizing F with
  | nil => exact spaced_nil b F
  | cons a xs ih =>
      apply spaced_cons
      · simpa [Atom.inputs] using h [] {a with side := f a} (Atomic.retag f xs) rfl
      · apply ih
        simpa [Atomic.retag, Atom.inputs] using h.tail (front := [{a with side := f a}])

end Atomic

namespace LabeledWord

theorem LegalRun.support_within {w v : LabeledWord} {xs : List (Finset ℕ × ℕ)}
    (h : LegalRun w xs v) (side : Bool) {F : Finset ℕ}
    (hw : w.support ⊆ F) (hxs : ∀ n ∈ Atomic.inputs (Atomic.tag side xs), n ∈ F) :
    v.support ⊆ F := by
  induction h with
  | nil => exact hw
  | cons w D n v xs last _ hr _ ih =>
      have hD : D ⊆ F := by
        intro i hi
        apply hxs i
        simp only [Atomic.tag_cons, Atomic.inputs_cons, Atomic.Atom.inputs,
          List.mem_append, Finset.mem_sort]
        exact Or.inl (Or.inl hi)
      have hn : n ∈ F := by
        apply hxs n
        exact List.mem_append_left _ (Atomic.Atom.value_mem ⟨side, D, n⟩)
      apply ih (read_support_within hw hD hn hr)
      intro i hi
      exact hxs i (List.mem_append_right _ hi)

theorem LegalRun.support {w v : LabeledWord} {xs : List (Finset ℕ × ℕ)}
    (h : LegalRun w xs v) (side : Bool) :
    v.support ⊆ w.support ∪ (Atomic.inputs (Atomic.tag side xs)).toFinset := by
  apply h.support_within side Finset.subset_union_left
  intro n hn
  exact Finset.mem_union_right _ (List.mem_toFinset.mpr hn)

end LabeledWord

#print axioms Atomic.Spaced.append
#print axioms Atomic.Spaced.retag
#print axioms LabeledWord.LegalRun.support

end Erdos591.Positive.Game

end Erdos118.Reused591
