import ErdosProblems.Erdos591.BodyMetadata

/-!
# Exact canonical recovery of a completed legal atomic word

The final stored body labels decorate the uniquely decoded bodies.
Their legality comes from the original reads, and label persistence
then identifies the whole canonical atom list with the actual input.
-/

namespace Erdos591.Positive.Game.LabeledCode

open Erdos591.Negative.Exact

def decoratedBodies (v : LabeledWord) (s : List (List ℕ)) : List Body :=
  s.mapIdx fun i a => (v.bodyLabels.getD i ∅, a)

@[simp] theorem decoratedBodies_length (v : LabeledWord) (s : List (List ℕ)) :
    (decoratedBodies v s).length = s.length := by simp [decoratedBodies]

@[simp] theorem erase_decoratedBodies (v : LabeledWord) (s : List (List ℕ)) :
    erase (decoratedBodies v s) = s := by
  apply List.ext_getElem
  · simp [erase]
  · intro i hi hj
    simp [erase, decoratedBodies]

theorem decoratedBodies_labels (v : LabeledWord) (s : List (List ℕ))
    (hv : v.bodyLabels.length = s.length) :
    (decoratedBodies v s).map Prod.fst = v.bodyLabels := by
  apply List.ext_getElem
  · simp [hv]
  · intro i hi hj
    simp only [List.getElem_map, decoratedBodies, List.getElem_mapIdx]
    exact List.getD_eq_getElem _ _ hj

theorem lawful_decoratedBodies {xs : List (Finset ℕ × ℕ)} {v : LabeledWord}
    (h : LabeledWord.LegalRun LabeledWord.initial xs v) (s : List (List ℕ))
    (hs : word s = v.coordinates) : LawfulBodies v.rootLabel 0 (decoratedBodies v s) := by
  apply lawfulBodies_of_getElem
  intro i hi
  have hi' : i < s.length := by simpa using hi
  have heq : s.take i ++ s[i] :: s.drop (i + 1) = s := by
    rw [← List.drop_eq_getElem_cons hi', List.take_append_drop]
  have hb := complete_body_label h (s.take i) s[i] (s.drop (i + 1)) (by rw [heq]; exact hs)
  simpa [decoratedBodies, List.length_take, Nat.min_eq_left hi'.le] using hb

theorem legal_decorated_atoms {xs : List (Finset ℕ × ℕ)} {v : LabeledWord}
    (h : LabeledWord.LegalRun LabeledWord.initial xs v) (s : List (List ℕ))
    (hs : word s = v.coordinates) :
    LabeledWord.LegalRun LabeledWord.initial (atoms v.rootLabel (decoratedBodies v s))
      (terminalCursor v.rootLabel (decoratedBodies v s)) := by
  apply legal_atoms
  · have hm := complete_rootMarker h.run s hs
    have hb := (h.cursorInvariant LabeledWord.cursorInvariant_initial).2.2.1
    simpa only [hm, decoratedBodies_length] using hb
  · exact lawful_decoratedBodies h s hs

/-- Recovery of the whole input list, including its original labels,
not merely of its erased coordinate list. -/
theorem canonical_atoms_eq {xs : List (Finset ℕ × ℕ)} {v : LabeledWord}
    (h : LabeledWord.LegalRun LabeledWord.initial xs v) (s : List (List ℕ))
    (hs : word s = v.coordinates) : xs = atoms v.rootLabel (decoratedBodies v s) := by
  apply h.atoms_unique (legal_decorated_atoms h s hs)
  · simpa [terminalCursor] using hs.symm
  · rfl
  · exact (decoratedBodies_labels v s (complete_bodyLabels_length h.run s hs)).symm

theorem canonical_cursor_eq {xs : List (Finset ℕ × ℕ)} {v : LabeledWord}
    (h : LabeledWord.LegalRun LabeledWord.initial xs v) (s : List (List ℕ))
    (hs : word s = v.coordinates) : v = terminalCursor v.rootLabel (decoratedBodies v s) := by
  have hr := h.run
  rw [canonical_atoms_eq h s hs, run_atoms] at hr
  exact Option.some.inj hr.symm

#print axioms lawful_decoratedBodies
#print axioms canonical_atoms_eq
#print axioms canonical_cursor_eq

end Erdos591.Positive.Game.LabeledCode
