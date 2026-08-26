import ErdosProblems.Erdos591.GameCoarsening
import ErdosProblems.Erdos591.LegalMetadata

/-!
# Recovering structural cursor data independently of labels

Erasing every label preserves all parser counters and coordinates.
This is a specialization of the existing cursor coarsening relation,
not a replacement parser or a relaxed legality rule.
-/

namespace Erdos591.Positive.Game.LabeledWord

def zeroAtoms (xs : List (Finset ℕ × ℕ)) : List (Finset ℕ × ℕ) :=
  xs.map fun a => (∅, a.2)

theorem zeroAtoms_eq_map_values (xs : List (Finset ℕ × ℕ)) :
    zeroAtoms xs = (xs.map Prod.snd).map (fun n => (∅, n)) := by
  simp [zeroAtoms]

theorem Coarsens.erase_run {c f last : LabeledWord} (h : Coarsens c f)
    {xs : List (Finset ℕ × ℕ)} (hf : f.runAtoms xs = some last) :
    ∃ z, c.runAtoms (zeroAtoms xs) = some z ∧ Coarsens z last := by
  induction xs generalizing c f with
  | nil =>
      have heq : f = last := Option.some.inj hf
      exact ⟨c, rfl, heq ▸ h⟩
  | cons a xs ih =>
      cases hr : f.read a.1 a.2 with
      | none => simp [runAtoms, hr] at hf
      | some u =>
          have htail : u.runAtoms xs = some last := by simpa [runAtoms, hr] using hf
          let v := c.record ∅ a.2 u.parser
          have hc : c.read ∅ a.2 = some v := by
            simp [LabeledWord.read, h.parser_eq, (read_spec hr).1, v]
          obtain ⟨z, hz, hlast⟩ := ih (h.read (Finset.empty_subset _) hc hr) htail
          refine ⟨z, ?_, hlast⟩
          simpa [zeroAtoms, runAtoms, hc] using hz

/-- Any independent execution of the erased coordinate word has the
same structural counters as the given fine-labeled execution. -/
theorem Coarsens.compare_erased {c f z last : LabeledWord} (h : Coarsens c f)
    {xs : List (Finset ℕ × ℕ)} (hf : f.runAtoms xs = some last)
    (hc : c.runAtoms ((xs.map Prod.snd).map fun n => (∅, n)) = some z) : Coarsens z last := by
  obtain ⟨v, hv, hvl⟩ := h.erase_run hf
  rw [zeroAtoms_eq_map_values] at hv
  have heq : z = v := Option.some.inj (hc.symm.trans hv)
  exact heq.symm ▸ hvl

#print axioms Coarsens.erase_run
#print axioms Coarsens.compare_erased

end Erdos591.Positive.Game.LabeledWord

namespace Erdos591.Positive.Game.LabeledCode

theorem unlabeled_atoms (s : List (List ℕ)) :
    atoms ∅ (s.map fun a => (∅, a)) =
      (Erdos591.Negative.Exact.word s).map (fun n => (∅, n)) := by
  simp [atoms, bodiesAtoms, bodyAtoms, Erdos591.Negative.Exact.word,
    Erdos591.Negative.Exact.levelWord, List.map_flatMap, List.flatMap_map]

theorem unlabeled_run (s : List (List ℕ)) :
    LabeledWord.initial.runAtoms ((Erdos591.Negative.Exact.word s).map fun n => (∅, n)) =
      some (terminalCursor ∅ (s.map fun a => (∅, a))) := by
  rw [← unlabeled_atoms]
  exact run_atoms ∅ _

theorem complete_unlabeled_coarsens {xs : List (Finset ℕ × ℕ)} {v : LabeledWord}
    (hv : LabeledWord.initial.runAtoms xs = some v) (s : List (List ℕ))
    (hs : Erdos591.Negative.Exact.word s = v.coordinates) :
    LabeledWord.Coarsens (terminalCursor ∅ (s.map fun a => (∅, a))) v := by
  have hvalues : xs.map Prod.snd = Erdos591.Negative.Exact.word s := by
    simpa [LabeledWord.initial] using (LabeledWord.runAtoms_coordinates hv).symm.trans hs.symm
  exact (LabeledWord.Coarsens.refl LabeledWord.initial).compare_erased hv
    (by simpa [hvalues] using unlabeled_run s)

/-- Every legal complete word has exactly one stored body label per
decoded body. The literal marker counts determine this equality. -/
theorem complete_bodyLabels_length {xs : List (Finset ℕ × ℕ)} {v : LabeledWord}
    (hv : LabeledWord.initial.runAtoms xs = some v) (s : List (List ℕ))
    (hs : Erdos591.Negative.Exact.word s = v.coordinates) : v.bodyLabels.length = s.length := by
  simpa [terminalCursor] using (complete_unlabeled_coarsens hv s hs).body_length.symm

theorem complete_rootMarker {xs : List (Finset ℕ × ℕ)} {v : LabeledWord}
    (hv : LabeledWord.initial.runAtoms xs = some v) (s : List (List ℕ))
    (hs : Erdos591.Negative.Exact.word s = v.coordinates) : v.rootMarker = s.length := by
  simpa [terminalCursor] using (complete_unlabeled_coarsens hv s hs).rootMarker_eq.symm

#print axioms unlabeled_run
#print axioms complete_bodyLabels_length

end Erdos591.Positive.Game.LabeledCode
