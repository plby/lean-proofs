import ErdosProblems.Erdos118.Reused591.ZeroLabelRun

namespace Erdos118.Reused591

/-!
# Recovering every completed body label from its actual marker read

An erased-label execution identifies the parser state just before a
chosen body marker. The original legal run then supplies the exact
stored label, its strict bounds, and its empty-unselected-body rule.
-/

namespace Erdos591.Positive.Game.LabeledCode

open Erdos591.Negative.Exact

theorem unlabeled_bodies (s : List (List ℕ)) :
    bodiesAtoms (s.map fun a => (∅, a)) =
      (s.flatMap levelWord).map (fun n => (∅, n)) := by
  have h := unlabeled_atoms s
  simp only [atoms, List.length_map, word, List.map_cons] at h
  exact (List.cons.inj h).2

def bodyPrefixCursor (pre rest : List (List ℕ)) : LabeledWord :=
  { parser := .blocks (rest.length + 1)
    coordinates := (pre.length + 1 + rest.length) :: pre.flatMap levelWord
    rootLabel := ∅
    bodyLabels := pre.map fun _ => ∅
    leafIndex := (pre.map List.length).getLastD 0
    rootMarker := pre.length + 1 + rest.length
    bodyMarker := (pre.map List.length).getLastD 0 }

theorem unlabeled_bodyPrefix (pre rest : List (List ℕ)) :
    LabeledWord.initial.runAtoms
      (((pre.length + 1 + rest.length) :: pre.flatMap levelWord).map fun n => (∅, n)) =
        some (bodyPrefixCursor pre rest) := by
  let m := pre.length + 1 + rest.length
  have hb := run_bodies (rootCursor ∅ m) (pre.map fun a => (∅, a)) (rest.length + 1)
    (by simp [rootCursor, m, Nat.add_comm, Nat.add_left_comm])
  simp only [List.map_cons, LabeledWord.runAtoms, read_root, Option.bind_some]
  rw [← unlabeled_bodies]
  simpa [bodyPrefixCursor, rootCursor, erase, m, Function.comp_def] using hb

/-- The label on a specified decoded body obeys the original marker
bound and selection rule. This holds for every body, not just the last
one retained by `CurrentBounds`. -/
theorem complete_body_label {xs : List (Finset ℕ × ℕ)} {v : LabeledWord}
    (h : LabeledWord.LegalRun LabeledWord.initial xs v)
    (pre : List (List ℕ)) (a : List ℕ) (rest : List (List ℕ))
    (hs : word (pre ++ a :: rest) = v.coordinates) :
    (∀ j ∈ v.bodyLabels.getD pre.length ∅, 0 < j ∧ j < a.length) ∧
      (pre.length + 1 ∉ v.rootLabel → v.bodyLabels.getD pre.length ∅ = ∅) := by
  have hvalues : xs.map Prod.snd = word (pre ++ a :: rest) := by
    simpa [LabeledWord.initial] using (LabeledWord.runAtoms_coordinates h.run).symm.trans hs.symm
  have hsplit : xs.map Prod.snd =
      ((pre.length + 1 + rest.length) :: pre.flatMap levelWord) ++
        (a.length :: (a ++ rest.flatMap levelWord)) := by
    simpa [word, levelWord, List.append_assoc, Nat.add_assoc, Nat.add_comm,
      Nat.add_left_comm] using hvalues
  obtain ⟨front, tail, hxs, hfront, htail⟩ := List.map_eq_append_iff.mp hsplit
  rw [hxs] at h
  obtain ⟨w, hw, ht⟩ := h.split
  have hz : LabeledWord.Coarsens (bodyPrefixCursor pre rest) w :=
    (LabeledWord.Coarsens.refl LabeledWord.initial).compare_erased hw.run
      (by rw [hfront]; exact unlabeled_bodyPrefix pre rest)
  have hp : w.parser = .blocks (rest.length + 1) := hz.parser_eq.symm
  have hlen : w.bodyLabels.length = pre.length := by
    simpa [bodyPrefixCursor] using hz.body_length.symm
  obtain ⟨z, ys, htailEq, hn, _⟩ := List.map_eq_cons_iff.mp htail
  rw [htailEq] at ht
  cases ht with
  | cons w D n u ys v hD hr ht =>
      have hn' : n = a.length := hn
      have hslot : v.bodyLabels.getD pre.length ∅ = D := by
        rw [← hlen]
        exact LabeledWord.bodyLabel_after_read hr ht hp
      have hstart : w.parser ≠ .start := by simp [hp]
      have hroot : v.rootLabel = w.rootLabel :=
        (ht.rootLabel_eq (LabeledWord.read_parser_ne_start hr)).trans
          (LabeledWord.read_rootLabel_eq hr hstart)
      rw [hslot]
      constructor
      · rw [← hn']
        exact hD.1
      · intro hnot
        have hempty : w.bodyLabels.length + 1 ∉ w.rootLabel → D = ∅ := by
          simpa [LabeledWord.AllowedLabel, hp] using hD.2
        exact hempty (by simpa [hlen, ← hroot] using hnot)

#print axioms unlabeled_bodyPrefix
#print axioms complete_body_label

end Erdos591.Positive.Game.LabeledCode

end Erdos118.Reused591
