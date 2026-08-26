import ErdosProblems.Erdos118.Reused591.ReplyRuns

namespace Erdos118.Reused591

/-!
# Extracting the actual first event from an atomic coordinate prefix

A valid empty-label atomic execution ending at an event contains an
accepted first-event prefix. If its accepted endpoint has the same
parser state as the prescribed endpoint, strict parser-potential
decrease proves that no unused tail remains.
-/

namespace Erdos591.Positive.Game.LabeledWord

theorem legal_of_zero_atoms {w v : LabeledWord} {xs : List ℕ}
    (h : w.runAtoms (xs.map fun n => (∅, n)) = some v) :
    LegalRun w (xs.map fun n => (∅, n)) v := by
  induction xs generalizing w with
  | nil =>
      have heq : w = v := Option.some.inj h
      exact heq ▸ LegalRun.nil w
  | cons n xs ih =>
      cases hr : w.read ∅ n with
      | none => simp [runAtoms, hr] at h
      | some u =>
          have ht : u.runAtoms (xs.map fun n => (∅, n)) = some v := by
            simpa [runAtoms, hr] using h
          exact .cons w ∅ n u _ v (allowed_empty (read_nonterminal hr) n) hr (ih ht)

theorem LegalRun.potential_le {w v : LabeledWord} {xs : List (Finset ℕ × ℕ)}
    (h : LegalRun w xs v) : Parser.potential v.parser ≤ Parser.potential w.parser := by
  induction h with
  | nil => exact le_refl _
  | cons w D n u xs v _ hr _ ih => exact ih.trans (read_decreases hr).le

theorem LegalRun.nil_of_parser_eq {w v : LabeledWord} {xs : List (Finset ℕ × ℕ)}
    (h : LegalRun w xs v) (hp : v.parser = w.parser) : xs = [] := by
  cases h with
  | nil => rfl
  | cons w D n u xs v _ hr ht =>
      have hlt := ht.potential_le.trans_lt (read_decreases hr)
      rw [hp] at hlt
      exact (lt_irrefl _ hlt).elim

theorem stopped_prefix (D : ResponseParser LabeledWord)
    (hstep : ∀ w n, D.step w n = w.read ∅ n)
    {w v : LabeledWord} {xs : List ℕ}
    (hraw : w.runAtoms (xs.map fun n => (∅, n)) = some v) (hv : D.stopped v = true) :
    ∃ front tail u, xs = front ++ tail ∧ D.run w front = some u ∧
      u.runAtoms (tail.map fun n => (∅, n)) = some v := by
  induction xs generalizing w with
  | nil =>
      have heq : w = v := Option.some.inj hraw
      subst v
      exact ⟨[], [], w, rfl, by simp [ResponseParser.run, hv], rfl⟩
  | cons n xs ih =>
      cases he : D.stopped w with
      | true => exact ⟨[], n :: xs, w, rfl, by simp [ResponseParser.run, he], hraw⟩
      | false =>
          cases hr : w.read ∅ n with
          | none => simp [runAtoms, hr] at hraw
          | some u =>
              have ht : u.runAtoms (xs.map fun n => (∅, n)) = some v := by
                simpa [runAtoms, hr] using hraw
              obtain ⟨front, tail, z, hxs, hf, hz⟩ := ih ht
              refine ⟨n :: front, tail, z, by simp [hxs], ?_, hz⟩
              simpa [ResponseParser.run, he, hstep, hr] using hf

theorem response_eq_of_endpoint_parser (D : ResponseParser LabeledWord)
    (hstep : ∀ w n, D.step w n = w.read ∅ n)
    {w v : LabeledWord} {xs : List ℕ}
    (hraw : w.runAtoms (xs.map fun n => (∅, n)) = some v) (hv : D.stopped v = true)
    (hend : ∀ front tail u, xs = front ++ tail → D.run w front = some u →
      u.runAtoms (tail.map fun n => (∅, n)) = some v → u.parser = v.parser) :
    D.run w xs = some v := by
  obtain ⟨front, tail, u, hxs, hf, ht⟩ := stopped_prefix D hstep hraw hv
  have hnil : tail = [] := List.map_eq_nil_iff.mp
    ((legal_of_zero_atoms ht).nil_of_parser_eq (hend front tail u hxs hf ht).symm)
  subst tail
  have heq : u = v := Option.some.inj ht
  rw [hxs, List.append_nil, ← heq]
  exact hf

#print axioms stopped_prefix
#print axioms response_eq_of_endpoint_parser

end Erdos591.Positive.Game.LabeledWord

end Erdos118.Reused591
