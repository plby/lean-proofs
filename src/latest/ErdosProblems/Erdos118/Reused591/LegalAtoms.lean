import ErdosProblems.Erdos118.Reused591.LabeledPrefix
import ErdosProblems.Erdos118.Reused591.CutLabels

namespace Erdos118.Reused591

/-!
# Label legality along canonical atomic words

`LegalRun` records each actual cursor read together with its label rule.
It has no scheduling or graph assumptions. Canonical words with the
specified strict label bounds give legal runs, in particular the labels
computed from geometrically admissible cuts.
-/

namespace Erdos591.Positive.Game

namespace LabeledWord

inductive LegalRun : LabeledWord → List (Finset ℕ × ℕ) → LabeledWord → Prop
  | nil (w : LabeledWord) : LegalRun w [] w
  | cons (w : LabeledWord) (D : Finset ℕ) (n : ℕ) (v : LabeledWord)
      (xs : List (Finset ℕ × ℕ)) (last : LabeledWord)
      (hlabel : w.AllowedLabel D n) (hread : w.read D n = some v)
      (htail : LegalRun v xs last) : LegalRun w ((D, n) :: xs) last

theorem LegalRun.run {w v : LabeledWord} {xs : List (Finset ℕ × ℕ)}
    (h : LegalRun w xs v) : runAtoms w xs = some v := by
  induction h with
  | nil => rfl
  | cons w D n v xs last _ hr _ ih => simpa [runAtoms, hr] using ih

theorem legalRun_nil_iff (w v : LabeledWord) : LegalRun w [] v ↔ w = v := by
  constructor
  · intro h
    exact Option.some.inj h.run
  · rintro rfl
    exact .nil w

theorem legalRun_cons_iff (w v : LabeledWord) (D : Finset ℕ) (n : ℕ)
    (xs : List (Finset ℕ × ℕ)) :
    LegalRun w ((D, n) :: xs) v ↔
      ∃ u, w.AllowedLabel D n ∧ w.read D n = some u ∧ LegalRun u xs v := by
  constructor
  · intro h
    cases h with
    | cons _ _ _ u _ _ hl hr ht => exact ⟨u, hl, hr, ht⟩
  · rintro ⟨u, hl, hr, ht⟩
    exact .cons w D n u xs v hl hr ht

theorem LegalRun.of_run_eq {w v u : LabeledWord} {xs : List (Finset ℕ × ℕ)}
    (h : LegalRun w xs v) (hu : runAtoms w xs = some u) : LegalRun w xs u := by
  have heq : v = u := Option.some.inj (h.run.symm.trans hu)
  exact heq ▸ h

theorem LegalRun.append {w v u : LabeledWord} {xs ys : List (Finset ℕ × ℕ)}
    (h : LegalRun w xs v) (hu : LegalRun v ys u) : LegalRun w (xs ++ ys) u := by
  induction h with
  | nil => exact hu
  | cons w D n v xs last hl hr _ ih => exact .cons w D n v (xs ++ ys) u hl hr (ih hu)

theorem LegalRun.split {w v : LabeledWord} {xs ys : List (Finset ℕ × ℕ)}
    (h : LegalRun w (xs ++ ys) v) : ∃ u, LegalRun w xs u ∧ LegalRun u ys v := by
  induction xs generalizing w with
  | nil => exact ⟨w, .nil w, h⟩
  | cons a xs ih =>
      cases h with
      | cons w D n u _ v hl hr ht =>
          obtain ⟨z, hz, hv⟩ := ih ht
          exact ⟨z, .cons w D n u xs z hl hr hz, hv⟩

theorem LegalRun.take_drop {w v : LabeledWord} {xs : List (Finset ℕ × ℕ)}
    (h : LegalRun w xs v) (n : ℕ) :
    ∃ u, LegalRun w (xs.take n) u ∧ LegalRun u (xs.drop n) v := by
  apply LegalRun.split
  simpa using h

theorem LegalRun.cursorInvariant {w v : LabeledWord} {xs : List (Finset ℕ × ℕ)}
    (h : LegalRun w xs v) (hw : w.CursorInvariant) : v.CursorInvariant := by
  induction h with
  | nil => exact hw
  | cons w D n v xs last hl hr _ ih => exact ih (hw.read hl hr)

theorem read_rootLabel_eq {w v : LabeledWord} {D : Finset ℕ} {n : ℕ}
    (hr : w.read D n = some v) (hw : w.parser ≠ .start) : v.rootLabel = w.rootLabel := by
  cases hs : Parser.step w.parser n with
  | none => simp [LabeledWord.read, hs] at hr
  | some p =>
      have heq : w.record D n p = v := by simpa [LabeledWord.read, hs] using hr
      subst v
      cases hp : w.parser <;> simp_all [LabeledWord.record]

theorem LegalRun.rootLabel_eq {w v : LabeledWord} {xs : List (Finset ℕ × ℕ)}
    (h : LegalRun w xs v) (hw : w.parser ≠ .start) : v.rootLabel = w.rootLabel := by
  induction h with
  | nil => rfl
  | cons w D n v xs last _ hr _ ih =>
      exact (ih (read_parser_ne_start hr)).trans (read_rootLabel_eq hr hw)

theorem exists_legal_leaves (w : LabeledWord) (r : ℕ) (xs : List ℕ)
    (hp : w.parser = Parser.normalize r xs.length) :
    ∃ v, LegalRun w (xs.map fun n => (∅, n)) v := by
  induction xs generalizing w with
  | nil => exact ⟨w, .nil w⟩
  | cons n xs ih =>
      have hp' : w.parser = .leaves r xs.length := hp
      let v : LabeledWord := {w with
        parser := Parser.normalize r xs.length
        coordinates := w.coordinates ++ [n]
        leafIndex := w.leafIndex + 1}
      have hr : w.read ∅ n = some v := read_leaves w r xs.length n hp'
      obtain ⟨last, hl⟩ := ih v rfl
      exact ⟨last, .cons w ∅ n v _ last (allowed_empty (read_nonterminal hr) n) hr hl⟩

end LabeledWord

namespace LabeledCode

open LabeledWord

def LawfulBodies (C : Finset ℕ) (offset : ℕ) : List Body → Prop
  | [] => True
  | a :: as => (∀ j ∈ a.1, 0 < j ∧ j < a.2.length) ∧
      (offset + 1 ∉ C → a.1 = ∅) ∧ LawfulBodies C (offset + 1) as

theorem lawfulBodies_of_getElem (C : Finset ℕ) (offset : ℕ) (as : List Body)
    (h : ∀ i (hi : i < as.length),
      (∀ j ∈ as[i].1, 0 < j ∧ j < as[i].2.length) ∧
        (offset + i + 1 ∉ C → as[i].1 = ∅)) : LawfulBodies C offset as := by
  induction as generalizing offset with
  | nil => trivial
  | cons a as ih =>
      have hh := h 0 (by simp)
      refine ⟨hh.1, by simpa using hh.2, ?_⟩
      apply ih
      intro i hi
      have ht := h (i + 1) (by simpa using hi)
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ht

theorem legal_body (w : LabeledWord) (a : Body) (r : ℕ)
    (hp : w.parser = .blocks (r + 1)) (ha : w.AllowedLabel a.1 a.2.length) :
    LegalRun w (bodyAtoms a)
      {w with
        parser := .blocks r
        coordinates := w.coordinates ++ Erdos591.Negative.Exact.levelWord a.2
        bodyLabels := w.bodyLabels ++ [a.1]
        leafIndex := a.2.length
        bodyMarker := a.2.length} := by
  let v := w.record a.1 a.2.length (Parser.normalize r a.2.length)
  have hr : w.read a.1 a.2.length = some v := by
    simp [LabeledWord.read, hp, Parser.step, v]
  obtain ⟨last, hl⟩ := exists_legal_leaves v r a.2 rfl
  exact (LegalRun.cons w a.1 a.2.length v _ last ha hr hl).of_run_eq (run_body w a r hp)

theorem legal_bodies (w : LabeledWord) (as : List Body) (r : ℕ)
    (hp : w.parser = .blocks (as.length + r))
    (hL : LawfulBodies w.rootLabel w.bodyLabels.length as) :
    LegalRun w (bodiesAtoms as)
      {w with
        parser := .blocks r
        coordinates := w.coordinates ++
          (erase as).flatMap Erdos591.Negative.Exact.levelWord
        bodyLabels := w.bodyLabels ++ as.map Prod.fst
        leafIndex := (as.map (fun a => a.2.length)).getLastD w.leafIndex
        bodyMarker := (as.map (fun a => a.2.length)).getLastD w.bodyMarker} := by
  induction as generalizing w with
  | nil =>
      exact (LegalRun.nil w).of_run_eq (run_bodies w [] r hp)
  | cons a as ih =>
      have hp' : w.parser = .blocks (as.length + r + 1) := by
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hp
      have hallowed : w.AllowedLabel a.1 a.2.length :=
        ⟨hL.1, by simpa [hp'] using hL.2.1⟩
      let v : LabeledWord := {w with
        parser := .blocks (as.length + r)
        coordinates := w.coordinates ++ Erdos591.Negative.Exact.levelWord a.2
        bodyLabels := w.bodyLabels ++ [a.1]
        leafIndex := a.2.length
        bodyMarker := a.2.length}
      have hb : LegalRun w (bodyAtoms a) v := legal_body w a (as.length + r) hp' hallowed
      have hv := ih v rfl (by simpa [v] using hL.2.2)
      have hfull := hb.append hv
      exact hfull.of_run_eq (run_bodies w (a :: as) r hp)

theorem legal_atoms (C : Finset ℕ) (as : List Body)
    (hC : ∀ i ∈ C, 0 < i ∧ i < as.length) (hL : LawfulBodies C 0 as) :
    LegalRun LabeledWord.initial (atoms C as) (terminalCursor C as) := by
  have hroot : LabeledWord.initial.AllowedLabel C as.length := ⟨hC, trivial⟩
  have hbody := legal_bodies (rootCursor C as.length) as 0 (by simp [rootCursor]) hL
  exact (LegalRun.cons LabeledWord.initial C as.length (rootCursor C as.length) _ _
    hroot (read_root C as.length) hbody).of_run_eq (run_atoms C as)

end LabeledCode

namespace CutLabels

theorem lawful_bodies {s t : List (List ℕ)} (h : Admissible s t) :
    LabeledCode.LawfulBodies (root s t) 0 (bodies s t) := by
  apply LabeledCode.lawfulBodies_of_getElem
  intro i hi
  have hi' : i < s.length := by simpa using hi
  have heq : (bodies s t)[i] = (body s t i, s.getD i []) := by
    rw [List.getD_eq_getElem _ _ hi']
    simp [bodies]
  rw [heq]
  exact ⟨body_bounds h i, by simpa using (body_empty_of_not_selected (s := s) (t := t) (i := i))⟩

theorem legal_atoms {s t : List (List ℕ)} (h : Admissible s t) :
    LabeledWord.LegalRun LabeledWord.initial
      (LabeledCode.atoms (root s t) (bodies s t)) (cursor s t) :=
  LabeledCode.legal_atoms (root s t) (bodies s t)
    (by simpa using root_bounds h) (lawful_bodies h)

#print axioms legal_atoms

end CutLabels

end Erdos591.Positive.Game

end Erdos118.Reused591
