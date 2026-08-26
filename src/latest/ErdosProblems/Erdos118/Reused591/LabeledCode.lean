import ErdosProblems.Erdos118.Reused591.AtomicTrace

namespace Erdos118.Reused591

/-!
# Literal labeled words and exact cursor metadata

Canonical labeled words attach labels only to the root and the body
markers. Reading them uses the existing cursor transition throughout.
The resulting body-label list and leaf counters are computed explicitly;
they are not inferred from an abstract order-isomorphic carrier.
-/

namespace Erdos591.Positive.Game.LabeledWord

def runAtoms (w : LabeledWord) : List (Finset ℕ × ℕ) → Option LabeledWord
  | [] => some w
  | (D, n) :: xs => (w.read D n).bind fun v => runAtoms v xs

@[simp] theorem runAtoms_nil (w : LabeledWord) : runAtoms w [] = some w := rfl

theorem runAtoms_append (w : LabeledWord) (xs ys : List (Finset ℕ × ℕ)) :
    runAtoms w (xs ++ ys) = (runAtoms w xs).bind fun v => runAtoms v ys := by
  induction xs generalizing w with
  | nil => rfl
  | cons a xs ih =>
      obtain ⟨D, n⟩ := a
      cases hr : w.read D n with
      | none => simp [runAtoms, hr]
      | some v => simpa [runAtoms, hr] using ih v

theorem runAtoms_coordinates {w v : LabeledWord} {xs : List (Finset ℕ × ℕ)}
    (h : runAtoms w xs = some v) : v.coordinates = w.coordinates ++ xs.map Prod.snd := by
  induction xs generalizing w with
  | nil =>
      have heq : w = v := Option.some.inj h
      simp [heq]
  | cons a xs ih =>
      obtain ⟨D, n⟩ := a
      cases hr : w.read D n with
      | none => simp [runAtoms, hr] at h
      | some u =>
          have ht : runAtoms u xs = some v := by simpa [runAtoms, hr] using h
          rw [ih ht, (read_spec hr).2]
          simp [List.append_assoc]

theorem read_leaves (w : LabeledWord) (r b n : ℕ) (hp : w.parser = .leaves r b) :
    w.read ∅ n = some {w with
      parser := Parser.normalize r b
      coordinates := w.coordinates ++ [n]
      leafIndex := w.leafIndex + 1} := by
  simp [read, record, hp, Parser.step]

theorem runAtoms_leaves (w : LabeledWord) (r : ℕ) (xs : List ℕ)
    (hp : w.parser = Parser.normalize r xs.length) :
    runAtoms w (xs.map fun n => (∅, n)) =
      some {w with
        parser := .blocks r
        coordinates := w.coordinates ++ xs
        leafIndex := w.leafIndex + xs.length} := by
  induction xs generalizing w with
  | nil =>
      have hp' : w.parser = .blocks r := hp
      cases w
      simp_all
  | cons n xs ih =>
      have hp' : w.parser = .leaves r xs.length := hp
      have hr := read_leaves w r xs.length n hp'
      let v : LabeledWord := {w with
        parser := Parser.normalize r xs.length
        coordinates := w.coordinates ++ [n]
        leafIndex := w.leafIndex + 1}
      have hv := ih v rfl
      simpa [runAtoms, hr, v, List.append_assoc, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm] using hv

end LabeledWord

namespace LabeledCode

abbrev Body := Finset ℕ × List ℕ

def bodyAtoms (a : Body) : List (Finset ℕ × ℕ) :=
  (a.1, a.2.length) :: a.2.map fun n => (∅, n)

def bodiesAtoms (as : List Body) : List (Finset ℕ × ℕ) := as.flatMap bodyAtoms

def erase (as : List Body) : List (List ℕ) := as.map Prod.snd

def atoms (C : Finset ℕ) (as : List Body) : List (Finset ℕ × ℕ) :=
  (C, as.length) :: bodiesAtoms as

def terminalCursor (C : Finset ℕ) (as : List Body) : LabeledWord :=
  { parser := .blocks 0
    coordinates := Erdos591.Negative.Exact.word (erase as)
    rootLabel := C
    bodyLabels := as.map Prod.fst
    leafIndex := (as.map (fun a => a.2.length)).getLastD 0
    rootMarker := as.length
    bodyMarker := (as.map (fun a => a.2.length)).getLastD 0 }

theorem run_body (w : LabeledWord) (a : Body) (r : ℕ) (hp : w.parser = .blocks (r + 1)) :
    w.runAtoms (bodyAtoms a) = some
      {w with
        parser := .blocks r
        coordinates := w.coordinates ++ Erdos591.Negative.Exact.levelWord a.2
        bodyLabels := w.bodyLabels ++ [a.1]
        leafIndex := a.2.length
        bodyMarker := a.2.length} := by
  let v := w.record a.1 a.2.length (Parser.normalize r a.2.length)
  have hr : w.read a.1 a.2.length = some v := by
    simp [LabeledWord.read, hp, Parser.step, v]
  have hv := LabeledWord.runAtoms_leaves v r a.2 rfl
  simpa [bodyAtoms, LabeledWord.runAtoms, hr, v, LabeledWord.record, hp,
    Erdos591.Negative.Exact.levelWord, List.append_assoc] using hv

theorem run_bodies (w : LabeledWord) (as : List Body) (r : ℕ)
    (hp : w.parser = .blocks (as.length + r)) :
    w.runAtoms (bodiesAtoms as) = some
      {w with
        parser := .blocks r
        coordinates := w.coordinates ++
          (erase as).flatMap Erdos591.Negative.Exact.levelWord
        bodyLabels := w.bodyLabels ++ as.map Prod.fst
        leafIndex := (as.map (fun a => a.2.length)).getLastD w.leafIndex
        bodyMarker := (as.map (fun a => a.2.length)).getLastD w.bodyMarker} := by
  induction as generalizing w with
  | nil =>
      have hp' : w.parser = .blocks r := by simpa using hp
      cases w
      simp_all [bodiesAtoms, erase]
  | cons a as ih =>
      have hp' : w.parser = .blocks (as.length + r + 1) := by
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hp
      have hb := run_body w a (as.length + r) hp'
      let v : LabeledWord :=
        {w with
          parser := .blocks (as.length + r)
          coordinates := w.coordinates ++ Erdos591.Negative.Exact.levelWord a.2
          bodyLabels := w.bodyLabels ++ [a.1]
          leafIndex := a.2.length
          bodyMarker := a.2.length}
      have hv := ih v rfl
      rw [bodiesAtoms, List.flatMap_cons, LabeledWord.runAtoms_append, hb]
      simpa only [bodiesAtoms, erase, v, List.map_cons, List.flatMap_cons,
        List.append_assoc, List.singleton_append, List.getLastD_cons, Option.bind_some] using hv

/-- Exact decoding of the root, all body labels, and the final leaf
counters of a canonical labeled word. -/
theorem run_atoms (C : Finset ℕ) (as : List Body) :
    LabeledWord.initial.runAtoms (atoms C as) = some (terminalCursor C as) := by
  let v : LabeledWord :=
    { parser := .blocks as.length
      coordinates := [as.length]
      rootLabel := C
      bodyLabels := []
      leafIndex := 0
      rootMarker := as.length
      bodyMarker := 0 }
  have hr : LabeledWord.initial.read C as.length = some v := rfl
  have hb := run_bodies v as 0 (by simp [v])
  simpa [atoms, LabeledWord.runAtoms, hr, terminalCursor, v,
    Erdos591.Negative.Exact.word, erase] using hb

theorem atoms_coordinates (C : Finset ℕ) (as : List Body) :
    (atoms C as).map Prod.snd = Erdos591.Negative.Exact.word (erase as) := by
  have hbody (a : Body) : (bodyAtoms a).map Prod.snd =
      Erdos591.Negative.Exact.levelWord a.2 := by
    simp [bodyAtoms, List.map_map, Erdos591.Negative.Exact.levelWord]
  simp [atoms, bodiesAtoms, erase, Erdos591.Negative.Exact.word,
    List.map_flatMap, List.flatMap_map, hbody]

#print axioms run_atoms
#print axioms atoms_coordinates

end LabeledCode

end Erdos591.Positive.Game

end Erdos118.Reused591
