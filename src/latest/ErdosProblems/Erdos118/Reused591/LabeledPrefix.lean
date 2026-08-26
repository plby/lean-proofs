import ErdosProblems.Erdos118.Reused591.LabeledCode
import ErdosProblems.Erdos118.Reused591.GamePayoff

namespace Erdos118.Reused591

/-!
# Canonical prefixes ending at a leaf

The prefix execution gives the exact one-based body and leaf indices
stored by the game cursor. Its endpoint is also identified with the
literal coordinate index used by the clarity predicate.
-/

namespace Erdos591.Positive.Game

namespace LabeledWord

theorem runAtoms_leaves_part (w : LabeledWord) (r k : ℕ) (xs : List ℕ)
    (hp : w.parser = Parser.normalize r (xs.length + k)) :
    runAtoms w (xs.map fun n => (∅, n)) = some {w with
      parser := Parser.normalize r k
      coordinates := w.coordinates ++ xs
      leafIndex := w.leafIndex + xs.length} := by
  induction xs generalizing w with
  | nil =>
      have hp' : w.parser = Parser.normalize r k := by simpa using hp
      cases w
      simp_all
  | cons n xs ih =>
      have hp' : w.parser = .leaves r (xs.length + k) := by
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm, Parser.normalize] using hp
      have hr := read_leaves w r (xs.length + k) n hp'
      let v : LabeledWord := {w with
        parser := Parser.normalize r (xs.length + k)
        coordinates := w.coordinates ++ [n]
        leafIndex := w.leafIndex + 1}
      have hv := ih v rfl
      simpa [runAtoms, hr, v, List.append_assoc, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm] using hv

end LabeledWord

namespace LabeledCode

open Erdos591.Negative.Exact

def rootCursor (C : Finset ℕ) (m : ℕ) : LabeledWord :=
  ⟨.blocks m, [m], C, [], 0, m, 0⟩

theorem read_root (C : Finset ℕ) (m : ℕ) :
    LabeledWord.initial.read C m = some (rootCursor C m) := rfl

def leafPrefixAtoms (C : Finset ℕ) (pre : List Body) (D : Finset ℕ)
    (us vs : List ℕ) (rest : List Body) : List (Finset ℕ × ℕ) :=
  [(C, pre.length + 1 + rest.length)] ++ bodiesAtoms pre ++
    [(D, (us ++ vs).length)] ++ us.map fun n => (∅, n)

def leafPrefixCursor (C : Finset ℕ) (pre : List Body) (D : Finset ℕ)
    (us vs : List ℕ) (rest : List Body) : LabeledWord :=
  { parser := Parser.normalize rest.length vs.length
    coordinates := [pre.length + 1 + rest.length] ++ (erase pre).flatMap levelWord ++
      [(us ++ vs).length] ++ us
    rootLabel := C
    bodyLabels := pre.map Prod.fst ++ [D]
    leafIndex := us.length
    rootMarker := pre.length + 1 + rest.length
    bodyMarker := (us ++ vs).length }

theorem run_leafPrefix (C : Finset ℕ) (pre : List Body) (D : Finset ℕ)
    (us vs : List ℕ) (rest : List Body) :
    LabeledWord.initial.runAtoms (leafPrefixAtoms C pre D us vs rest) =
      some (leafPrefixCursor C pre D us vs rest) := by
  let m := pre.length + 1 + rest.length
  let r := rest.length
  let v₀ := rootCursor C m
  let v₁ : LabeledWord :=
    { parser := .blocks (r + 1)
      coordinates := [m] ++ (erase pre).flatMap levelWord
      rootLabel := C
      bodyLabels := pre.map Prod.fst
      leafIndex := (pre.map (fun a => a.2.length)).getLastD 0
      rootMarker := m
      bodyMarker := (pre.map (fun a => a.2.length)).getLastD 0 }
  have hb : v₀.runAtoms (bodiesAtoms pre) = some v₁ := by
    have hp : v₀.parser = .blocks (pre.length + (r + 1)) := by
      simp [v₀, rootCursor, m, r, Nat.add_comm, Nat.add_left_comm]
    simpa [v₀, rootCursor, v₁] using run_bodies v₀ pre (r + 1) hp
  let v₂ := v₁.record D (us ++ vs).length (Parser.normalize r (us ++ vs).length)
  have hr : v₁.read D (us ++ vs).length = some v₂ := by
    simp [LabeledWord.read, v₁, Parser.step, v₂]
  have hl := LabeledWord.runAtoms_leaves_part v₂ r vs.length us
    (by simp [v₂, LabeledWord.record])
  rw [leafPrefixAtoms, LabeledWord.runAtoms_append,
    LabeledWord.runAtoms_append, LabeledWord.runAtoms_append]
  simp only [LabeledWord.runAtoms, read_root, Option.bind_some,
    Option.bind_fun_some, Option.bind_assoc]
  change ((v₀.runAtoms (bodiesAtoms pre)).bind fun w =>
    (w.read D (us ++ vs).length).bind fun v =>
      v.runAtoms (us.map fun n => (∅, n))) = _
  rw [hb, Option.bind_some, hr, Option.bind_some]
  simpa [leafPrefixCursor, v₂, LabeledWord.record, v₁, m, r, List.append_assoc] using hl

theorem atoms_split_leafPrefix (C : Finset ℕ) (pre : List Body) (D : Finset ℕ)
    (us vs : List ℕ) (rest : List Body) :
    atoms C (pre ++ (D, us ++ vs) :: rest) =
      leafPrefixAtoms C pre D us vs rest ++
        ((vs.map fun n => (∅, n)) ++ bodiesAtoms rest) := by
  simp [atoms, leafPrefixAtoms, bodiesAtoms, bodyAtoms, List.append_assoc,
    Nat.add_comm, Nat.add_left_comm]

theorem leafPrefix_relaxed (C : Finset ℕ) (pre : List Body) (D : Finset ℕ)
    (us vs : List ℕ) (rest : List Body) :
    (leafPrefixCursor C pre D us vs rest).relaxed = true ↔
      0 < us.length ∧ pre.length + 1 ∈ C ∧ us.length ∈ D := by
  simp [LabeledWord.relaxed, LabeledWord.currentLabel, leafPrefixCursor]

theorem erase_take_prefix (pre rest : List Body) (D : Finset ℕ) (a : List ℕ) :
    (erase (pre ++ (D, a) :: rest)).take pre.length = erase pre := by
  simp [erase]

theorem leafPrefix_length (C : Finset ℕ) (pre : List Body) (D : Finset ℕ)
    (us vs : List ℕ) (rest : List Body) (hu : 0 < us.length) :
    (leafPrefixCursor C pre D us vs rest).coordinates.length =
      Payoff.leafPosition (erase (pre ++ (D, us ++ vs) :: rest))
        pre.length (us.length - 1) + 1 := by
  have hflat : ((erase pre).flatMap levelWord).length =
      ((erase pre).map (fun a => a.length + 1)).sum := by
    simp [List.length_flatMap, levelWord_length]
  simp only [leafPrefixCursor, List.length_append, List.length_singleton,
    Payoff.leafPosition, erase_take_prefix, hflat]
  omega

#print axioms run_leafPrefix
#print axioms leafPrefix_length

end LabeledCode

end Erdos591.Positive.Game

end Erdos118.Reused591
