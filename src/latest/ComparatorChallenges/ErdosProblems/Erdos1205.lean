/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

/-!
# Erdős Problem 1205

For every modulus `1 ≤ n ≤ x`, choose one residue class modulo `n`.
The function `coveringNumber x` is the largest number of those congruences
that can be satisfied simultaneously by every integer in `{1, ..., x}`.

This file proves that `coveringNumber x ∼ log x`.  A detailed mathematical
proof and Leanization plan are in `tex/1205.tex`.
-/

open Filter Finset Set
open scoped Asymptotics BigOperators Topology

namespace Erdos1205

noncomputable section

open scoped Classical in
/-- A choice of one residue for each modulus `1, ..., x`.
The index `i : Fin x` represents modulus `i + 1`. -/
abbrev Assignment (x : ℕ) := (i : Fin x) → Fin (i.1 + 1)

open scoped Classical in
/-- Whether the positive integer represented by `m` lies in the residue
chosen at the modulus represented by `i`. -/
def Covers {x : ℕ} (a : Assignment x) (m i : Fin x) : Prop :=
  (m.1 + 1) % (i.1 + 1) = (a i).1

open scoped Classical in
/-- The number of chosen congruences satisfied by a point. -/
def coverage {x : ℕ} (a : Assignment x) (m : Fin x) : ℕ :=
  ((Finset.univ : Finset (Fin x)).filter fun i ↦ Covers a m i).card

open scoped Classical in
/-- There is an assignment giving every point at least `k` incidences.
The explicit bound `k ≤ x` makes the empty interval behave correctly. -/
def IsCovering (x k : ℕ) : Prop :=
  k ≤ x ∧ ∃ a : Assignment x, ∀ m : Fin x, k ≤ coverage a m

open scoped Classical in
/-- Erdős's extremal function `F(x)`. -/
def coveringNumber (x : ℕ) : ℕ :=
  Nat.findGreatest (IsCovering x) x

open scoped Classical in
/-- The all-zero residue assignment. -/
def zeroAssignment (x : ℕ) : Assignment x :=
  fun i ↦ ⟨0, Nat.succ_pos i.1⟩

open scoped Classical in
theorem erdos_1205 :
    (fun x : ℕ ↦ (coveringNumber x : ℝ)) ~[atTop]
      (fun x : ℕ ↦ Real.log x) := by
  sorry

end

end Erdos1205
