/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

open Filter
open scoped Asymptotics

namespace Erdos1205

/-- A choice of one residue for each modulus `1, ..., x`.
The index `i : Fin x` represents modulus `i + 1`. -/
abbrev Assignment (x : ℕ) := (i : Fin x) → Fin (i.1 + 1)

/-- Whether the positive integer represented by `m` lies in the residue
chosen at the modulus represented by `i`. -/
def Covers {x : ℕ} (a : Assignment x) (m i : Fin x) : Prop :=
  (m.1 + 1) % (i.1 + 1) = (a i).1

open scoped Classical in
/-- The number of chosen congruences satisfied by a point. -/
noncomputable def coverage {x : ℕ} (a : Assignment x) (m : Fin x) : ℕ :=
  ((Finset.univ : Finset (Fin x)).filter fun i ↦ Covers a m i).card

/-- There is an assignment giving every point at least `k` incidences.
The explicit bound `k ≤ x` makes the empty interval behave correctly. -/
def IsCovering (x k : ℕ) : Prop :=
  k ≤ x ∧ ∃ a : Assignment x, ∀ m : Fin x, k ≤ coverage a m

open scoped Classical in
/-- Erdős's extremal function `F(x)`. -/
noncomputable def coveringNumber (x : ℕ) : ℕ :=
  Nat.findGreatest (IsCovering x) x

theorem erdos_1205 :
    (fun x : ℕ ↦ (coveringNumber x : ℝ)) ~[atTop]
      (fun x : ℕ ↦ Real.log x) := by
  sorry

end Erdos1205
