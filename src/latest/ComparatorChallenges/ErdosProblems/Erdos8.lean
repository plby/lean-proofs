/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

namespace Erdos8

/-- A finite family of congruence classes with distinct nontrivial moduli.

The moduli form a `Finset`, so distinctness is built into the representation.
The function `a` chooses the single residue attached to each modulus. -/
def IsDistinctCoveringSystem (D : Finset ℕ) (a : ℕ → ℤ) : Prop :=
  (∀ d ∈ D, 2 ≤ d) ∧
    ∀ z : ℤ, ∃ d ∈ D, Int.ModEq d z (a d)

/-- All moduli of `D` receive one common colour. -/
def Monochromatic {κ : Type*} (colour : ℤ → κ) (D : Finset ℕ) : Prop :=
  ∃ k : κ, ∀ d ∈ D, colour (d : ℤ) = k

/-- Not every finite colouring admits a monochromatic distinct covering system. -/
theorem not_erdos_8 :
    ¬ (∀ (r : ℕ), 0 < r → ∀ colour : ℤ → Fin r,
      ∃ D : Finset ℕ, ∃ a : ℕ → ℤ,
        IsDistinctCoveringSystem D a ∧ Monochromatic colour D) := by
  sorry

end Erdos8
