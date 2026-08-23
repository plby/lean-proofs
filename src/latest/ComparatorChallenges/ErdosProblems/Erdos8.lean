/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

namespace Erdos8


open scoped Classical in
/-- A finite family of congruence classes with distinct nontrivial moduli.

The moduli form a `Finset`, so distinctness is built into the representation.
The function `a` chooses the single residue attached to each modulus. -/
def IsDistinctCoveringSystem (D : Finset ℕ) (a : ℕ → ℤ) : Prop :=
  (∀ d ∈ D, 2 ≤ d) ∧
    ∀ z : ℤ, ∃ d ∈ D, Int.ModEq d z (a d)

open scoped Classical in
/-- All moduli of `D` receive one common colour. -/
def Monochromatic {κ : Type*} (colour : ℤ → κ) (D : Finset ℕ) : Prop :=
  ∃ k : κ, ∀ d ∈ D, colour (d : ℤ) = k

open scoped Classical in
/-- The literal universal question in Problem 8, with a nonempty finite palette
represented by `Fin r`. -/
def EveryFiniteColoringHasMonochromaticCover : Prop :=
  ∀ (r : ℕ), 0 < r → ∀ colour : ℤ → Fin r,
    ∃ D : Finset ℕ, ∃ a : ℕ → ℤ,
      IsDistinctCoveringSystem D a ∧ Monochromatic colour D

open scoped Classical in
/-- `B` meets the minimum-modulus conclusion if every distinct covering
system contains a modulus at most `B`. -/
def IsMinimumModulusBound (B : ℕ) : Prop :=
  ∀ (D : Finset ℕ) (a : ℕ → ℤ), IsDistinctCoveringSystem D a →
    ∃ d ∈ D, d ≤ B

open scoped Classical in
/-- The cutoff colouring: integers of absolute value at most `B` receive
their absolute value, and every other integer has colour zero.  In particular,
the positive moduli `d ≤ B` all receive distinct nonzero colours. -/
def cutoffColour (B : ℕ) (z : ℤ) : Fin (B + 1) :=
  if h : z.natAbs ≤ B then
    ⟨z.natAbs, by omega⟩
  else
    0

open scoped Classical in
@[simp]
theorem erdos_8 : ¬ EveryFiniteColoringHasMonochromaticCover := by
  sorry

end Erdos8
