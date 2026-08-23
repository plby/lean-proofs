/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright 2026.
Released under Apache 2.0 license.
-/

import ErdosProblems.Erdos438

/-!
# Erdős Problem 587

Let `A ⊆ {1, ..., N}` and suppose that `A + A` contains no square.  The
largest possible cardinality is

`(11 / 32 + o(1)) N`.

The pair quantified by `SquareSumFree` is allowed to repeat an element, so
this is the literal sumset formulation.  The lower bound is Massias's eleven
residue classes modulo `32`; the upper bound is the
Khalfalah--Lodha--Szemerédi argument using the sharp modular theorem of
Lagarias--Odlyzko--Shearer.

The repository's complete formalization of these ingredients historically
lives under `ErdosProblems.Erdos438`.  This file supplies the required Problem
587 interface with definitionally identical names.  The mathematical proof
and a theorem-by-theorem Leanization map are in `tex/587.tex`.
-/

open Filter

namespace Erdos587

/-! ## Exact finite problem -/

/-- A finite set is square-sum-free when the sum of every ordered pair of its
elements, including a repeated element, is not a natural-number square. -/
abbrev SquareSumFree (A : Finset ℕ) : Prop :=
  Erdos438.SquareSumFree A

/-- The finite sets considered at cutoff `N`. -/
abbrev admissible (N : ℕ) (A : Finset ℕ) : Prop :=
  Erdos438.admissible N A

/-- The maximum cardinality of a square-sum-free subset of `{1, ..., N}`. -/
noncomputable abbrev extremalSize (N : ℕ) : ℕ :=
  Erdos438.extremalSize N

/-! ## The explicit lower construction -/

/-- Massias's truncation of the eleven residue classes
`1, 5, 9, 13, 14, 17, 21, 25, 26, 29, 30` modulo `32`. -/
abbrev massiasSet (N : ℕ) : Finset ℕ :=
  Erdos438.massiasSet N

/-- The Massias set is an admissible set for every cutoff. -/
theorem massiasSet_admissible (N : ℕ) :
    admissible N (massiasSet N) := by
  exact Erdos438.massiasSet_admissible N

/-- The explicit lower construction has density tending to `11 / 32`. -/
theorem tendsto_massiasSet_density :
    Tendsto (fun N : ℕ ↦ ((massiasSet N).card : ℝ) / (N : ℝ)) atTop
      (nhds ((11 : ℝ) / 32)) := by
  exact Erdos438.tendsto_massiasSet_density

/-! ## The asymptotic upper bound -/

/-- Khalfalah--Lodha--Szemerédi upper bound in its precise epsilon form. -/
theorem eventually_upper :
    ∀ ε : ℝ, 0 < ε →
      ∀ᶠ N : ℕ in atTop, ∀ A : Finset ℕ, admissible N A →
        (A.card : ℝ) / (N : ℝ) ≤ (11 : ℝ) / 32 + ε := by
  exact Erdos438.kls_eventuallyUpper

/-! ## Resolution -/

/-- Resolution of Erdős Problem 587: the extremal density of subsets of
`{1, ..., N}` whose two-fold sumset contains no square is exactly `11 / 32`. -/
theorem erdos_587 :
    Tendsto (fun N : ℕ ↦ (extremalSize N : ℝ) / (N : ℝ)) atTop
      (nhds ((11 : ℝ) / 32)) := by
  exact Erdos438.erdos_438

#print axioms Erdos587.erdos_587

end Erdos587
