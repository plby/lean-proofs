/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import Mathlib

/-!
# Erdős Problem 277

Haight proved that integers with arbitrarily large abundancy can be chosen so
that their nontrivial divisors cannot be the distinct moduli of a covering
system.  The proof below uses the finite residual-density estimate of
Filaseta--Ford--Konyagin--Pomerance--Yu.

The mathematical proof and a map from its lemmas to this formalization are in
`tex/277.tex`.
-/

open scoped ArithmeticFunction.sigma BigOperators Pointwise

syntax (name := answerSyntax277) "answer(" term ")" : term
macro_rules
  | `(answer($t)) => `($t)

/-- A finite covering system over a commutative semiring. -/
structure CoveringSystem (R : Type*) [CommSemiring R] where
  ι : Type
  [fintypeIndex : Fintype ι]
  residue : ι → R
  moduli : ι → Ideal R
  unionCovers : ⋃ i, ({residue i} : Set R) + (moduli i : Set R) = Set.univ
  ne_bot : ∀ i, moduli i ≠ ⊥
  ne_top : ∀ i, moduli i ≠ ⊤

attribute [instance] CoveringSystem.fintypeIndex

/-- A covering system whose modulus ideals are pairwise distinct. -/
structure StrictCoveringSystem (R : Type*) [CommSemiring R]
    extends CoveringSystem R where
  injective_moduli : moduli.Injective

namespace Erdos277

noncomputable section

open MeasureTheory ProbabilityTheory Set

attribute [local instance] Classical.propDecidable

/-! ## The finite residual-density inequality -/

/-- The complement of the union of a finite family of events. -/
def residual {Ω ι : Type*} (s : Finset ι) (E : ι → Set Ω) : Set Ω :=
  (⋃ i ∈ s, E i)ᶜ

theorem erdos_277 :
    answer(True) ↔ ∀ c : ℝ, ∃ n : ℕ, (σ 1 n : ℝ) > c * n ∧
      ∀ (m : StrictCoveringSystem ℤ), ∃ i, (n : ℤ) ∉ m.moduli i := by
  sorry

