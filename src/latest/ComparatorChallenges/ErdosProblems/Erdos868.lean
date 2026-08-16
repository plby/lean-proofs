/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
This file formalizes the negative resolution of Erdős Problem 868 by
Daniel Larsen and Michael Larsen.

Mathematical proof and formalization notes: ../../../tex/868.tex
Primary source: https://github.com/Larsen-Daniel/Erdos-868/blob/main/868.pdf
-/

import Mathlib.Algebra.Group.Pointwise.Set.BigOperators
import Mathlib.Algebra.Group.Pointwise.Set.Finite
import Mathlib.Algebra.Order.Monoid.Canonical.Defs
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Data.Set.Card
import Mathlib.Order.Filter.Cofinite
import Mathlib.Probability.Distributions.Bernoulli
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.Moments.Basic

open Filter
open scoped Pointwise

namespace Set

variable {M : Type*} [AddCommMonoid M]

/-- An asymptotic additive basis of order `o`: its `o`-fold pointwise sum is cofinite.

This is the definition from
`FormalConjecturesForMathlib.Combinatorics.Additive.Basis`; the local Mathlib
snapshot does not yet contain that file. -/
def IsAsymptoticAddBasisOfOrder (A : Set M) (o : ℕ) : Prop :=
  ∀ᶠ m in cofinite, m ∈ o • A

end Set

namespace Erdos868

syntax (name := answerSyntax868) "answer(" term ")" : term

macro_rules
  | `(answer($t)) => `($t)

/-- The ordered representation function used by the formal-conjectures specification. -/
noncomputable def ncard_add_repr (A : Set ℕ) (o : ℕ) (n : ℕ) : ℕ :=
  { a : Fin o → ℕ | Set.range a ⊆ A ∧ ∑ i, a i = n }.ncard

theorem erdos_868.parts.i :
    answer(False) ↔ ∀ (A : Set ℕ), A.IsAsymptoticAddBasisOfOrder 2 →
      atTop.Tendsto (fun n ↦ ncard_add_repr A 2 n) atTop → ∃ B ⊆ A,
      B.IsAsymptoticAddBasisOfOrder 2 ∧
        ∀ b ∈ B, ¬(B \ {b}).IsAsymptoticAddBasisOfOrder 2 := by
  sorry

theorem erdos_868.parts.ii :
    answer(False) ↔ ∀ᵉ (A : Set ℕ) (ε > 0), A.IsAsymptoticAddBasisOfOrder 2 →
      (∀ᶠ (n : ℕ) in atTop, ε * Real.log n < ncard_add_repr A 2 n) → ∃ B ⊆ A,
      B.IsAsymptoticAddBasisOfOrder 2 ∧
        ∀ b ∈ B, ¬(B \ {b}).IsAsymptoticAddBasisOfOrder 2 := by
  sorry

end Erdos868
