/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

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
import Mathlib.Algebra.Order.Floor.Div
import Mathlib.Probability.Distributions.Uniform

open Filter
open scoped Pointwise

namespace Set

variable {M : Type*} [AddCommMonoid M]

def IsAsymptoticAddBasisOfOrder (A : Set M) (o : ℕ) : Prop :=
  ∀ᶠ m in cofinite, m ∈ o • A

end Set

namespace Erdos869

abbrev IsBasis2 (A : Set ℕ) : Prop := A.IsAsymptoticAddBasisOfOrder 2

theorem not_erdos_869 :
    ¬ ∀ (A₁ A₂ : Set ℕ), Disjoint A₁ A₂ →
      IsBasis2 A₁ → IsBasis2 A₂ →
      ∃ D ⊆ A₁ ∪ A₂, IsBasis2 D ∧
        ∀ d ∈ D, ¬ IsBasis2 (D \ {d}) := by
  sorry

end Erdos869
