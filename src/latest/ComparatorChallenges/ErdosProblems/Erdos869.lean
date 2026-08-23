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
open MeasureTheory ProbabilityTheory

noncomputable section


namespace Set

variable {M : Type*} [AddCommMonoid M]

open scoped Classical in
def IsAsymptoticAddBasisOfOrder (A : Set M) (o : ℕ) : Prop :=
  ∀ᶠ m in cofinite, m ∈ o • A

end Set

namespace Erdos869

open scoped Classical in
abbrev IsBasis2 (A : Set ℕ) : Prop := A.IsAsymptoticAddBasisOfOrder 2

end Erdos869

namespace Erdos869

open scoped Classical in
theorem erdos_869 :
    ¬ ∀ (A₁ A₂ : Set ℕ), Disjoint A₁ A₂ →
      IsBasis2 A₁ → IsBasis2 A₂ →
      ∃ D ⊆ A₁ ∪ A₂, IsBasis2 D ∧
        ∀ d ∈ D, ¬ IsBasis2 (D \ {d}) := by
  sorry

end Erdos869

end
