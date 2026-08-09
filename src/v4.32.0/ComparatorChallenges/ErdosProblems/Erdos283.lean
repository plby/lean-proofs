import Mathlib.AlgebraicTopology.SimplexCategory.Basic
import Mathlib.Data.Int.ConditionallyCompleteOrder
import Mathlib.Algebra.Polynomial.Degree.Defs
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Order.Filter.AtTopBot.Defs
import Mathlib.Order.Interval.Finset.Fin

namespace Erdos283

open Filter Polynomial Finset

def Condition (p : ℤ[X]) : Prop :=
  p.leadingCoeff > 0 → ¬ (∃ d ≥ 2, ∀ n ≥ 1, d ∣ p.eval n) →
    ∀ᶠ m in atTop, ∃ k ≥ 1, ∃ n : Fin (k + 1) → ℤ, 0 = n 0 ∧ StrictMono n ∧
      1 = ∑ i ∈ Finset.Icc 1 (Fin.last k), (1 : ℚ) / (n i) ∧
      m = ∑ i ∈ Finset.Icc 1 (Fin.last k), p.eval (n i)
end Erdos283

attribute [local instance] Classical.propDecidable

theorem Erdos283.erdos_283 :
    Iff True (∀ (p : @Polynomial.{0} Int Int.instSemiring), Erdos283.Condition p)
  := by
  sorry
