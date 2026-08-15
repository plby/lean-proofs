/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos387.CoverAlgebra
import ErdosProblems.Erdos387.DivisorStructure

/-!
# Exhaustion of the BNPZ divisor error classes

The analytic estimates use different tools according to the sizes and
factorizations of the residual-divisor components.  This file proves that the
corresponding finite cases really exhaust every tuple.  Thresholds are kept
as natural numbers so later modules can instantiate them by the required
integer floors of powers of `x`.
-/

namespace Erdos387

namespace CoverDivisorTuple

/-- Some component is strictly above the large threshold. -/
def HasLargeComponent {D : CoverFactorization n k}
    (E : CoverDivisorTuple D) (large : ℕ) : Prop :=
  ∃ i : Fin k, large < E.factor i

/-- Some component lies in the half-open medium range `(medium, large]`. -/
def HasMediumComponent {D : CoverFactorization n k}
    (E : CoverDivisorTuple D) (medium large : ℕ) : Prop :=
  ∃ i : Fin k, medium < E.factor i ∧ E.factor i ≤ large

/-- One component factors into two integers both exceeding `y`. -/
def HasConvenientComponent {D : CoverFactorization n k}
    (E : CoverDivisorTuple D) (y : ℕ) : Prop :=
  ∃ i : Fin k, ∃ r s : ℕ,
    E.factor i = r * s ∧ y < r ∧ y < s

/-- Every component is a `y³`-small factor times either one or a single prime
above `y`. -/
def IsAlmostPrimeTuple {D : CoverFactorization n k}
    (E : CoverDivisorTuple D) (y : ℕ) : Prop :=
  ∀ i : Fin k, ∃ f q : ℕ,
    E.factor i = f * q ∧ f ≤ y ^ 3 ∧
      (q = 1 ∨ q.Prime ∧ y < q)

/-- Negating the tuple-level convenient case gives the component-level
factorization hypothesis consumed by `exists_almostPrime_decomposition`. -/
theorem noConvenientFactorization_factor
    {D : CoverFactorization n k} {E : CoverDivisorTuple D} {y : ℕ}
    (hnot : ¬E.HasConvenientComponent y) (i : Fin k) :
    NoConvenientFactorization y (E.factor i) := by
  intro r s hrs
  by_contra hsmall
  simp only [not_or, not_le] at hsmall
  exact hnot ⟨i, r, s, hrs, hsmall.1, hsmall.2⟩

/-- Once the convenient case is excluded, every positive component has the
exact almost-prime decomposition used in the last two error classes. -/
theorem isAlmostPrimeTuple_of_not_hasConvenient
    {D : CoverFactorization n k} {E : CoverDivisorTuple D} {y : ℕ}
    (hy : 2 ≤ y) (hpos : ∀ i : Fin k, 0 < E.factor i)
    (hnot : ¬E.HasConvenientComponent y) :
    E.IsAlmostPrimeTuple y := by
  intro i
  exact exists_almostPrime_decomposition hy (hpos i)
    (noConvenientFactorization_factor hnot i)

/-- Exact four-way exhaustion underlying BNPZ's five error estimates.

The first disjunct is Proposition 6.2's range, the second is Proposition
6.3's range, and the third is Proposition 6.4's convenient-factorization
range.  In the final disjunct all components are below `medium` and have the
small-times-one-prime representation used in Propositions 6.5 and 6.6. -/
theorem errorClass_exhaustion
    {D : CoverFactorization n k} (E : CoverDivisorTuple D)
    {y medium large : ℕ} (hy : 2 ≤ y)
    (hpos : ∀ i : Fin k, 0 < E.factor i) :
    E.HasLargeComponent large ∨
      E.HasMediumComponent medium large ∨
      ((∀ i : Fin k, E.factor i ≤ medium) ∧
        E.HasConvenientComponent y) ∨
      ((∀ i : Fin k, E.factor i ≤ medium) ∧ E.IsAlmostPrimeTuple y) := by
  by_cases hlarge : E.HasLargeComponent large
  · exact Or.inl hlarge
  right
  have hallLarge : ∀ i : Fin k, E.factor i ≤ large := by
    intro i
    by_contra hi
    exact hlarge ⟨i, Nat.lt_of_not_ge hi⟩
  by_cases hmedium : ∃ i : Fin k, medium < E.factor i
  · obtain ⟨i, hi⟩ := hmedium
    exact Or.inl ⟨i, hi, hallLarge i⟩
  right
  have hallMedium : ∀ i : Fin k, E.factor i ≤ medium := by
    intro i
    by_contra hi
    exact hmedium ⟨i, Nat.lt_of_not_ge hi⟩
  by_cases hconv : E.HasConvenientComponent y
  · exact Or.inl ⟨hallMedium, hconv⟩
  · exact Or.inr ⟨hallMedium,
      isAlmostPrimeTuple_of_not_hasConvenient hy hpos hconv⟩

end CoverDivisorTuple

end Erdos387
