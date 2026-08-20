/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Erdos Problem 999 is the Duffin--Schaeffer theorem.

The exact statement is formalized below on the unit additive circle.  The
circle is the standard probability-space version of "almost every alpha",
and `n + 1` indexes the positive denominator q.

Primary reference:
D. Koukoulopoulos and J. Maynard, On the Duffin--Schaeffer conjecture,
Annals of Mathematics 192 (2020), 251--307.

The detailed mathematical proof and Leanization dependency map are in
`tex/999.tex`.
-/

import Mathlib

open Filter Metric Set MeasureTheory
open scoped ENNReal MeasureTheory Topology

namespace Erdos999

noncomputable section

/-- A reduced numerator for the positive denominator `q`. -/
abbrev ReducedNumerator (q : ℕ) :=
  {p : ℕ // p < q ∧ q.Coprime p}

/-- The radius in the inequality of Problem 999. -/
def approximationRadius (f : ℕ → ℕ) (q : ℕ) : ℝ :=
  (f q : ℝ) / q

/-- The set of points admitting a reduced approximation with denominator
`n + 1`. -/
def approximationLayer (f : ℕ → ℕ) (n : ℕ) : Set UnitAddCircle :=
  ⋃ p : ReducedNumerator (n + 1),
    ball (↑(((p.1 : ℕ) : ℝ) / (n + 1)) : UnitAddCircle)
      (approximationRadius f (n + 1))

/-- The literal "infinitely many solutions" predicate, with positive
denominators indexed by `n + 1`. -/
def InfinitelyOftenApproximable (f : ℕ → ℕ) (x : UnitAddCircle) : Prop :=
  {n : ℕ | x ∈ approximationLayer f n}.Infinite

/-- The almost-everywhere approximation property in Problem 999. -/
def AlmostEverywhereApproximable (f : ℕ → ℕ) : Prop :=
  ∀ᵐ x : UnitAddCircle, InfinitelyOftenApproximable f x

/-- The nonnegative extended-real series from Problem 999.  Index `n`
corresponds to the positive denominator `q = n + 1`. -/
def duffinSchaefferSum (f : ℕ → ℕ) : ℝ≥0∞ :=
  ∑' n : ℕ,
    (Nat.totient (n + 1) : ℝ≥0∞) * (f (n + 1) : ℝ≥0∞) / (n + 1 : ℝ≥0∞)

/-- Exact formal statement of the `ℕ → ℕ` specialization recorded as
Erdos Problem 999. -/
def Erdos999Statement : Prop :=
  ∀ f : ℕ → ℕ,
    AlmostEverywhereApproximable f ↔ duffinSchaefferSum f = ∞


theorem erdos_999 : Erdos999Statement := by
  sorry

end

end Erdos999
