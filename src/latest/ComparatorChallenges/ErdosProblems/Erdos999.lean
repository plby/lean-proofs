/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

open Metric
open scoped ENNReal

namespace Erdos999

/-- A reduced numerator for the positive denominator `q`. -/
abbrev ReducedNumerator (q : ℕ) :=
  {p : ℕ // p < q ∧ q.Coprime p}

/-- The radius in the inequality of Problem 999. -/
noncomputable def approximationRadius (f : ℕ → ℕ) (q : ℕ) : ℝ :=
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
noncomputable def duffinSchaefferSum (f : ℕ → ℕ) : ℝ≥0∞ :=
  ∑' n : ℕ,
    (Nat.totient (n + 1) : ℝ≥0∞) * (f (n + 1) : ℝ≥0∞) / (n + 1 : ℝ≥0∞)

theorem erdos_999 :
    ∀ f : ℕ → ℕ,
      Erdos999.AlmostEverywhereApproximable f ↔ Erdos999.duffinSchaefferSum f = ∞ := by
  sorry

end Erdos999
