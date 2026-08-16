import Mathlib

/-!
# The Lean Eval statement of Szemerédi's theorem

This module records the definitions used by the Lean theorem-proving
evaluation.  Keeping them in a small module makes the public theorem's type
easy to compare verbatim with the challenge statement.
-/

namespace SzemeredisTheorem

open scoped BigOperators

/-- A set contains arithmetic progressions of every finite length. -/
def ContainsArbitraryAPs (A : Set ℕ) : Prop :=
  ∀ k : ℕ, ∃ a b : ℕ, 1 ≤ b ∧ ∀ j : ℕ, j < k → a + b * j ∈ A

/-- Upper asymptotic density, using the same inclusive prefixes as Lean Eval. -/
noncomputable def upperDensity (A : Set ℕ) : ℝ :=
  Filter.limsup
    (fun n : ℕ =>
      (∑ k ∈ Finset.range (n + 1), A.indicator (fun _ => (1 : ℝ)) k) / (n + 1))
    Filter.atTop

end SzemeredisTheorem
