/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib


open Complex ArithmeticFunction Int Set Real Filter Topology BigOperators Metric
open scoped BigOperators

namespace Erdos498

open scoped Classical in
theorem littlewood_offord_complex_bound (n : ℕ) (z : Fin n → ℂ) (hz : ∀ i, 1 < ‖z i‖) (c : ℂ) :
    let signs : Finset ℤ := {-1, 1}
    let all_coeffs : Set (Fin n → ℤ) := {ε | ∀ i, ε i ∈ signs}
    let valid_sums : Set (Fin n → ℤ) :=
      {ε | ε ∈ all_coeffs ∧ (∑ i, (ε i : ℂ) * z i) ∈ Metric.closedBall c 1}
    valid_sums.ncard ≤ Nat.choose n (n / 2) := by
  sorry

end Erdos498
