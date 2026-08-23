/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

set_option linter.style.setOption false
set_option linter.style.longLine false
set_option linter.style.show false
set_option linter.flexible false

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Pointwise

set_option maxHeartbeats 1000000
set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Erdos115

open scoped Classical in
noncomputable def eremenko_bound (n : ℕ) : ℝ := (2 : ℝ) ^ ((1 : ℝ) / n - 1) * (n : ℝ) ^ 2
open scoped Classical in
noncomputable def extremal_polynomial (n : ℕ) : Polynomial ℂ :=
  (Polynomial.Chebyshev.T ℂ n).comp (Polynomial.C ((2 : ℂ) ^ ((1 : ℂ) / n - 1)) * Polynomial.X + 1)
end Erdos115

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Pointwise

namespace Erdos115

open scoped Classical in
theorem eremenko_lempert_1999 (n : ℕ) :
    (n ≠ 0 → ∀ p : Polynomial ℂ, p.Monic → p.degree = n →
      IsConnected {z | ‖p.eval z‖ ≤ 1} →
      ∀ z, ‖p.eval z‖ ≤ 1 → ‖p.derivative.eval z‖ ≤ (2 : ℝ) ^ ((1 : ℝ) / n - 1) * (n : ℝ) ^ 2) ∧
    (n ≠ 0 → ‖(extremal_polynomial n).derivative.eval 0‖ = (2 : ℝ) ^ ((1 : ℝ) / n - 1) * (n : ℝ) ^ 2) := by
  sorry

end Erdos115
