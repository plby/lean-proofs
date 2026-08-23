/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib


open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Pointwise
open MeasureTheory Measure Filter Set

namespace Erdos1126

open scoped Classical in
theorem erdos_1126
    (f : ℝ → ℝ)
    (h :
      ∀ᵐ (p : ℝ × ℝ) ∂(volume.prod volume),
        f (p.1 + p.2) = f p.1 + f p.2) :
    ∃ h : ℝ → ℝ,
      (∀ x y, h (x + y) = h x + h y) ∧ (∀ᵐ x ∂volume, f x = h x) := by
  sorry

end Erdos1126
