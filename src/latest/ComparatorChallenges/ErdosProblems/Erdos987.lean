/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

open Filter Finset

namespace Erdos987

/-! Indices are zero-based, so `range n` represents `j < n`. -/

/- ## API for the additive character `e(x) = e^{2πi x}` -/

noncomputable def e (x : ℝ) : ℂ := Complex.exp ((2 * Real.pi * x : ℝ) * Complex.I)

noncomputable def A (x : ℕ → ℝ) (k : ℕ) : EReal :=
  atTop.limsup fun n : ℕ => (‖∑ j ∈ range n, e (k * x j)‖ : EReal)

theorem erdos_987 :
    ∀ (x : ℕ → ℝ) (_ : ∀ j : ℕ, x j ∈ Set.Ioo (0 : ℝ) 1),
      atTop.limsup (fun k : ℕ => A x k) = ⊤ := by
  sorry

theorem erdos_987.variants.sqrt_log_upper_bound :
    ∃ (x : ℕ → ℝ) (_ : ∀ j : ℕ, x j ∈ Set.Ioo (0 : ℝ) 1) (C : ℝ) (_ : 0 < C),
      ∀ k n : ℕ, 2 ≤ k → ‖∑ j ∈ range n, e (k * x j)‖ ≤ C * Real.sqrt (k * Real.log k) := by
  sorry

theorem erdos_987.parts.ii :
    ∃ (x : ℕ → ℝ) (_ : ∀ j : ℕ, x j ∈ Set.Ioo (0 : ℝ) 1) (b : ℕ → ℝ),
      b =o[atTop] (fun k : ℕ => (k : ℝ)) ∧ ∀ᶠ k : ℕ in atTop, A x k ≤ ((b k : ℝ) : EReal) := by
  sorry
