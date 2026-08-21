/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos228.AnalyticCore

/-!
# Erdős Problem 228

Balister, Bollobás, Morris, Sahasrabudhe, and Tiba proved that Littlewood
polynomials exist whose modulus is bounded above and below by absolute
multiples of the square root of their degree, uniformly on the unit circle.

The detailed mathematical reconstruction and the correspondence between its
lemmas and this development are in `tex/228.tex`.
-/

namespace Erdos228

/-- The affirmative resolution of Erdős Problem 228. -/
theorem erdos_228 :
    answer(True) ↔ ∃ (c₁ : ℝ) (c₂ : ℝ), ∀ᶠ n : ℕ in Filter.atTop,
    ∃ p : Polynomial ℂ, p.degree = n ∧
    (∀ i ≤ n, p.coeff i = 1 ∨ p.coeff i = -1) ∧
    ∀ z : ℂ, ‖z‖ = 1 →
    (√n < c₁ * ‖p.eval z‖ ∧ ‖p.eval z‖ < c₂ * √n) := by
  exact target_of_eventually_centered eventuallyCenteredPaired

#print axioms Erdos228.erdos_228

end Erdos228
