/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/- Original license: Apache 2.0. Note: This file has been modified. -/
/-
This is a Lean formalization of a solution to Erdős Problem 228.
https://www.erdosproblems.com/forum/thread/228

Informal authors:
- Paul Balister
- Béla Bollobás
- Robert Morris
- Julian Sahasrabudhe
- Marius Tiba

Statement authors:
- Formal Conjectures authors

Formal authors:
- Codex
- GPT-5.6 Sol

URLs:
- https://github.com/plby/lean-proofs/blob/main/ErdosProblems/Erdos228.md
- https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/ErdosProblems/228.lean
-/
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
    ∃ (c₁ : ℝ) (c₂ : ℝ), ∀ᶠ n : ℕ in Filter.atTop,
    ∃ p : Polynomial ℂ, p.degree = n ∧
    (∀ i ≤ n, p.coeff i = 1 ∨ p.coeff i = -1) ∧
    ∀ z : ℂ, ‖z‖ = 1 →
    (√n < c₁ * ‖p.eval z‖ ∧ ‖p.eval z‖ < c₂ * √n) := by
  exact target_of_eventually_centered eventuallyCenteredPaired

#print axioms Erdos228.erdos_228

end Erdos228
