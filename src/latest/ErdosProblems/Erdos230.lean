/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/- Original license: Apache 2.0. Note: This file has been modified. -/
/-
This is a Lean formalization of a solution to Erdős Problem 230.
https://www.erdosproblems.com/forum/thread/230

Informal authors:
- Jean-Pierre Kahane

Formal authors:
- Codex
- GPT-5.6 Sol

URLs:
- https://github.com/plby/lean-proofs/blob/main/ErdosProblems/Erdos230.md
-/
/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ErdosProblems.Erdos230.Construction

/-!
# Erdős Problem 230

Erdős and Newman asked whether every polynomial

`P(z) = a₁ z + ⋯ + aₙ zⁿ`,  `‖aₖ‖ = 1`,

has circle maximum at least `(1 + c) * sqrt n` for some absolute `c > 0`.
The answer is negative.  The Gaussian-smoothed quadratic chirp constructed
in the supporting modules, followed by a finite Rademacher chord correction,
produces arbitrarily large unimodular polynomials with uniform upper norm
`(1 + o(1)) * sqrt n`.
-/

namespace Erdos230

/-- The negative resolution of Erdős Problem 230. -/
theorem not_erdos_230 :
    ¬ (∃ c : ℝ, 0 < c ∧
      ∀ n : ℕ, 2 ≤ n →
        ∀ a : Fin n → ℂ, IsUnimodular a →
          (1 + c) * Real.sqrt n ≤ circleMaximum a) :=
  not_erdos230Claim_of_ultraflat_upper
    (hasUltraflatUpper_of_angular
      (hasAngularUltraflatUpper_of_power_examples hasPowerUpperExamples))

end Erdos230

#print axioms Erdos230.not_erdos_230

alias _root_.Erdos230.erdos_230 := _root_.Erdos230.not_erdos_230
