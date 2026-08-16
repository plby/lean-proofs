/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import Mathlib

/-!
# Erdős Problem 965

There is a two-coloring of `ℝ` for which every uncountable set has two distinct
pair sums of different colors.  Thus the answer is negative.
-/

syntax (name := answerSyntax965) "answer(" term ")" : term
macro_rules | `(answer($t)) => `($t)

namespace Erdos965

theorem erdos_965 :
    answer(False) ↔ ∀ f : ℝ → Fin 2, ∃ A : Set ℝ, ¬ A.Countable ∧
      ∀ᵉ (a ∈ A) (b ∈ A) (c ∈ A) (d ∈ A), a ≠ b → c ≠ d →
        f (a + b) = f (c + d) := by
  sorry
