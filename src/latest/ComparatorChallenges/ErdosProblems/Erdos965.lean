/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos965.FiniteColoring
import ErdosProblems.Erdos965.FiniteMain
import ErdosProblems.Erdos965.HamelTransfer

/-!
# Erdős Problem 965

Komjáth's ZFC finite-union coloring, transferred through a Hamel basis of
`ℝ` over `ℚ`, gives a two-coloring for which every uncountable set has two
distinct pair sums of different colors.  Thus the answer is negative.

The detailed mathematical proof and Leanization map are in `tex/965.tex`.
-/

syntax (name := answerSyntax965) "answer(" term ")" : term
macro_rules | `(answer($t)) => `($t)

namespace Erdos965

theorem erdos_965 :
    answer(False) ↔ ∀ f : ℝ → Fin 2, ∃ A : Set ℝ, ¬ A.Countable ∧
      ∀ᵉ (a ∈ A) (b ∈ A) (c ∈ A) (d ∈ A), a ≠ b → c ≠ d →
        f (a + b) = f (c + d) := by
  sorry

