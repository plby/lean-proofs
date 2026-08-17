/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
# Erdős Problem 480

Chung and Graham's reciprocal-jump argument gives the stronger finite bound
`3 / 7`: every thirteen points of `[0,1]` contain a suitable pair.  Sliding
this window and applying finite pigeonhole yields one frequently occurring
gap, from which the stated `liminf` bound follows.
-/

import Mathlib

open Filter

namespace Erdos480

syntax (name := answerSyntax480) "answer(" term ")" : term
macro_rules | `(answer($t)) => `($t)

theorem erdos_480 : answer(True) ↔ ∀ (x : ℕ → ℝ), (∀ n, x n ∈ Set.Icc 0 1) →
    ⨅ (n : ℕ+), atTop.liminf (fun m => (n : ℕ) * |x (m + (n : ℕ)) - x m|) ≤
      1 / √5 := by
  sorry
