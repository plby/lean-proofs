/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

open Filter

namespace Erdos480

theorem erdos_480 : ∀ (x : ℕ → ℝ), (∀ n, x n ∈ Set.Icc 0 1) →
    ⨅ (n : ℕ+), atTop.liminf (fun m => (n : ℕ) * |x (m + (n : ℕ)) - x m|) ≤
      1 / √5 := by
  sorry
