/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

open Filter SimpleGraph Set Real
open scoped Topology BigOperators ENNReal NNReal

namespace Erdos615


open scoped Classical in
theorem erdos_615 :
    ¬ ∃ c : ℝ, 0 < c ∧ ∀ᶠ (n : ℕ) in atTop,
      ∀ G : SimpleGraph (Fin n), (1 / 8 - c) * n ^ 2 ≤ G.edgeFinset.card →
        ¬ G.CliqueFree 4 ∨ (n : ℝ) / Real.log n ≤ G.indepNum := by
  sorry
