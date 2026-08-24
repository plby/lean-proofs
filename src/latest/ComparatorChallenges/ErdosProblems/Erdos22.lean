/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

open Filter

namespace Erdos22

open scoped Classical in
theorem erdos_22 :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ (n : ℕ) in atTop,
      ∃ G : SimpleGraph (Fin n), G.CliqueFree 4 ∧
        (G.indepNum : ℝ) ≤ ε * n ∧ (n : ℝ) ^ 2 / 8 ≤ G.edgeFinset.card := by
  sorry
