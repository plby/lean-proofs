/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

open Filter SimpleGraph
open Set MeasureTheory
open scoped Classical ENNReal NNReal Pointwise Topology BigOperators

namespace Erdos533

theorem erdos_533 :
    ¬ ∀ δ : ℝ, 0 < δ → ∃ c : ℝ, 0 < c ∧ ∀ᶠ n : ℕ in atTop,
      ∀ G : SimpleGraph (Fin n), G.CliqueFree 5 →
        δ * (n : ℝ) ^ 2 ≤ G.edgeFinset.card →
          ∃ S : Finset (Fin n), c * n ≤ (S.card : ℝ) ∧
            G.CliqueFreeOn (S : Set (Fin n)) 3 := by
  sorry
