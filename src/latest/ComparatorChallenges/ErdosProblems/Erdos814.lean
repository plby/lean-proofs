/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

namespace Erdos814

def edgeThreshold (k n : ℕ) : ℕ :=
  (k - 1) * (n + 2 - k) + (k - 2).choose 2 + 1

theorem erdos_814 :
    ∀ k : ℕ, 2 ≤ k →
      ∃ c : ℝ, 0 < c ∧
        ∀ n : ℕ, k - 1 ≤ n →
          ∀ (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
            G.edgeFinset.card = Erdos814.edgeThreshold k n →
              ∃ S : Finset (Fin n),
                S.Nonempty ∧
                (S.card : ℝ) ≤ (1 - c) * (n : ℝ) ∧
                k ≤ (G.induce (↑S : Set (Fin n))).minDegree := by
  sorry

end Erdos814
