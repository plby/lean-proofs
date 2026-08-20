import Mathlib

open Finset SimpleGraph

noncomputable section

attribute [local instance] Classical.propDecidable

namespace Erdos814

def edgeThreshold (k n : ℕ) : ℕ :=
  (k - 1) * (n + 2 - k) + (k - 2).choose 2 + 1

end Erdos814

namespace Erdos814

def Erdos814Statement : Prop :=
  ∀ k : ℕ, 2 ≤ k →
    ∃ c : ℝ, 0 < c ∧
      ∀ n : ℕ, k - 1 ≤ n →
        ∀ (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
          G.edgeFinset.card = edgeThreshold k n →
            ∃ S : Finset (Fin n),
              S.Nonempty ∧
              (S.card : ℝ) ≤ (1 - c) * (n : ℝ) ∧
              k ≤ (G.induce (↑S : Set (Fin n))).minDegree

end Erdos814

namespace Erdos814

theorem erdos_814 : True ↔ Erdos814Statement := by
  sorry

end Erdos814

end
