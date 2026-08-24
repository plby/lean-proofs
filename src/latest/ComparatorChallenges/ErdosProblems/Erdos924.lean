/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

namespace Erdos924

def IsEdgeRamseyForClique {V : Type*} (G : SimpleGraph V) (k l : ℕ) : Prop :=
  ∀ C : SimpleGraph.EdgeLabeling G (Fin k),
    ∃ i : Fin k, ∃ S : Finset V, (C.labelGraph i).IsNClique l S

theorem erdos_924 :
    ∀ k l : ℕ, 2 ≤ k → 3 ≤ l →
      ∃ (V : Type) (_ : Fintype V) (G : SimpleGraph V),
        G.CliqueFree (l + 1) ∧ IsEdgeRamseyForClique G k l := by
  sorry

end Erdos924
