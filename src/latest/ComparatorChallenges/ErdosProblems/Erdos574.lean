/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

open Filter
open scoped Asymptotics

namespace Erdos574

def FreeConsecutiveCycles {V : Type*} (k : ℕ) (G : SimpleGraph V) : Prop :=
  (SimpleGraph.cycleGraph (2 * k - 1)).Free G ∧
    (SimpleGraph.cycleGraph (2 * k)).Free G

noncomputable def consecutiveCycleExtremalNumber (k n : ℕ) : ℕ :=
  by
    classical
    exact Finset.sup {G : SimpleGraph (Fin n) | FreeConsecutiveCycles k G}
      (fun G ↦ G.edgeFinset.card)

noncomputable def erdos574Comparison (k n : ℕ) : ℝ :=
  ((n : ℝ) / 2) ^ (1 + 1 / (k : ℝ))

theorem not_erdos_574 :
    ¬ (∀ k : ℕ, 2 ≤ k →
      (fun n : ℕ ↦ (consecutiveCycleExtremalNumber k n : ℝ)) ~[atTop]
        erdos574Comparison k) := by
  sorry

end Erdos574
