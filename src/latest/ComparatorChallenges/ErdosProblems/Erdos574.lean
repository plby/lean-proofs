/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

open Filter Finset Fintype SimpleGraph
open scoped Asymptotics BigOperators

noncomputable section

namespace Erdos574

open scoped Classical in
def FreeConsecutiveCycles {V : Type*} (k : ℕ) (G : SimpleGraph V) : Prop :=
  (SimpleGraph.cycleGraph (2 * k - 1)).Free G ∧
    (SimpleGraph.cycleGraph (2 * k)).Free G

end Erdos574

namespace Erdos574

open scoped Classical in
noncomputable def consecutiveCycleExtremalNumber (k n : ℕ) : ℕ :=
  by
    classical
    exact Finset.sup {G : SimpleGraph (Fin n) | FreeConsecutiveCycles k G}
      (fun G ↦ G.edgeFinset.card)

end Erdos574

namespace Erdos574

open scoped Classical in
noncomputable def erdos574Comparison (k n : ℕ) : ℝ :=
  ((n : ℝ) / 2) ^ (1 + 1 / (k : ℝ))

end Erdos574

namespace Erdos574

open scoped Classical in
def erdos_574 : Prop :=
  ∀ k : ℕ, 2 ≤ k →
    (fun n : ℕ ↦ (consecutiveCycleExtremalNumber k n : ℝ)) ~[atTop]
      erdos574Comparison k

end Erdos574

namespace Erdos574

open scoped Classical in
theorem not_erdos_574 : ¬ erdos_574 := by
  sorry

end Erdos574

end
