/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

namespace Erdos577

/-- Minimum degree `2 * k` on `4 * k` vertices gives `k` disjoint ordinary four-cycles. -/
theorem erdos_577 {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (k : ℕ) (hcard : Fintype.card V = 4 * k) (hdeg : 2 * k ≤ G.minDegree) :
    ∃ f : Fin k × Fin 4 ↪ V, ∀ i j, G.Adj (f (i, j)) (f (i, j + 1)) := by
  sorry

end Erdos577
