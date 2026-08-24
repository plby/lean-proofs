/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

namespace Erdos1037

def NumDistinctDegrees {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  (Finset.univ.image (fun v => G.degree v)).card

open scoped Classical in
theorem not_erdos_1037 :
  ¬(
    ∀ ε : ℝ, 0 < ε →
    ∀ C : ℝ, 0 < C →
    ∃ n₀ : ℕ, ∀ n ≥ n₀,
      ∀ G : SimpleGraph (Fin n),
        (NumDistinctDegrees G : ℝ) ≥ (1 / 2 + ε) * n →
        (C * Real.log n ≤ (G.cliqueNum : ℝ) ∨
         C * Real.log n ≤ (G.indepNum : ℝ))
  ) := by
  sorry

end Erdos1037
