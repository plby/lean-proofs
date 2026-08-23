import Mathlib

namespace Erdos1037

set_option linter.style.setOption false
set_option linter.style.longLine false
set_option linter.flexible false


open scoped Classical in
def NumDistinctDegrees {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  (Finset.univ.image (fun v => G.degree v)).card
end Erdos1037

open Erdos1037



namespace Erdos1037

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
