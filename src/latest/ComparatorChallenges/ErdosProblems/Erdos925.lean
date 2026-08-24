/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

namespace Erdos925

/-- An exact two-coloring of the edges of `G`, with neither color containing a triangle. -/
def AdmitsTriangleFreeTwoColoring {V : Type*} (G : SimpleGraph V) : Prop :=
  ∃ red blue : SimpleGraph V,
    Disjoint red blue ∧ red ⊔ blue = G ∧ red.CliqueFree 3 ∧ blue.CliqueFree 3

theorem not_erdos_925 :
    ¬ (∃ δ c : ℝ, 0 < δ ∧ 0 < c ∧ ∃ threshold : ℕ,
      ∀ (n : ℕ) (G : SimpleGraph (Fin n)), threshold ≤ n →
        Erdos925.AdmitsTriangleFreeTwoColoring G →
          c * (n : ℝ) ^ ((1 : ℝ) / 3 + δ) ≤ (G.indepNum : ℝ)) := by
  sorry

end Erdos925
