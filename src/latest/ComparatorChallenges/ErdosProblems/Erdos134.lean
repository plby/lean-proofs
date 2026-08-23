/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib


namespace Erdos134

open scoped Classical in
theorem erdos_134
    {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ G : SimpleGraph (Fin n),
      G.CliqueFree 3 →
      (∀ v : Fin n, (G.degree v : ℝ) < Real.rpow (n : ℝ) ((1 : ℝ) / 2 - ε)) →
      ∃ H : SimpleGraph (Fin n),
        G ≤ H ∧
        H.CliqueFree 3 ∧
        (∀ x y : Fin n, x ≠ y → H.Adj x y ∨ ∃ z, H.Adj x z ∧ H.Adj z y) ∧
        ((H.edgeFinset \ G.edgeFinset).card : ℝ) ≤ δ * (n : ℝ) ^ 2 := by
  sorry

end Erdos134
