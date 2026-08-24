/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

open scoped SimpleGraph

namespace Erdos546

def GraphRamseyProperty {v : ℕ} (G : SimpleGraph (Fin v)) (N : ℕ) : Prop :=
  ∀ R : SimpleGraph (Fin N), G ⊑ R ∨ G ⊑ Rᶜ

noncomputable def graphRamseyNumber {v : ℕ} (G : SimpleGraph (Fin v)) : ℕ :=
  sInf {N : ℕ | GraphRamseyProperty G N}

theorem erdos_546 :
    ∃ C : ℝ, 0 < C ∧
      ∀ (v : ℕ) (G : SimpleGraph (Fin v)) [DecidableRel G.Adj],
        (∀ x, ¬ G.IsIsolated x) →
          (graphRamseyNumber G : ℝ) ≤
            Real.rpow 2 (C * Real.sqrt (G.edgeFinset.card : ℝ)) := by
  sorry

end Erdos546
