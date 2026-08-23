import Mathlib

open scoped SimpleGraph
open SimpleGraph

noncomputable section


namespace Erdos546

open scoped Classical in
def GraphRamseyProperty {v : ℕ} (G : SimpleGraph (Fin v)) (N : ℕ) : Prop :=
  ∀ R : SimpleGraph (Fin N), G ⊑ R ∨ G ⊑ Rᶜ

end Erdos546

namespace Erdos546

open scoped Classical in
noncomputable def graphRamseyNumber {v : ℕ} (G : SimpleGraph (Fin v)) : ℕ :=
  sInf {N : ℕ | GraphRamseyProperty G N}

end Erdos546

namespace Erdos546

open scoped Classical in
theorem erdos_546 :
    ∃ C : ℝ, 0 < C ∧
      ∀ (v : ℕ) (G : SimpleGraph (Fin v)) [DecidableRel G.Adj],
        (∀ x, ¬ G.IsIsolated x) →
          (graphRamseyNumber G : ℝ) ≤
            Real.rpow 2 (C * Real.sqrt (G.edgeFinset.card : ℝ)) := by
  sorry

end Erdos546

end
