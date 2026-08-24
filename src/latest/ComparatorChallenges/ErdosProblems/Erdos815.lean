/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

open SimpleGraph

namespace Erdos815

open scoped Classical in
noncomputable def DegreeThreeCritical {V : Type*} [Fintype V]
    (G : SimpleGraph V) : Prop :=
  G.edgeFinset.card = 2 * Fintype.card V - 2 ∧
    ∀ s : Set V, s ≠ Set.univ → (G.induce s).minDegree ≤ 2

theorem not_erdos_815 :
    ¬ (∀ k : ℕ, 3 ≤ k → ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∀ G : SimpleGraph (Fin n),
        Erdos815.DegreeThreeCritical G → SimpleGraph.cycleGraph k ⊑ G) := by
  sorry

end Erdos815
