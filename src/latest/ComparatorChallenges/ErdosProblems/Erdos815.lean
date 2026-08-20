import Mathlib

open Classical Finset Set SimpleGraph

noncomputable section

attribute [local instance] Classical.propDecidable

namespace Erdos815

noncomputable def DegreeThreeCritical {V : Type*} [Fintype V]
    (G : SimpleGraph V) : Prop :=
  G.edgeFinset.card = 2 * Fintype.card V - 2 ∧
    ∀ s : Set V, s ≠ Set.univ → (G.induce s).minDegree ≤ 2

end Erdos815

namespace Erdos815

def Erdos815Statement : Prop :=
  ∀ k : ℕ, 3 ≤ k → ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
    ∀ G : SimpleGraph (Fin n),
      DegreeThreeCritical G → cycleGraph k ⊑ G

end Erdos815

namespace Erdos815

theorem erdos_815 : False ↔ Erdos815Statement := by
  sorry

end Erdos815

end
