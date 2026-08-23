import Mathlib

open Classical Finset Set SimpleGraph

noncomputable section


namespace Erdos815

open scoped Classical in
noncomputable def DegreeThreeCritical {V : Type*} [Fintype V]
    (G : SimpleGraph V) : Prop :=
  G.edgeFinset.card = 2 * Fintype.card V - 2 ∧
    ∀ s : Set V, s ≠ Set.univ → (G.induce s).minDegree ≤ 2

end Erdos815

namespace Erdos815

open scoped Classical in
def Erdos815Statement : Prop :=
  ∀ k : ℕ, 3 ≤ k → ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
    ∀ G : SimpleGraph (Fin n),
      DegreeThreeCritical G → cycleGraph k ⊑ G

end Erdos815

namespace Erdos815

open scoped Classical in
theorem erdos_815 : ¬ Erdos815Statement := by
  sorry

end Erdos815

end
