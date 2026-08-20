import Mathlib

noncomputable section

attribute [local instance] Classical.propDecidable

namespace Erdos916

variable {V : Type u} [Fintype V] [DecidableEq V]

def HasWheelWitness (G : SimpleGraph V) [DecidableRel G.Adj] : Prop :=
  ∃ (a : V) (p : G.Walk a a) (x : V),
    p.IsCycle ∧ x ∉ p.support ∧
      3 ≤ (G.neighborFinset x ∩ p.support.toFinset).card

end Erdos916

namespace Erdos916

theorem erdos916 {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hcard : 4 ≤ Fintype.card V)
    (hedges : G.edgeFinset.card = 2 * Fintype.card V - 2) :
    HasWheelWitness G := by
  sorry

end Erdos916

end
