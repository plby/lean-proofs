/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

namespace Erdos1008

def is_C4 {V : Type} [DecidableEq V] (s : Finset (Sym2 V)) : Prop :=
  s.card = 4 ∧ ¬ (SimpleGraph.cycleGraph 4).Free (SimpleGraph.fromEdgeSet (s : Set (Sym2 V)))

theorem erdos_1008 {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
  ∃ (S' : Finset (Sym2 V)), S' ⊆ G.edgeFinset ∧
  (∀ s, s ⊆ S' → ¬is_C4 s) ∧
  (S'.card : ℝ) ≥ ((1 : ℝ) / 2) * (G.edgeFinset.card : ℝ) ^ ((2 : ℝ) / 3) := by
  sorry

end Erdos1008
