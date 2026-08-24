/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

namespace Erdos922

def HasLargeIndependentSets {V : Type u} [Finite V]
    (G : SimpleGraph V) (k : ℕ) : Prop :=
  ∀ H : G.Subgraph, ∃ I : Finset H.verts,
    H.coe.IsIndepSet I ∧ H.verts.ncard ≤ 2 * I.card + k

theorem erdos_922 {V : Type u} [Finite V] (G : SimpleGraph V) (k : ℕ)
    (hG : HasLargeIndependentSets G k) :
    G.chromaticNumber ≤ ((k + 2 : ℕ) : ℕ∞) := by
  sorry

end Erdos922
