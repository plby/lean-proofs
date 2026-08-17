import Mathlib

open SimpleGraph
open scoped Classical
open Function

noncomputable section

attribute [local instance] Classical.propDecidable

namespace Erdos922

def HasLargeIndependentSets {V : Type u} [Finite V]
    (G : SimpleGraph V) (k : ℕ) : Prop :=
  ∀ H : G.Subgraph, ∃ I : Finset H.verts,
    H.coe.IsIndepSet I ∧ H.verts.ncard ≤ 2 * I.card + k

end Erdos922

namespace Erdos922

theorem erdos_922 {V : Type u} [Finite V] (G : SimpleGraph V) (k : ℕ)
    (hG : HasLargeIndependentSets G k) :
    G.chromaticNumber ≤ ((k + 2 : ℕ) : ℕ∞) := by
  sorry

end Erdos922

end
