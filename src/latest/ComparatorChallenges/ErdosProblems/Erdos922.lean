import Mathlib

open SimpleGraph
open scoped Classical
open Function

noncomputable section


namespace Erdos922

open scoped Classical in
def HasLargeIndependentSets {V : Type u} [Finite V]
    (G : SimpleGraph V) (k : ℕ) : Prop :=
  ∀ H : G.Subgraph, ∃ I : Finset H.verts,
    H.coe.IsIndepSet I ∧ H.verts.ncard ≤ 2 * I.card + k

end Erdos922

namespace Erdos922

open scoped Classical in
theorem erdos_922 {V : Type u} [Finite V] (G : SimpleGraph V) (k : ℕ)
    (hG : HasLargeIndependentSets G k) :
    G.chromaticNumber ≤ ((k + 2 : ℕ) : ℕ∞) := by
  sorry

end Erdos922

end
