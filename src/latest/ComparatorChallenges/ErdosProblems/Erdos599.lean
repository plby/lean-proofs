import Erdos599.Definitions
import Mathlib.Order.CompletePartialOrder

open SimpleGraph

universe u

namespace Erdos599

/-- Every pair of disjoint independent vertex sets in a possibly infinite
graph admits an orthogonal path packing and separator. -/
theorem erdos_599 {V : Type u} (G : SimpleGraph V) (A B : Set V)
    (hAB : Disjoint A B) (hA : G.IsIndepSet A) (hB : G.IsIndepSet B) :
    ∃ (P : Set (ABPath G A B)) (S : Set V),
      IsPathPacking P ∧ IsABSeparator G A B S ∧ IsOrthogonal P S := by
  sorry

end Erdos599
