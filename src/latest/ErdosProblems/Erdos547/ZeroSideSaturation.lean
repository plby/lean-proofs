import ErdosProblems.Erdos547.BipartiteFractional
import ErdosProblems.Erdos547.CappingLoss

/-!
# Saturation charged only to one side of a fractional matching
-/

namespace Erdos547.DPRS

open Finset SimpleGraph
open scoped BigOperators

variable {V : Type*} [Fintype V] {G : SimpleGraph V}

theorem FractionalMatching.saturation_le_total_of_zero_side (P : FractionalMatching G)
    (U : Finset V) (hcross : P.Crosses U) (w : EdgeWeights G) (c : V)
    (hzero : ∀ u ∈ U, min (w.weight c u) (P.load u) = 0) :
    w.saturation P.load c ≤ P.total := by
  classical
  rw [EdgeWeights.saturation, ← Finset.sum_add_sum_compl U]
  have hU : (∑ u ∈ U, min (w.weight c u) (P.load u)) = 0 :=
    Finset.sum_eq_zero hzero
  rw [hU, zero_add, ← hcross.swap.sum_load_side]
  exact Finset.sum_le_sum fun _ _ ↦ min_le_right _ _

end Erdos547.DPRS
