import ErdosProblems.Erdos577.DenseOutsideModel

/-! Strict improvements or the exact diamond rows at ten triangle contacts. -/

namespace Erdos577.DenseTriangle

open Finset

def Positive (diagonal : Fin 4) (m : ℕ) : Prop :=
  StrictImprovement (Unattached.graph diagonal m) univ (Unattached.oldEdges diagonal)

lemma Positive.mono {diagonal : Fin 4} {small large : ℕ}
    (hs : Positive diagonal small) (h : large &&& small = small) : Positive diagonal large := by
  let f := SimpleGraph.Copy.ofLE (Unattached.graph diagonal small)
    (Unattached.graph diagonal large) (Unattached.graph_mono diagonal h)
  change StrictImprovement (Unattached.graph diagonal large) univ (Unattached.oldEdges diagonal)
  simpa only [f, SimpleGraph.Copy.coe_ofLE, image_id] using hs.image f

/-- Two rows are full; the remaining row consists exactly of the diagonal
endpoints. Only the two diamond masks are permitted. -/
def DiamondRows (diagonal : Fin 4) (m : ℕ) : Prop :=
  diagonal ≠ 0 ∧ diagonal ≠ 3 ∧ ∃ low : Fin 3, ∀ i : Fin 3, ∀ j : Fin 4,
    m.testBit (4 * (i.val + 1) + j.val) =
      if i = low then diagonal.val.testBit (j.val % 2) else true

instance (diagonal : Fin 4) (m : ℕ) : Decidable (DiamondRows diagonal m) :=
  inferInstanceAs (Decidable (_ ∧ _))

end Erdos577.DenseTriangle
