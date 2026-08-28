import ErdosProblems.Erdos577.QuadDegrees
import ErdosProblems.Erdos577.UnattachedTransport

/-! Read each cycle vertex's opposite edge from the retained diagonal mask. -/

namespace Erdos577.Quadrilateral

variable {V : Type*} {G : SimpleGraph V} [DecidableRel G.Adj]

lemma diagonal_bit_iff (q : Quadrilateral G) (i : Fin 4) :
    (Unattached.diagonal q).val.testBit (i.val % 2) = true ↔ G.Adj (q i) (q (i + 2)) := by
  fin_cases i
  · change (Unattached.diagonal q).val.testBit 0 = true ↔ G.Adj (q 0) (q 2)
    exact Unattached.diagonal_first q
  · change (Unattached.diagonal q).val.testBit 1 = true ↔ G.Adj (q 1) (q 3)
    exact Unattached.diagonal_second q
  · change (Unattached.diagonal q).val.testBit 0 = true ↔ G.Adj (q 2) (q 0)
    exact (Unattached.diagonal_first q).trans (G.adj_comm _ _)
  · change (Unattached.diagonal q).val.testBit 1 = true ↔ G.Adj (q 3) (q 1)
    exact (Unattached.diagonal_second q).trans (G.adj_comm _ _)

lemma degreeIn_eq_two_of_diagonal_false [DecidableEq V] (q : Quadrilateral G) (i : Fin 4)
    (h : (Unattached.diagonal q).val.testBit (i.val % 2) = false) :
    degreeIn G (q i) q.support = 2 := by
  have hn : ¬G.Adj (q i) (q (i + 2)) := by
    intro he
    rw [(q.diagonal_bit_iff i).mpr he] at h
    contradiction
  rw [q.degreeIn_eq, if_neg hn, Nat.add_zero]

end Erdos577.Quadrilateral
