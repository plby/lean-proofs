import ErdosProblems.Erdos577.FirstPawSixModel

/-! Exact counting of the ten allowed contacts in pattern (6). -/

namespace Erdos577.FirstPawSix

open Finset

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

lemma allowed_contact_count (p : Paw G) (q : Quadrilateral G) (h : PawBlock.Pattern6 p q) :
    (univ.filter (fun i : Fin 10 ↦ G.Adj (p.vertices (row i)) (q (column i)))).card =
      contacts G p.support q.support := by
  rw [card_eq_sum_ones, sum_filter, Paw.support, tupleSupport,
    contacts_image_left G univ p.vertices p.vertices.injective]
  simp_rw [Quadrilateral.support, degreeIn_image G _ univ q q.injective]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  have hn02 : ¬G.Adj (p.vertices 0) (q 2) := by
    intro he
    exact (by decide : ¬(3 : ℕ).testBit 2 = true) (allowed_row p q h 0 2 he)
  have hn03 : ¬G.Adj (p.vertices 0) (q 3) := by
    intro he
    exact (by decide : ¬(3 : ℕ).testBit 3 = true) (allowed_row p q h 0 3 he)
  have hn23 : ¬G.Adj (p.vertices 2) (q 3) := by
    intro he
    exact (by decide : ¬(7 : ℕ).testBit 3 = true) (allowed_row p q h 2 3 he)
  have hn31 : ¬G.Adj (p.vertices 3) (q 1) := by
    intro he
    exact (by decide : ¬(1 : ℕ).testBit 1 = true) (allowed_row p q h 3 1 he)
  have hn32 : ¬G.Adj (p.vertices 3) (q 2) := by
    intro he
    exact (by decide : ¬(1 : ℕ).testBit 2 = true) (allowed_row p q h 3 2 he)
  have hn33 : ¬G.Adj (p.vertices 3) (q 3) := by
    intro he
    exact (by decide : ¬(1 : ℕ).testBit 3 = true) (allowed_row p q h 3 3 he)
  change
    (if G.Adj (p.vertices 0) (q 0) then 1 else 0) +
      ((if G.Adj (p.vertices 0) (q 1) then 1 else 0) +
        ((if G.Adj (p.vertices 1) (q 0) then 1 else 0) +
          ((if G.Adj (p.vertices 1) (q 1) then 1 else 0) +
            ((if G.Adj (p.vertices 1) (q 2) then 1 else 0) +
              ((if G.Adj (p.vertices 1) (q 3) then 1 else 0) +
                ((if G.Adj (p.vertices 2) (q 0) then 1 else 0) +
                  ((if G.Adj (p.vertices 2) (q 1) then 1 else 0) +
                    ((if G.Adj (p.vertices 2) (q 2) then 1 else 0) +
                      ((if G.Adj (p.vertices 3) (q 0) then 1 else 0) +
                        (0)))))))))) =
    ((if G.Adj (p.vertices 0) (q 0) then 1 else 0) +
      ((if G.Adj (p.vertices 0) (q 1) then 1 else 0) +
        ((if G.Adj (p.vertices 0) (q 2) then 1 else 0) +
          ((if G.Adj (p.vertices 0) (q 3) then 1 else 0) +
            (0))))) +
      (((if G.Adj (p.vertices 1) (q 0) then 1 else 0) +
      ((if G.Adj (p.vertices 1) (q 1) then 1 else 0) +
        ((if G.Adj (p.vertices 1) (q 2) then 1 else 0) +
          ((if G.Adj (p.vertices 1) (q 3) then 1 else 0) +
            (0))))) +
        (((if G.Adj (p.vertices 2) (q 0) then 1 else 0) +
      ((if G.Adj (p.vertices 2) (q 1) then 1 else 0) +
        ((if G.Adj (p.vertices 2) (q 2) then 1 else 0) +
          ((if G.Adj (p.vertices 2) (q 3) then 1 else 0) +
            (0))))) +
          (((if G.Adj (p.vertices 3) (q 0) then 1 else 0) +
      ((if G.Adj (p.vertices 3) (q 1) then 1 else 0) +
        ((if G.Adj (p.vertices 3) (q 2) then 1 else 0) +
          ((if G.Adj (p.vertices 3) (q 3) then 1 else 0) +
            (0))))) +
            (0))))
  simp only [if_neg hn02, if_neg hn03, if_neg hn23, if_neg hn31, if_neg hn32, if_neg hn33]
  omega

end Erdos577.FirstPawSix
