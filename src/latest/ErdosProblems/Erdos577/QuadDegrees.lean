import ErdosProblems.Erdos577.QuadScores

/-! The internal degree at a four-cycle vertex is two plus its diagonal indicator. -/

namespace Erdos577.Quadrilateral

open Finset
open scoped BigOperators

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

lemma degreeIn_eq (q : Quadrilateral G) (i : Fin 4) :
    degreeIn G (q i) q.support = 2 + (if G.Adj (q i) (q (i + 2)) then 1 else 0) := by
  have hinj : Function.Injective (q : Fin 4 → V) := q.injective
  have h01 : G.Adj (q 0) (q 1) := q.adjacent 0
  have h12 : G.Adj (q 1) (q 2) := q.adjacent 1
  have h23 : G.Adj (q 2) (q 3) := q.adjacent 2
  have h30 : G.Adj (q 3) (q 0) := q.adjacent 3
  have h10 := h01.symm
  have h21 := h12.symm
  have h32 := h23.symm
  have h03 := h30.symm
  have h20 : G.Adj (q 2) (q 0) ↔ G.Adj (q 0) (q 2) := G.adj_comm _ _
  have h31 : G.Adj (q 3) (q 1) ↔ G.Adj (q 1) (q 3) := G.adj_comm _ _
  rw [support, degreeIn_image G _ _ _ hinj]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  let row (j : Fin 4) : ℕ :=
    (if G.Adj (q j) (q 0) then 1 else 0) +
      ((if G.Adj (q j) (q 1) then 1 else 0) +
        ((if G.Adj (q j) (q 2) then 1 else 0) +
          ((if G.Adj (q j) (q 3) then 1 else 0) + 0)))
  change row i = _
  fin_cases i
  · change row 0 = 2 + (if G.Adj (q 0) (q 2) then 1 else 0)
    simp only [row, h01, h03, SimpleGraph.irrefl, if_true, if_false]
    omega
  · change row 1 = 2 + (if G.Adj (q 1) (q 3) then 1 else 0)
    simp only [row, h10, h12, SimpleGraph.irrefl, if_true, if_false]
    omega
  · change row 2 = 2 + (if G.Adj (q 2) (q 0) then 1 else 0)
    simp only [row, h21, h23, SimpleGraph.irrefl, if_true, if_false]
    omega
  · change row 3 = 2 + (if G.Adj (q 3) (q 1) then 1 else 0)
    simp only [row, h30, h32, SimpleGraph.irrefl, if_true, if_false]
    omega

end Erdos577.Quadrilateral
