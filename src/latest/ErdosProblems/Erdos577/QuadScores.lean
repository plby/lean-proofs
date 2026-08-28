import ErdosProblems.Erdos577.CopyCounts

/-! The induced edge count of a four-cycle is determined by its two diagonals. -/

namespace Erdos577.Quadrilateral

open Finset
open scoped BigOperators

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

lemma edgeCount_eq (q : Quadrilateral G) :
    edgeCount G q.support = 4 + (if G.Adj (q 0) (q 2) then 1 else 0) +
      (if G.Adj (q 1) (q 3) then 1 else 0) := by
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
  have hc := contacts_self_eq_twice_edgeCount G q.support
  rw [support, contacts_image_left G _ _ hinj] at hc
  simp_rw [degreeIn_image G _ _ _ hinj] at hc
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero] at hc
  let row (i : Fin 4) : ℕ :=
    (if G.Adj (q i) (q 0) then 1 else 0) +
      ((if G.Adj (q i) (q 1) then 1 else 0) +
        ((if G.Adj (q i) (q 2) then 1 else 0) +
          ((if G.Adj (q i) (q 3) then 1 else 0) + 0)))
  change row 0 + (row 1 + (row 2 + (row 3 + 0))) =
    2 * edgeCount G (univ.image q) at hc
  change edgeCount G (univ.image q) = _
  by_cases h02 : G.Adj (q 0) (q 2) <;> by_cases h13 : G.Adj (q 1) (q 3) <;>
    simp only [row, h01, h12, h23, h30, h10, h21, h32, h03, h20, h31, h02, h13,
      SimpleGraph.irrefl, if_true, if_false]
      at hc ⊢ <;> omega

end Erdos577.Quadrilateral
