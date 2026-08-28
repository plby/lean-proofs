import ErdosProblems.Erdos577.Blocks
import ErdosProblems.Erdos577.FourTuples
import ErdosProblems.Erdos577.QuadSets

/-! Two adjacent pairs and three cross contacts contain a genuine four-cycle. -/

namespace Erdos577

open Finset

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

lemma QuadOn.of_three_cross (e : Fin 4 ↪ V) (h01 : G.Adj (e 0) (e 1))
    (h23 : G.Adj (e 2) (e 3))
    (hcross : 3 ≤ (if G.Adj (e 0) (e 2) then 1 else 0) +
      (if G.Adj (e 0) (e 3) then 1 else 0) + (if G.Adj (e 1) (e 2) then 1 else 0) +
      (if G.Adj (e 1) (e 3) then 1 else 0)) : QuadOn G {e 0, e 1, e 2, e 3} := by
  have hmatch : (G.Adj (e 0) (e 2) ∧ G.Adj (e 1) (e 3)) ∨
      (G.Adj (e 0) (e 3) ∧ G.Adj (e 1) (e 2)) := by
    by_cases h02 : G.Adj (e 0) (e 2) <;> by_cases h03 : G.Adj (e 0) (e 3) <;>
      by_cases h12 : G.Adj (e 1) (e 2) <;> by_cases h13 : G.Adj (e 1) (e 3) <;> simp_all
  have hne (i j : Fin 4) (hij : i ≠ j) : e i ≠ e j := fun he ↦ hij (e.injective he)
  rcases hmatch with hh | hh
  · have hq := QuadOn.of_vertices (hne 0 3 (by decide)) (hne 1 2 (by decide))
      h01 hh.2 h23.symm hh.1.symm
    convert hq using 1
    ext u
    simp only [mem_insert, mem_singleton]
    tauto
  · exact QuadOn.of_vertices (hne 0 2 (by decide)) (hne 1 3 (by decide))
      h01 hh.2 h23 hh.1.symm

lemma Quadrilateral.degree_last_pair (q : Quadrilateral G) (z : V)
    (hzero : ¬G.Adj z (q 0)) (hone : ¬G.Adj z (q 1)) :
    degreeIn G z q.support = (if G.Adj z (q 2) then 1 else 0) +
      (if G.Adj z (q 3) then 1 else 0) := by
  rw [Quadrilateral.support, degreeIn_image G z univ q q.injective]
  simp only [Fin.sum_univ_four, if_neg hzero, if_neg hone, zero_add]

end Erdos577
