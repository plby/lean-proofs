import ErdosProblems.Erdos577.FullLeafHeavyAdjacentEdges

/-! Preserve the adjacent first row when labeling the unique diagonal of a five-edge block. -/

namespace Erdos577.FullLeafHeavy

open Finset

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

lemma adjacent_diamond_labels (q : Quadrilateral G) (x : V)
    (hrow : ∀ i : Fin 4, G.Adj x (q i) ↔ i = 0 ∨ i = 1)
    (hfive : edgeCount G q.support = 5) :
    ∃ v : Quadrilateral G, v.support = q.support ∧
      (∀ i : Fin 4, G.Adj x (v i) ↔ i = 0 ∨ i = 1) ∧
      G.Adj (v 0) (v 2) ∧ ¬G.Adj (v 1) (v 3) := by
  have he := q.edgeCount_eq
  by_cases h02 : G.Adj (q 0) (q 2)
  · refine ⟨q, rfl, hrow, h02, ?_⟩
    intro h13
    rw [if_pos h02, if_pos h13] at he
    omega
  · have h13 : G.Adj (q 1) (q 3) := by
      by_contra h13
      rw [if_neg h02, if_neg h13] at he
      omega
    refine ⟨(q.rotate 1).reverse, (q.rotate 1).reverse_support.trans (q.rotate_support 1),
      ?_, h13, h02⟩
    intro i
    rw [Quadrilateral.reverse_apply, Quadrilateral.rotate_apply, hrow]
    fin_cases i <;> decide

omit [DecidableRel G.Adj] in
lemma diamond_low_triangle (q : Quadrilateral G) (hdiag : G.Adj (q 0) (q 2))
    (i : Fin 4) (hi : i = 1 ∨ i = 3) : G.IsNClique 3 (q.support.erase (q i)) := by
  have hinj : Function.Injective (q : Fin 4 → V) := q.injective
  rcases hi with rfl | rfl
  · have he := congrArg (fun t : Finset (Fin 4) ↦ t.image q)
      (show ({0, 2, 3} : Finset (Fin 4)) = univ.erase 1 by decide)
    have hs : q.support.erase (q 1) = {q 0, q 2, q 3} := by
      simpa only [image_insert, image_singleton, image_erase hinj, Quadrilateral.support]
        using he.symm
    rw [hs]
    exact SimpleGraph.is3Clique_triple_iff.mpr ⟨hdiag, (q.adjacent 3).symm, q.adjacent 2⟩
  · have he := congrArg (fun t : Finset (Fin 4) ↦ t.image q)
      (show ({0, 1, 2} : Finset (Fin 4)) = univ.erase 3 by decide)
    have hs : q.support.erase (q 3) = {q 0, q 1, q 2} := by
      simpa only [image_insert, image_singleton, image_erase hinj, Quadrilateral.support]
        using he.symm
    rw [hs]
    exact SimpleGraph.is3Clique_triple_iff.mpr ⟨q.adjacent 0, hdiag, q.adjacent 1⟩

lemma diamond_three_replaces_lows (q : Quadrilateral G) (hdiag : G.Adj (q 0) (q 2))
    {u : V} (hu : u ∉ q.support) (hthree : 3 ≤ degreeIn G u q.support)
    (i : Fin 4) (hi : i = 1 ∨ i = 3) :
    QuadOn G (insert u (q.support.erase (q i))) := by
  have he := degreeIn_erase_add G u (q i) ((q.mem_support _).mpr ⟨i, rfl⟩)
  have htwo : 2 ≤ degreeIn G u (q.support.erase (q i)) := by split_ifs at he <;> omega
  exact QuadOn.of_triangle (diamond_low_triangle q hdiag i hi)
    (fun hh ↦ hu (mem_erase.mp hh).2) htwo

omit [DecidableRel G.Adj] in
lemma diamond_first_replaces_last (q : Quadrilateral G) (hdiag : G.Adj (q 0) (q 2))
    {x : V} (hx : x ∉ q.support) (h0 : G.Adj x (q 0)) (h1 : G.Adj x (q 1)) :
    QuadOn G (insert x (q.support.erase (q 3))) :=
  q.replace_using_path x hx 3 0 2 1 (by decide) (by decide) h0 hdiag (q.adjacent 1).symm h1

end Erdos577.FullLeafHeavy
