import ErdosProblems.Erdos577.FullRowDenseShape

/-! Disjoint low rows at the thirteen-contact threshold meet the center row. -/

namespace Erdos577.FullRow

open Finset

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

lemma triangle_contacts_center_upper (p : Paw G) (j : Finset V) (hj : j.card = 4) :
    contacts G p.triangle j ≤ degreeIn G p.center j + 8 := by
  have hsum := sum_erase_add p.triangle (fun u ↦ degreeIn G u j) p.center_mem_triangle
  change contacts G (p.triangle.erase p.center) j + degreeIn G p.center j =
    contacts G p.triangle j at hsum
  have hrest := contacts_le_card_mul G (p.triangle.erase p.center) j
  rw [card_erase_of_mem p.center_mem_triangle, p.triangle_clique.card_eq, hj] at hrest
  omega

lemma exists_center_low_neighbor (p : Paw G) (v : Quadrilateral G) (j : Finset V)
    (hj : j.card = 4)
    (hheavy : 13 ≤ contacts G p.triangle j + degreeIn G (v 1) j + degreeIn G (v 3) j)
    (hsep : ∀ w ∈ j, ¬(G.Adj (v 1) w ∧ G.Adj (v 3) w)) :
    ∃ i : Fin 4, (i = 1 ∨ i = 3) ∧ ∃ w ∈ j, G.Adj p.center w ∧ G.Adj (v i) w := by
  by_contra hn
  have hxy : Disjoint (j.filter (G.Adj (v 1))) (j.filter (G.Adj (v 3))) := by
    apply disjoint_left.mpr
    intro w h1 h3
    exact hsep w (mem_filter.mp h1).1 ⟨(mem_filter.mp h1).2, (mem_filter.mp h3).2⟩
  have hrxy : Disjoint (j.filter (G.Adj p.center))
      (j.filter (G.Adj (v 1)) ∪ j.filter (G.Adj (v 3))) := by
    apply disjoint_left.mpr
    intro w hr hw
    obtain ⟨hwj, hrw⟩ := mem_filter.mp hr
    rcases mem_union.mp hw with h1 | h3
    · exact hn ⟨1, Or.inl rfl, w, hwj, hrw, (mem_filter.mp h1).2⟩
    · exact hn ⟨3, Or.inr rfl, w, hwj, hrw, (mem_filter.mp h3).2⟩
  have hbound := card_le_card (union_subset (filter_subset (G.Adj p.center) j)
    (union_subset (filter_subset (G.Adj (v 1)) j) (filter_subset (G.Adj (v 3)) j)))
  rw [card_union_of_disjoint hrxy, card_union_of_disjoint hxy, hj] at hbound
  change degreeIn G p.center j + (degreeIn G (v 1) j + degreeIn G (v 3) j) ≤ 4 at hbound
  have htri := triangle_contacts_center_upper p j hj
  omega

end Erdos577.FullRow
