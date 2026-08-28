import ErdosProblems.Erdos577.FullLeafSixThreeContacts

/-! The final adjacent row forces the supposedly missing diagonal. -/

namespace Erdos577.FullLeafCore

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
variable {c : TriangleChain G} {p : Paw G} {s a : Finset V} {y : V}

theorem Configuration.six_diamond_false (h : Configuration c p s a y) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hn : ¬HasPacking G k)
    (q : Quadrilateral G) (hj : q.support ∈ c.blocks) (hjs : q.support ≠ s)
    (hja : q.support ≠ a) (height : contacts G (s.erase y) q.support = 8)
    {v : V} (hv : v ∈ FullLeafEquality.matchedSecond p s a y)
    (h0 : G.Adj v (q 0)) (h1 : G.Adj v (q 1))
    (hdiag : G.Adj (q 0) (q 2)) (hmissing : ¬G.Adj (q 1) (q 3)) : False := by
  have hout : v ∉ q.support := fun hh ↦
    disjoint_left.mp (h.matched_second_disjoint_block hj hja) hv hh
  have hrep := q.replace_using_path v hout 3 1 2 0 (by decide) (by decide)
    h1 (q.adjacent 1) hdiag.symm h0
  have hlow := h.triple_degree_of_second_replacement hcard hn (mem_filter.mp hv).1
    hj hjs hja ((q.mem_support _).mpr ⟨3, rfl⟩) hrep
  obtain ⟨x, hx, hrow⟩ := FullLeafSix.three_contacts_of_eight q h.first_triple_clique.card_eq
    height hlow
  exact hmissing (h.first_last_diagonal q hj hjs (mem_insert_of_mem (mem_erase.mp hx).2) hrow)

theorem Configuration.six_eight_four_false (h : Configuration c p s a y) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hn : ¬HasPacking G k)
    (ht : G.IsNClique 3 (FullLeafEquality.matchedSecond p s a y))
    (q : Quadrilateral G) (hj : q.support ∈ c.blocks) (hjs : q.support ≠ s)
    (hja : q.support ≠ a) (height : contacts G (s.erase y) q.support = 8)
    (hfour : contacts G (FullLeafEquality.matchedSecond p s a y) q.support = 4)
    {u : V} (hu : u ∈ s.erase y) (hrow : 3 ≤ degreeIn G u q.support) : False := by
  obtain ⟨v, hv, w, hw, hlabels, hdiag, hmissing⟩ :=
    h.six_diamond_labels hcard hn ht q hj hjs hja height hfour hu hrow
  exact h.six_diamond_false hcard hn w (by rwa [hw]) (by rwa [hw]) (by rwa [hw])
    (by rwa [hw]) hv ((hlabels 0).mpr (Or.inl rfl)) ((hlabels 1).mpr (Or.inr rfl)) hdiag hmissing

end Erdos577.FullLeafCore
