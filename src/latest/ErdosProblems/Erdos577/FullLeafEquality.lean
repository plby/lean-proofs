import ErdosProblems.Erdos577.FullLeafEqualityMatchedInside

/-! TeX9.76: the complete core, perfect triple matching, and exact inside sum thirty-six. -/

namespace Erdos577.FullLeafCore

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
variable {c : TriangleChain G} {p : Paw G} {s a : Finset V} {y : V}

theorem Maximal.full_leaf_equality (hm : Maximal c p s a y) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hdeg : ∀ v, 2 * k ≤ G.degree v) (hn : ¬HasPacking G k) :
    G.IsNClique 7 (p.triangle ∪ a) ∧
      contacts G (s.erase y) (insert (p.vertices 3) a) = 3 ∧
      FullLeafEquality.matchedFirst p s a y = s.erase y ∧
      G.IsNClique 3 (FullLeafEquality.matchedSecond p s a y) ∧
      Nonempty (FullLeafEquality.MatchedTriple G (s.erase y)
        (FullLeafEquality.matchedSecond p s a y)) ∧
      contacts G ((s.erase y) ∪ FullLeafEquality.matchedSecond p s a y) (p.support ∪ s ∪ a) = 36 :=
  ⟨hm.equality_core_complete hcard hdeg hn, hm.matching_contacts_three hcard hdeg hn,
    hm.matched_first_eq hcard hdeg hn, hm.matched_second_triangle hcard hdeg hn,
    hm.matching_triple hcard hdeg hn, hm.matched_six_inside_contacts hcard hdeg hn⟩

end Erdos577.FullLeafCore
