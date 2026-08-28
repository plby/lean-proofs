import ErdosProblems.Erdos577.PawInduced
import ErdosProblems.Erdos577.EdgeChanges
import ErdosProblems.Erdos577.AlmostComplete

/-! A paw remainder with no additional leaf edges has exactly four induced edges. -/

namespace Erdos577.Paw

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

lemma edgeCount_of_nonadjacent (p : Paw G)
    (h : ¬G.Adj p.leaf (p.vertices 2) ∧ ¬G.Adj p.leaf (p.vertices 3)) :
    edgeCount G p.support = 4 := by
  rw [p.support_eq, edgeCount_insert G p.leaf p.leaf_not_mem_triangle,
    edgeCount_clique p.triangle_clique.isClique, p.triangle_clique.card_eq,
    p.leaf_triangle_degree, if_neg h.1, if_neg h.2]
  decide +kernel

lemma edgeCount_of_no_quad (p : Paw G) (h : ¬QuadOn G p.support) :
    edgeCount G p.support = 4 := p.edgeCount_of_nonadjacent (p.nonadjacent_of_no_quad h)

end Erdos577.Paw
