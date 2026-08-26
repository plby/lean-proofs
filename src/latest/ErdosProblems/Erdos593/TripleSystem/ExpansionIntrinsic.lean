import ErdosProblems.Erdos593.TripleSystem.Expansion
import ErdosProblems.Erdos593.TripleSystem.Intrinsic

set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Intrinsic bridge property of private-vertex expansions

The private point of each expanded edge is a leaf in the Levi graph, so its
incidence with the corresponding hyperedge-node is an actual bridge.
-/

namespace Erdos593

universe u

namespace TripleSystem

/-- Every expanded hyperedge has the bridge to its private point. -/
-- ARISTOTLE_TARGET F2
theorem privateVertexExpansion_bridgeAtEveryEdge {V : Type u}
    (G : _root_.SimpleGraph V) :
    (privateVertexExpansion G).BridgeAtEveryEdge := by
  intro e
  let x := PrivateVertexExpansion.privateVertex G e
  have hAdj : (privateVertexExpansion G).levi.Adj (.inl x) (.inr e) := by
    simp [x]
  refine ⟨x, hAdj, ?_⟩
  rw [show s(Sum.inl x, Sum.inr e) = s(Sum.inr e, Sum.inl x) from Sym2.eq_swap]
  apply Erdos593.SimpleGraph.isBridge_of_adj_of_unique_neighbor _ hAdj.symm
  intro w hw
  rcases w with y | f
  · exact (not_levi_adj_point_point (privateVertexExpansion G) hw).elim
  · congr 1
    exact (by simpa [x] using! hw : e = f).symm

end TripleSystem

end Erdos593
