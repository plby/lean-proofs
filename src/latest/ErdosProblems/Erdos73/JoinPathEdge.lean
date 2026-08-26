/- Joining two paths through an actual host edge, with exact support control. -/
import ErdosProblems.Erdos73.GraphPaths

namespace Erdos73Infrastructure.SimpleGraph.GraphPath
noncomputable section
attribute [local instance] Classical.propDecidable Classical.decEq
variable {V : Type*} {G : _root_.SimpleGraph V}

def joinViaEdge (P Q : GraphPath G) (h : G.Adj P.target Q.source) : GraphPath G :=
  GraphPath.ofWalk (P.walk.append (.cons h Q.walk))

@[simp] theorem joinViaEdge_source (P Q : GraphPath G) (h : G.Adj P.target Q.source) :
    (P.joinViaEdge Q h).source = P.source := rfl

@[simp] theorem joinViaEdge_target (P Q : GraphPath G) (h : G.Adj P.target Q.source) :
    (P.joinViaEdge Q h).target = Q.target := rfl

theorem joinViaEdge_vertexSet_subset (P Q : GraphPath G) (h : G.Adj P.target Q.source) :
    (P.joinViaEdge Q h).vertexSet ⊆ P.vertexSet ∪ Q.vertexSet := by
  intro v hv
  have hv' := GraphPath.ofWalk_vertexSet_subset (P.walk.append (.cons h Q.walk)) hv
  simp only [List.mem_toFinset, _root_.SimpleGraph.Walk.mem_support_append_iff,
    _root_.SimpleGraph.Walk.support_cons, List.mem_cons] at hv'
  rcases hv' with hp | he | hq
  · exact Finset.mem_union_left _ (List.mem_toFinset.mpr hp)
  · exact Finset.mem_union_left _ (he ▸ P.target_mem_vertexSet)
  · exact Finset.mem_union_right _ (List.mem_toFinset.mpr hq)

end
end Erdos73Infrastructure.SimpleGraph.GraphPath
