/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.BlueprintImaginaryEdgeSubdivision
import ErdosProblems.Erdos599.IntermediateRelationLimitRefinement

/-!
# Predecessor refinement for imaginary-edge subdivision

Subdividing a represented blueprint edge by a finite original path is not a
full no-new-predecessors operation: the last edge of the inserted path is a
new predecessor of the old head.  It does, however, satisfy the exact
`PredecessorRefines` relation used by intermediate proper limits.  The whole
inserted path is the refinement certificate, anchored at the old represented
edge.

If the deleted represented edge is not an original edge, subdivision also
extends the spanning real part.  The same conclusion follows when its tail
was an old real terminal, since then the represented outgoing edge cannot
have been original.
-/

noncomputable section

open Cardinal Set

namespace Erdos599
namespace Blueprint
namespace LinkageBlueprint

open DirectedPath

universe u

variable {V : Type u}
variable {Gamma : DWeb V} {Y : Set Gamma.DPath} {kappa : Cardinal.{u}}

/-- Replacing one represented edge by a fresh finite original path satisfies
the exact predecessor-refinement relation.  In the genuinely new-incoming
case, the inserted path itself is the finite real certificate anchored at
the old edge `u → v`. -/
theorem predecessorRefines_subdivideEdge
    (W : LinkageBlueprint Gamma Y kappa) {u v : V}
    (huv : (u, v) ∈ W.edgeSet) (P : FinitePath Gamma.graph)
    (hstart : P.start = u) (hfinish : P.finish = v)
    (hfresh : W.vertexSet ∩ P.support ⊆ {u, v}) :
    W.PredecessorRefines
      (W.subdivideEdge huv P hstart hfinish hfresh) := by
  intro x y hx hyx
  rcases W.subdivideEdge_incoming_old_vertex huv P hstart hfinish hfresh
      hx hyx with hold | hnew
  · exact Or.inl hold
  · refine Or.inr ⟨u, P, ?_, hstart, ?_, ?_⟩
    · simpa only [hnew.1] using huv
    · exact hfinish.trans hnew.1.symm
    · intro e he
      refine ⟨?_, P.edgeSet_subset_adj he⟩
      rw [subdivideEdge_edgeSet]
      exact Or.inr he

/-- If the represented edge being replaced is not an edge of the original
graph, subdivision retains every old real vertex and every old real edge. -/
theorem realPart_extends_subdivideEdge_of_not_original
    (W : LinkageBlueprint Gamma Y kappa) {u v : V}
    (huv : (u, v) ∈ W.edgeSet) (P : FinitePath Gamma.graph)
    (hstart : P.start = u) (hfinish : P.finish = v)
    (hfresh : W.vertexSet ∩ P.support ⊆ {u, v})
    (hnotOriginal : ¬ Gamma.graph.Adj u v) :
    W.realPart.Extends
      (W.subdivideEdge huv P hstart hfinish hfresh).realPart := by
  constructor
  · rw [realPart_vertices, realPart_vertices, subdivideEdge_vertexSet]
    exact Set.subset_union_left
  · rintro e ⟨heW, heOriginal⟩
    refine ⟨?_, heOriginal⟩
    rw [subdivideEdge_edgeSet]
    left
    refine ⟨heW, ?_⟩
    intro he
    have heq : e = (u, v) := Set.mem_singleton_iff.mp he
    subst e
    exact hnotOriginal heOriginal

/-- A represented outgoing edge at an old real terminal is necessarily
non-original, so its subdivision extends the real part. -/
theorem realPart_extends_subdivideEdge_of_mem_terminal
    (W : LinkageBlueprint Gamma Y kappa) {u v : V}
    (huv : (u, v) ∈ W.edgeSet) (P : FinitePath Gamma.graph)
    (hstart : P.start = u) (hfinish : P.finish = v)
    (hfresh : W.vertexSet ∩ P.support ⊆ {u, v})
    (huTerminal : u ∈ W.realPart.terminals) :
    W.realPart.Extends
      (W.subdivideEdge huv P hstart hfinish hfresh).realPart := by
  apply W.realPart_extends_subdivideEdge_of_not_original huv P hstart
    hfinish hfresh
  intro huvOriginal
  exact huTerminal.2 ⟨v, ⟨huv, huvOriginal⟩⟩

/-- Deletion data supplies the represented edge required by the subdivision
adapter.  The non-original hypothesis is stated explicitly because an
imaginary edge may also happen to be an original graph edge. -/
theorem IsImaginaryEdgeDeletionAt.realPart_extends_subdivideEdge
    {W cut : LinkageBlueprint Gamma Y kappa} {u v : V}
    (hdelete : W.IsImaginaryEdgeDeletionAt cut u v)
    (P : FinitePath Gamma.graph) (hstart : P.start = u)
    (hfinish : P.finish = v)
    (hfresh : W.vertexSet ∩ P.support ⊆ {u, v})
    (hnotOriginal : ¬ Gamma.graph.Adj u v) :
    W.realPart.Extends
      (W.subdivideEdge hdelete.edge_mem P hstart hfinish hfresh).realPart :=
  W.realPart_extends_subdivideEdge_of_not_original hdelete.edge_mem P
    hstart hfinish hfresh hnotOriginal

end LinkageBlueprint
end Blueprint
end Erdos599
