/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.LambdaRawSwitchBalance
import ErdosProblems.Erdos599.GroundingFinitePerturbationRooting

/-!
# Actual path/ray realization of a finite-source raw switch

The inserted relation is finite, so the raw switch has no reverse ray.
Removing whole cyclic components gives an actual warp without changing its
endpoint balance. Forward rays are retained; no finite-character claim or
source/target grounding premise is hidden in the realization.
-/

noncomputable section

namespace Erdos599
namespace PopularAuxiliary.Input

open Set DirectedPath Alternating Alternating.TerminalContactSwitch

universe u v

variable {V : Type u} {I : Type v} {Gamma : DWeb V}
variable (L : PopularAuxiliary.Input Gamma I)

private theorem raw_reference_eq_familyEdges :
    L.familyEdges = Alternating.familyEdges L.ladder.paths := by
  ext e
  simp only [familyEdges, Alternating.familyEdges, Set.mem_iUnion,
    Set.mem_ofPred_eq, exists_prop]

/-- Either colour relation of a finite signed list is finite. -/
theorem directedSignedEdgeSet_finite (d : Direction) (q : List (SignedEdge V)) :
    (directedSignedEdgeSet d q).Finite := by
  apply (q.finite_toSet.image SignedEdge.edge).subset
  rintro e ⟨s, hs, _hd, he⟩
  exact ⟨s, hs, he⟩

theorem properSelectedConnectorEdges_finite (p : FinitePath L.lambda.graph) :
    (L.properSelectedConnectorEdges p).Finite := by
  rw [← decodeProperSteps_forwardEdges]
  exact directedSignedEdgeSet_finite .forward _

/-- The local switch inserts only finitely many genuine original edges. -/
theorem rawSwitchedEdges_subset_adj (p : FinitePath L.lambda.graph) :
    L.rawSwitchedEdges p ⊆ {e | Gamma.graph.Adj e.1 e.2} := by
  intro e he
  rcases he with ⟨⟨q, _hq, heq⟩, _hnot⟩ | he
  · exact q.edgeSet_subset_adj heq
  · exact L.selectedConnectorEdges_subset_adj p he.1

/-- A finite insertion into a path/ray warp cannot create a reverse ray. -/
theorem rawSwitchedEdges_not_containsReverseDirectedRay
    (p : FinitePath L.lambda.graph) :
    ¬ ContainsReverseDirectedRay (L.rawSwitchedEdges p) := by
  apply not_containsReverseDirectedRay_of_subset_union_finite
    (E := L.rawSwitchedEdges p) (B := L.familyEdges)
    (F := L.properSelectedConnectorEdges p)
  · intro e he
    rcases he with he | he
    · exact Or.inl he.1
    · exact Or.inr he
  · rw [L.raw_reference_eq_familyEdges]
    exact PathFilterComponents.DWeb.IsWarp.familyEdges_not_containsReverseDirectedRay
      L.ladder.disjoint
  · exact L.properSelectedConnectorEdges_finite p

variable {L}

/-- A source-starting ordinary raw route yields an actual path/ray warp
with its exact cycle-discarded relation and exact endpoint balance. -/
theorem HasBoundaryIncidence.exists_rawSwitchWarp_of_start_old
    (hL : L.HasBoundaryIncidence) (p : FinitePath L.lambda.graph)
    (hs : p.start ∈ L.lambda.source) {s t : V}
    (hstart : p.start = .old s) (hexit : L.gadgetExit p.finish = some t) :
    ∃ W : Set Gamma.DPath,
      Gamma.IsWarp W ∧
      Alternating.familyEdges W = L.rawSwitchedEdges p \ cyclicEdges (L.rawSwitchedEdges p) ∧
      isolatedVertices W = ∅ ∧
      ∀ x, edgeBalance (Alternating.familyEdges W) x = edgeBalance L.familyEdges x +
        propInt (x = s) - propInt (x = t) := by
  obtain ⟨W, hW, hWE, hWI, hbal⟩ :=
    GroundingFinitePerturbationRooting.exists_warp_with_edges_sdiff_cyclic
      (L.rawSwitchedEdges p) (L.rawSwitchedEdges_subset_adj p)
      (hL.rawSwitchedEdges_biUnique_of_start_old p hs hstart)
      (L.rawSwitchedEdges_not_containsReverseDirectedRay p)
  refine ⟨W, hW, hWE, hWI, ?_⟩
  intro x
  rw [hbal]
  exact hL.rawSwitchedEdges_balance_of_start_old p hs hstart hexit x

end PopularAuxiliary.Input
end Erdos599

#print axioms Erdos599.PopularAuxiliary.Input.rawSwitchedEdges_not_containsReverseDirectedRay
#print axioms Erdos599.PopularAuxiliary.Input.HasBoundaryIncidence.exists_rawSwitchWarp_of_start_old
