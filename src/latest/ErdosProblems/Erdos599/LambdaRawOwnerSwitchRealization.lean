/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.LambdaRawOwnerSwitch
import ErdosProblems.Erdos599.LambdaRawSwitchRealization

/-!
# Realization of the genuine-source raw owner transaction

Replacing a finite or ray owner by a finite prefix and finitely many raw
connectors does not create a reverse ray. The actual biunique relation is
therefore realized by paths and forward rays after whole cycles are removed.
The exact source-minus-exit balance is preserved.
-/

noncomputable section

namespace Erdos599.PopularAuxiliary.Input.RawOwnerAttachment

open Set DirectedPath Alternating Alternating.TerminalContactSwitch

universe u

variable {V I : Type u} {Gamma : DWeb V}
variable {L : PopularAuxiliary.Input Gamma I} {H : Gamma.DPath}
variable {p : FinitePath L.lambda.graph} (A : L.RawOwnerAttachment H p)

theorem forwardEdges_finite : A.forwardEdges.Finite :=
  (Set.finite_singleton _).union (L.properSelectedConnectorEdges_finite A.tail)

theorem sourceEdges_subset_adj :
    A.sourceEdges ⊆ {e | Gamma.graph.Adj e.1 e.2} := by
  intro e he
  rcases he with (he | he | he) | he
  · obtain ⟨q, _hq, heq⟩ := he.1.1
    exact q.edgeSet_subset_adj heq
  · have heq : e = (A.anchor, A.nextVertex) := Set.mem_singleton_iff.1 he
    exact heq.symm ▸ A.connector.2.2
  · exact L.selectedConnectorEdges_subset_adj A.tail he.1
  · exact A.sourcePrefix.edgeSet_subset_adj he

/-- The only genuinely inserted edges form a finite relation; the restored
prefix already belongs to the original reference warp. -/
theorem sourceEdges_subset_reference_union_forward (hH : H ∈ L.ladder.paths) :
    A.sourceEdges ⊆ L.familyEdges ∪ A.forwardEdges := by
  intro e he
  rcases he with (he | he) | he
  · exact Or.inl he.1.1
  · exact Or.inr he
  · exact Or.inl ⟨H, hH, A.sourcePrefix_edges he⟩

theorem sourceEdges_not_containsReverseDirectedRay (hH : H ∈ L.ladder.paths) :
    ¬ ContainsReverseDirectedRay A.sourceEdges := by
  apply not_containsReverseDirectedRay_of_subset_union_finite
    (A.sourceEdges_subset_reference_union_forward hH) _ A.forwardEdges_finite
  have href : L.familyEdges = Alternating.familyEdges L.ladder.paths := by
    ext e
    simp only [PopularAuxiliary.Input.familyEdges, Alternating.familyEdges,
      Set.mem_iUnion, Set.mem_ofPred_eq, exists_prop]
  rw [href]
  exact PathFilterComponents.DWeb.IsWarp.familyEdges_not_containsReverseDirectedRay
    L.ladder.disjoint

/-- The whole-owner transaction gives an actual path/ray warp with exact
cycle-discarded edges and balance at the genuine original source. -/
theorem exists_sourceSwitchWarp (hL : L.HasBoundaryIncidence) (hH : H ∈ L.ladder.paths)
    (hs : p.start ∈ L.lambda.source) {t : V}
    (ht : L.gadgetExit p.finish = some t) :
    ∃ W : Set Gamma.DPath,
      Gamma.IsWarp W ∧
      Alternating.familyEdges W = A.sourceEdges \ cyclicEdges A.sourceEdges ∧
      isolatedVertices W = ∅ ∧
      ∀ x, edgeBalance (Alternating.familyEdges W) x =
        edgeBalance (L.familyEdges \ H.edgeSet) x +
          propInt (x = H.initial) - propInt (x = t) := by
  obtain ⟨W, hW, hWE, hWI, hbalance⟩ :=
    GroundingFinitePerturbationRooting.exists_warp_with_edges_sdiff_cyclic
      A.sourceEdges A.sourceEdges_subset_adj (A.sourceEdges_biUnique hL hH)
      (A.sourceEdges_not_containsReverseDirectedRay hH)
  refine ⟨W, hW, hWE, hWI, ?_⟩
  intro x
  rw [hbalance]
  exact A.sourceEdges_balance hL hH hs ht x

#print axioms sourceEdges_not_containsReverseDirectedRay
#print axioms exists_sourceSwitchWarp

end Erdos599.PopularAuxiliary.Input.RawOwnerAttachment
