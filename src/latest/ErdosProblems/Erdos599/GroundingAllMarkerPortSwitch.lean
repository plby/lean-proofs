/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.GroundingAllMarkerPortAugmentation
import ErdosProblems.Erdos599.GroundingPortToggleProjection
import ErdosProblems.Erdos599.GroundingFinitePerturbationRooting

/-!
# The actual port switch has exact original-graph boundary balance

The generic finite toggle applies to the constructed port augmentation
with all endpoint and residual-step premises discharged. Its projected
edges form a finite perturbation of the original reference warp. No
projected edge leaves the blocking set, and every old blocking sink is
preserved, not just a sink in the component of the requested entry.
-/

noncomputable section

namespace Erdos599.GroundingAllMarkerAuxiliary.Input

open Set Cardinal DirectedPath Alternating GroundingAllMarkerPorts GroundingPortToggle

universe u

variable {V I : Type u} {G : DWeb V} (L : Input G I)

namespace PortAugmentation

variable {C : Set L.Vertex} {q : FinitePath L.web.graph} {r : L.Request C}
  (D : L.PortAugmentation C q r)

def togglePath : AugmentingPath G (L.originStoppedMatching C D.origin D.departure) where
  portGraph := L.matchingRouteGraph q.support r.1 D.departure
    (L.originStoppedMatching C D.origin D.departure)
  path := D.path
  first := D.departure
  last := L.requestVertex r
  path_start := D.path_start
  path_finish := D.path_finish
  step he := (D.path.edgeSet_subset_adj he).1
  first_free := D.source_unmatched L
  last_free := D.request_unmatched L

def baseEdges : Set (V × V) := nonDiagonal (L.originStoppedMatching C D.origin D.departure)

def switchedEdges : Set (V × V) := (D.togglePath L).projectedEdges

theorem switchedEdges_biUnique : Relator.BiUnique (fun x y ↦ (x, y) ∈ D.switchedEdges L) :=
  (D.togglePath L).projectedEdges_biUnique
    (L.originStoppedMatching_biUnique C D.origin D.departure)

theorem switchedEdges_edgeBalance (x : V) :
    edgeBalance (D.switchedEdges L) x = edgeBalance (D.baseEdges L) x +
      propInt (x = D.departure) - propInt (x = L.requestVertex r) :=
  (D.togglePath L).projectedEdges_edgeBalance
    (L.originStoppedMatching_biUnique C D.origin D.departure) x

theorem baseEdges_subset_reference : D.baseEdges L ⊆ familyEdges L.reference.paths := by
  rintro e ⟨⟨hstop, _⟩, hne⟩
  rcases hstop with he | ⟨he, _⟩
  · exact L.stoppedReferenceEdges_subset C he
  · exact (hne he).elim

theorem switchedEdges_subset_adj : D.switchedEdges L ⊆ {e | G.graph.Adj e.1 e.2} := by
  apply (D.togglePath L).projectedEdges_subset_adj
  intro x y h
  rcases L.residualMatching_subset_reference C
      (L.stoppedMatching_subset_residual C h.1) with he | ⟨he, _⟩
  · exact Or.inl (familyEdges_subset_adj L.reference.paths he)
  · exact Or.inr he

theorem switchedEdges_finitePerturbation : ∃ F : Set (V × V),
    F.Finite ∧ D.switchedEdges L ⊆ familyEdges L.reference.paths ∪ F := by
  refine ⟨(D.togglePath L).insertedEdges, (D.togglePath L).insertedEdges_finite, ?_⟩
  intro e he
  exact ((D.togglePath L).projectedEdges_subset he).imp
    (fun h ↦ D.baseEdges_subset_reference L h) id

theorem switchedEdges_noReverseRay : ¬ ContainsReverseDirectedRay (D.switchedEdges L) := by
  obtain ⟨F, hF, hE⟩ := D.switchedEdges_finitePerturbation L
  exact TerminalContactSwitch.not_containsReverseDirectedRay_of_subset_union_finite hE
    (PathFilterComponents.DWeb.IsWarp.familyEdges_not_containsReverseDirectedRay
      L.reference.disjoint) hF

theorem switchedEdges_positive_old_or_departure {x : V}
    (hx : edgeBalance (D.switchedEdges L) x = 1) :
    edgeBalance (D.baseEdges L) x = 1 ∨ x = D.departure :=
  (D.togglePath L).projectedEdges_positive_old_or_first
    (L.originStoppedMatching_biUnique C D.origin D.departure) hx

end PortAugmentation

variable {kappa : Cardinal.{u}} {U : Popular.KappaIndexed L.web kappa}
  (S : Popular.PopularSeparator U) (hInitial : ∀ i, (L.record i).initial ∉ L.markers)

namespace PortAugmentation

variable (r : L.Request S.cut) {q : FinitePath L.web.graph}
  (hq : q ∈ (L.shortenedRecordFan S r hInitial).paths) (D : L.PortAugmentation S.cut q r)

include hq

theorem toggled_tail_not_blockingSet {x y : V} (h : (D.togglePath L).toggled x y) :
    x ∉ L.blockingSet S.cut := by
  rcases h with h | h
  · exact L.stoppedMatching_tail_not_blockingSet S.cut h.1.1
  · exact D.forward_tail_not_blockingSet L S hInitial r hq h

theorem switchedEdges_no_outgoing_blockingSet {x : V} (hx : x ∈ L.blockingSet S.cut) :
    ¬ HasOutgoing (D.switchedEdges L) x := by
  rintro ⟨y, hy, _⟩
  exact D.toggled_tail_not_blockingSet L S hInitial r hq hy hx

/-- The range identity at blocking vertices is not obscured by diagonal
pairs, since neither the old nor new matching has an outgoing pair there. -/
theorem switchedEdges_incoming_blockingSet_iff {x : V} (hx : x ∈ L.blockingSet S.cut) :
    HasIncoming (D.switchedEdges L) x ↔
      HasIncoming (D.baseEdges L) x ∨ x = L.requestVertex r := by
  have hnew : HasIncoming (D.switchedEdges L) x ↔ ∃ y, (D.togglePath L).toggled y x := by
    constructor
    · rintro ⟨y, hy, _⟩
      exact ⟨y, hy⟩
    · rintro ⟨y, hy⟩
      refine ⟨y, hy, ?_⟩
      intro heq
      have hyx : y = x := heq
      exact D.toggled_tail_not_blockingSet L S hInitial r hq hy (hyx.symm ▸ hx)
  have hold : HasIncoming (D.baseEdges L) x ↔
      ∃ y, L.originStoppedMatching S.cut D.origin D.departure y x := by
    constructor
    · rintro ⟨y, hy, _⟩
      exact ⟨y, hy⟩
    · rintro ⟨y, hy⟩
      refine ⟨y, hy, ?_⟩
      intro heq
      have hyx : y = x := heq
      exact L.stoppedMatching_tail_not_blockingSet S.cut hy.1 (hyx.symm ▸ hx)
  rw [hnew, (D.togglePath L).toggled_incoming_iff, hold]
  rfl

theorem switchedEdges_preserves_blocking_sink {x : V} (hx : x ∈ L.blockingSet S.cut)
    (hin : HasIncoming (D.baseEdges L) x) :
    HasIncoming (D.switchedEdges L) x ∧ ¬ HasOutgoing (D.switchedEdges L) x :=
  ⟨(D.switchedEdges_incoming_blockingSet_iff L S hInitial r hq hx).2 (Or.inl hin),
    D.switchedEdges_no_outgoing_blockingSet L S hInitial r hq hx⟩

theorem switchedEdges_request_sink (hr : L.requestVertex r ∈ L.blockingSet S.cut) :
    HasIncoming (D.switchedEdges L) (L.requestVertex r) ∧
      ¬ HasOutgoing (D.switchedEdges L) (L.requestVertex r) :=
  ⟨(D.switchedEdges_incoming_blockingSet_iff L S hInitial r hq hr).2 (Or.inr rfl),
    D.switchedEdges_no_outgoing_blockingSet L S hInitial r hq hr⟩

#print axioms switchedEdges_biUnique
#print axioms switchedEdges_edgeBalance
#print axioms switchedEdges_finitePerturbation
#print axioms switchedEdges_noReverseRay
#print axioms switchedEdges_no_outgoing_blockingSet
#print axioms switchedEdges_incoming_blockingSet_iff
#print axioms switchedEdges_preserves_blocking_sink
#print axioms switchedEdges_request_sink

end PortAugmentation
end Erdos599.GroundingAllMarkerAuxiliary.Input
