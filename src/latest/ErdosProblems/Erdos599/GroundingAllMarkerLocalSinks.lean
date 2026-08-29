/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.GroundingAllMarkerLocalBoundary
import ErdosProblems.Erdos599.GroundingPortToggleSink

/-!
# Every required local blocking point is reached from an original source

The finite local blocking set keeps all selected-fragment blockers, not
only the requested entry. Noninitial blockers retain their incoming edge;
initial blockers are grounded singletons or the requested entry. The
proved local boundary and no-reverse-ray theorems then root every sink.
-/

noncomputable section

namespace Erdos599.GroundingAllMarkerAuxiliary.Input

open Set Cardinal DirectedPath Alternating GroundingAllMarkerPorts GroundingPortToggle

universe u

variable {V I : Type u} {G : DWeb V} (L : Input G I)

namespace PortAugmentation

variable {C : Set L.Vertex} {q : FinitePath L.web.graph} {r : L.Request C}
  (D : L.PortAugmentation C q r)

def localBlockingSet : Set V := {x | x ∈ L.blockingSet C ∧
  (x = (D.togglePath L).last ∨ ∃ P ∈ L.localFragments C q r, x ∈ P.path.support)}

theorem localBlockingSet_finite : (D.localBlockingSet L).Finite := by
  have hfinite := (L.localFragments_finite C q r).image (L.fragmentBlockingPoint C)
  have hf := hfinite.insert (L.requestVertex r)
  apply hf.subset
  rintro x ⟨hxK, hreq | ⟨P, hP, hxP⟩⟩
  · exact Or.inl hreq
  · exact Or.inr ⟨P, hP, L.fragmentBlockingPoint_eq_of_mem C
      (L.localFragments_mem C q r hP) hxP hxK⟩

end PortAugmentation

variable {kappa : Cardinal.{u}} {U : Popular.KappaIndexed L.web kappa}
  (S : Popular.PopularSeparator U) (hInitial : ∀ i, (L.record i).initial ∉ L.markers)

namespace PortAugmentation

variable (r : L.Request S.cut) {q : FinitePath L.web.graph}
  (hq : q ∈ (L.shortenedRecordFan S r hInitial).paths) (D : L.PortAugmentation S.cut q r)

include hq in
theorem localToggled_tail_not_blockingSet {x y : V}
    (h : (D.localTogglePath L S hInitial r hq).toggled x y) : x ∉ L.blockingSet S.cut := by
  rcases h with h | h
  · exact L.stoppedMatching_tail_not_blockingSet S.cut h.1.1.1
  · exact D.forward_tail_not_blockingSet L S hInitial r hq h

theorem localSwitchedEdges_no_outgoing_blockingSet {x : V} (hx : x ∈ L.blockingSet S.cut) :
    ¬ HasOutgoing (D.localSwitchedEdges L S hInitial r hq) x := by
  rintro ⟨y, hy⟩
  exact D.switchedEdges_no_outgoing_blockingSet L S hInitial r hq hx
    ⟨y, D.localSwitchedEdges_subset_switchedEdges L S hInitial r hq hy⟩

theorem localSwitchedEdges_incoming_blockingSet_iff {x : V} (hx : x ∈ L.blockingSet S.cut) :
    HasIncoming (D.localSwitchedEdges L S hInitial r hq) x ↔
      HasIncoming (D.localBaseEdges L) x ∨ x = L.requestVertex r := by
  apply (D.localTogglePath L S hInitial r hq).projectedEdges_incoming_iff_of_noOutgoing x
  · intro y hy
    exact L.stoppedMatching_tail_not_blockingSet S.cut hy.1.1 hx
  · intro y hy
    exact D.localToggled_tail_not_blockingSet L S hInitial r hq hy hx

variable (hInitials : G.initialSet L.reference.paths ⊆ G.source ∪ L.markers)

include hq hInitials in
theorem localBlockingSet_source_or_incoming {x : V} (hx : x ∈ D.localBlockingSet L) :
    x ∈ G.source ∨ HasIncoming (D.localSwitchedEdges L S hInitial r hq) x := by
  obtain ⟨hxK, hreq | ⟨P, hP, hxP⟩⟩ := hx
  · exact Or.inr ((D.localSwitchedEdges_incoming_blockingSet_iff L S hInitial r hq hxK).2
      (Or.inr hreq))
  · by_cases hxi : x = P.path.initial
    · rcases L.localFragments_initial_profile S hInitial hInitials r hq hP with hs | hr
      · exact Or.inl (hxi.symm ▸ hs)
      · exact Or.inr ((D.localSwitchedEdges_incoming_blockingSet_iff L S hInitial r hq hxK).2
          (Or.inr (hxi.trans hr)))
    · have hActual := L.localFragments_mem S.cut q r hP
      have hblocked : P ∈ L.blockedFragments S.cut := ⟨hActual, x, hxP, hxK⟩
      have hparent := L.blockedFragment_parent_ne_goodRecord S.cut S.separates
        hblocked D.origin_good
      have hspec := L.blockingPrefix_spec S.cut hblocked
      have hfinish : (L.blockingPrefix S.cut hblocked).finish = x := hspec.2.1.trans
        (L.fragmentBlockingPoint_eq_of_mem S.cut hActual hxP hxK)
      have hxPrefix : x ∈ (L.blockingPrefix S.cut hblocked).support :=
        hfinish ▸ (L.blockingPrefix S.cut hblocked).finish_mem_support
      have hne : x ≠ (L.blockingPrefix S.cut hblocked).start := by rwa [hspec.1]
      obtain ⟨y, hy⟩ := FinitePath.exists_incoming_edge_of_mem_support_of_ne_start
        (L.blockingPrefix S.cut hblocked) hxPrefix hne
      have hyStop : (y, x) ∈ (L.stoppedFragment S.cut P).edgeSet := by
        rw [L.stoppedFragment_of_blocked S.cut hblocked]
        exact hy
      have hin : HasIncoming (D.localBaseEdges L) x :=
        ⟨y, D.stoppedFragment_edges_subset_localBase_of_parent_ne L hP hparent hyStop⟩
      exact Or.inr ((D.localSwitchedEdges_incoming_blockingSet_iff L S hInitial r hq hxK).2
        (Or.inl hin))

include hq hInitials in
theorem localBlockingSet_rooted (hOrigin : (L.record D.origin).initial ∈ G.source)
    {x : V} (hx : x ∈ D.localBlockingSet L) :
    ∃ a ∈ G.source, Relation.ReflTransGen
      (fun u v ↦ (u, v) ∈ D.localSwitchedEdges L S hInitial r hq) a x := by
  apply GroundingFinitePerturbationRooting.sink_rooted_of_noReverseRay
    (D.localSwitchedEdges L S hInitial r hq) G.source
    (fun _ he ↦ D.switchedEdges_subset_adj L
      (D.localSwitchedEdges_subset_switchedEdges L S hInitial r hq he))
    (D.localSwitchedEdges_biUnique L S hInitial r hq)
    (D.localSwitchedEdges_noReverseRay L S hInitial r hq)
  · intro y hy
    exact D.localSwitchedEdges_positive_source L S hInitial hInitials r hq hOrigin hy
  · exact D.localBlockingSet_source_or_incoming L S hInitial r hq hInitials hx
  · exact D.localSwitchedEdges_no_outgoing_blockingSet L S hInitial r hq hx.1

#print axioms localBlockingSet_finite
#print axioms localSwitchedEdges_incoming_blockingSet_iff
#print axioms localBlockingSet_source_or_incoming
#print axioms localBlockingSet_rooted

end PortAugmentation
end Erdos599.GroundingAllMarkerAuxiliary.Input
