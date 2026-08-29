/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.GroundingAllMarkerLocalMatching
import ErdosProblems.Erdos599.GroundingAllMarkerUntouchedGeometry
import ErdosProblems.Erdos599.GroundingSourceRootTransfer

/-!
# Every positive local switched boundary is an original source

The local base has only grounded fragment initials and the requested
entry as possible positive boundaries. Origin truncation is treated by
its exact finite prefix. The entry loses one unit of balance; a newly
positive departure must be the initial of its origin prefix.
-/

namespace Erdos599.GroundingAllMarkerAuxiliary.Input

open Set Cardinal DirectedPath Alternating GroundingAllMarkerPorts GroundingPortToggle

universe u

variable {V I : Type u} {G : DWeb V} (L : Input G I)

private theorem initial_eq_of_edges_subset_of_noIncoming (P : G.DPath) (E : Set (V × V))
    (hE : P.edgeSet ⊆ E) {x : V} (hx : x ∈ P.support) (hno : ¬ HasIncoming E x) :
    P.initial = x := by
  apply initial_eq_of_mem_support_of_noIncoming (W := {P}) (Set.mem_singleton P) hx
  rintro ⟨y, hy⟩
  have hyP : (y, x) ∈ P.edgeSet := by simpa [familyEdges] using hy
  exact hno ⟨y, hE hyP⟩

namespace PortAugmentation

variable {C : Set L.Vertex} {q : FinitePath L.web.graph} {r : L.Request C}
  (D : L.PortAugmentation C q r)

/-- An entire selected stopped fragment is retained unless it is on the
origin owner, where the exact origin-prefix characterization applies. -/
theorem stoppedFragment_edges_subset_localBase_of_parent_ne {P : L.CutFragment}
    (hP : P ∈ L.localFragments C q r) (hne : P.parent ≠ L.record D.origin) :
    (L.stoppedFragment C P).edgeSet ⊆ D.localBaseEdges L := by
  intro e he
  have hActual := L.localFragments_mem C q r hP
  refine ⟨⟨⟨Or.inl ⟨P, hActual, he⟩, ?_⟩, Or.inr (Or.inr ⟨P, hP, he⟩)⟩, ?_⟩
  · intro hx
    have hxP : e.1 ∈ P.parent.support := P.support_subset
      (L.stoppedFragment_support_subset C P
        ((L.stoppedFragment C P).edgeSet_subset_support_prod he).1)
    exact (hne (DWeb.IsWarp.eq_of_mem_support L.reference.disjoint
      P.parent_mem (L.record_mem D.origin) hxP hx)).elim
  · exact GroundingFragmentResidualOrder.ne_of_mem_dpath_edgeSet he

end PortAugmentation

variable {kappa : Cardinal.{u}} {U : Popular.KappaIndexed L.web kappa}
  (S : Popular.PopularSeparator U) (hInitial : ∀ i, (L.record i).initial ∉ L.markers)
  (hInitials : G.initialSet L.reference.paths ⊆ G.source ∪ L.markers)

namespace PortAugmentation

variable (r : L.Request S.cut) {q : FinitePath L.web.graph}
  (hq : q ∈ (L.shortenedRecordFan S r hInitial).paths) (D : L.PortAugmentation S.cut q r)
  (hOrigin : (L.record D.origin).initial ∈ G.source)

include hq hInitials hOrigin in
theorem localBase_positive_source_or_request {x : V}
    (hx : edgeBalance (D.localBaseEdges L) x = 1) : x ∈ G.source ∨ x = L.requestVertex r := by
  classical
  obtain ⟨hout, hno⟩ := edgeBalance_eq_one_iff.mp hx
  obtain ⟨y, hy⟩ := hout
  by_cases hxOrigin : x ∈ (L.record D.origin).support
  · have hePrefix := D.matching_edge_mem_originPrefix L hy.1.1 hxOrigin
    have hstart : (D.originPrefix L).start = x :=
      initial_eq_of_edges_subset_of_noIncoming (.inl (D.originPrefix L)) (D.localBaseEdges L)
        (D.originPrefix_edges_subset_localBase L S.separates)
        ((D.originPrefix L).edgeSet_subset_support_prod hePrefix).1 hno
    have hxInitial : x = (L.record D.origin).initial :=
      hstart.symm.trans (D.originPrefix_spec L).1
    exact Or.inl (hxInitial.symm ▸ hOrigin)
  · have hraw := hy.1.2.resolve_left hy.2
    rcases hraw with hprefix | ⟨P, hP, he⟩
    · exact (hxOrigin ((D.originPrefix_spec L).2.2.1
        ((D.originPrefix L).edgeSet_subset_support_prod hprefix).1)).elim
    · have hxP : x ∈ P.path.support := L.stoppedFragment_support_subset S.cut P
        ((L.stoppedFragment S.cut P).edgeSet_subset_support_prod he).1
      have hparent : P.parent ≠ L.record D.origin :=
        fun h ↦ hxOrigin (h ▸ P.support_subset hxP)
      have hstart := initial_eq_of_edges_subset_of_noIncoming
        (L.stoppedFragment S.cut P) (D.localBaseEdges L)
        (D.stoppedFragment_edges_subset_localBase_of_parent_ne L hP hparent)
        ((L.stoppedFragment S.cut P).edgeSet_subset_support_prod he).1 hno
      have hPx : P.path.initial = x := (L.stoppedFragment_initial S.cut P).symm.trans hstart
      rcases L.localFragments_initial_profile S hInitial hInitials r hq hP with hsource | hentry
      · exact Or.inl (hPx ▸ hsource)
      · exact Or.inr (hPx.symm.trans hentry)

include hInitial in
theorem departure_ne_request : D.departure ≠ L.requestVertex r := by
  intro h
  exact L.requestVertex_not_mem_good_record S hInitial r D.origin D.origin_good
    (h ▸ D.departure_mem)

include hq hInitials hOrigin in
theorem localSwitchedEdges_positive_source {x : V}
    (hx : edgeBalance (D.localSwitchedEdges L S hInitial r hq) x = 1) : x ∈ G.source := by
  classical
  by_cases hdep : x = D.departure
  · subst x
    have hentry := D.departure_ne_request L S hInitial r
    have hbal := D.localSwitchedEdges_edgeBalance L S hInitial r hq D.departure
    have hzero : edgeBalance (D.localBaseEdges L) D.departure = 0 := by
      rw [hx] at hbal
      norm_num [propInt, hentry] at hbal
      omega
    have hnoOut : ¬ HasOutgoing (D.localBaseEdges L) D.departure := by
      rintro ⟨y, hy⟩
      exact D.source_unmatched L y hy.1.1
    have hnoIn : ¬ HasIncoming (D.localBaseEdges L) D.departure := by
      intro hin
      have hneg := edgeBalance_eq_neg_one_iff.mpr ⟨hin, hnoOut⟩
      omega
    have hprefixNoIn : ¬ HasIncoming (D.originPrefix L).edgeSet D.departure := by
      rintro ⟨y, hy⟩
      exact hnoIn ⟨y, D.originPrefix_edges_subset_localBase L S.separates hy⟩
    exact (D.departure_eq_initial_of_prefix_noIncoming L hprefixNoIn).symm ▸ hOrigin
  · have hold : edgeBalance (D.localBaseEdges L) x = 1 :=
      ((D.localTogglePath L S hInitial r hq).projectedEdges_positive_old_or_first
        (D.localMatching_biUnique L) hx).resolve_right hdep
    rcases D.localBase_positive_source_or_request L S hInitial hInitials r hq hOrigin hold with
      hsource | hentry
    · exact hsource
    · have hbal := D.localSwitchedEdges_edgeBalance L S hInitial r hq x
      simp only [hx, hold, propInt, if_neg hdep, if_pos hentry] at hbal
      omega

#print axioms stoppedFragment_edges_subset_localBase_of_parent_ne
#print axioms localBase_positive_source_or_request
#print axioms localSwitchedEdges_positive_source

end PortAugmentation
end Erdos599.GroundingAllMarkerAuxiliary.Input
