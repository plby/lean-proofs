/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.GroundingAllMarkerOriginPrefix

/-!
# Localizing the old matching without changing the augmenting port path

Only old reference pairs on the finite selected fragment family or origin
prefix are kept; diagonal pairs remain. Every actual backward pair is
retained by port-representative uniqueness. The identical finite port path
is therefore an augmenting path for the restricted matching.
-/

noncomputable section

namespace Erdos599.GroundingAllMarkerAuxiliary.Input

open Set Cardinal DirectedPath Alternating GroundingAllMarkerPorts GroundingPortToggle

universe u

variable {V I : Type u} {G : DWeb V} (L : Input G I)

namespace PortAugmentation

variable {C : Set L.Vertex} {q : FinitePath L.web.graph} {r : L.Request C}
  (D : L.PortAugmentation C q r)

def rawLocalEdges : Set (V × V) := (D.originPrefix L).edgeSet ∪
  {e | ∃ P ∈ L.localFragments C q r, e ∈ (L.stoppedFragment C P).edgeSet}

def localMatching (x y : V) : Prop :=
  L.originStoppedMatching C D.origin D.departure x y ∧
    (x = y ∨ (x, y) ∈ D.rawLocalEdges L)

def localBaseEdges : Set (V × V) := nonDiagonal (D.localMatching L)

theorem localMatching_biUnique : Relator.BiUnique (D.localMatching L) :=
  ⟨fun _ _ _ h h' ↦
    (L.originStoppedMatching_biUnique C D.origin D.departure).1 h.1 h'.1,
    fun _ _ _ h h' ↦
    (L.originStoppedMatching_biUnique C D.origin D.departure).2 h.1 h'.1⟩

theorem originPrefix_edge_mem_localMatching (hC : Popular.IsSeparator L.web C) {x y : V}
    (he : (x, y) ∈ (D.originPrefix L).edgeSet) : D.localMatching L x y :=
  ⟨D.originPrefix_edge_mem_matching L hC he, Or.inr (Or.inl he)⟩

theorem originPrefix_edges_subset_localBase (hC : Popular.IsSeparator L.web C) :
    (D.originPrefix L).edgeSet ⊆ D.localBaseEdges L := by
  intro e he
  exact ⟨D.originPrefix_edge_mem_localMatching L hC he,
    GroundingFragmentResidualOrder.ne_of_mem_dpath_edgeSet
      (P := .inl (D.originPrefix L)) he⟩

theorem localBaseEdges_subset_baseEdges : D.localBaseEdges L ⊆ D.baseEdges L := by
  rintro e ⟨he, hne⟩
  exact ⟨he.1, hne⟩

end PortAugmentation

variable {kappa : Cardinal.{u}} {U : Popular.KappaIndexed L.web kappa}
  (S : Popular.PopularSeparator U) (hInitial : ∀ i, (L.record i).initial ∉ L.markers)

namespace PortAugmentation

variable (r : L.Request S.cut) {q : FinitePath L.web.graph}
  (hq : q ∈ (L.shortenedRecordFan S r hInitial).paths) (D : L.PortAugmentation S.cut q r)

include hq in
theorem backward_mem_localMatching {x y : V}
    (he : (.inr y, .inl x) ∈ D.path.edgeSet) : D.localMatching L x y := by
  have hAdj := D.path.edgeSet_subset_adj he
  have hOld : L.originStoppedMatching S.cut D.origin D.departure x y := hAdj.1
  refine ⟨hOld, ?_⟩
  obtain ⟨b, hbq, hb⟩ := hAdj.2.1
  rcases hAdj.2.2 with hx | ⟨a, haq, har, ha⟩
  · exact (D.source_unmatched L y (hx ▸ hOld)).elim
  · have hRef := L.residualMatching_subset_reference S.cut
      (L.stoppedMatching_subset_residual S.cut hOld.1)
    have hab := (L.referenceMatching_iff_same_vertex ha hb).1 hRef
    subst b
    cases a with
    | source i => simp [receiving] at hb
    | marker z => simp [sending] at ha
    | off z => exact Or.inl ((Option.some.inj ha).symm.trans (Option.some.inj hb))
    | edge e =>
        have hexy : e.1 = (x, y) := Prod.ext (Option.some.inj ha) (Option.some.inj hb)
        have heCut : e.1 ∉ L.cutEdges S.cut := by
          intro hcut
          exact L.residualMatching_not_of_cutEdge S.cut (hexy ▸ hcut)
            (L.stoppedMatching_subset_residual S.cut hOld.1)
        let t : L.RouteEdge S.cut q := ⟨e, haq, heCut⟩
        have heP := L.routeFragment_edge S.cut q t
        have heStop := L.shortenedRecordFan_internal_edge_mem_stopped S hInitial r hq
          e heP haq har
        exact Or.inr (Or.inr ⟨L.routeFragment S.cut q t, Or.inl ⟨t, rfl⟩, hexy ▸ heStop⟩)

def localTogglePath : AugmentingPath G (D.localMatching L) where
  portGraph := (D.togglePath L).portGraph
  path := D.path
  first := D.departure
  last := L.requestVertex r
  path_start := D.path_start
  path_finish := D.path_finish
  step := by
    intro a b he
    cases a with
    | inl x =>
        cases b with
        | inl y => exact (D.togglePath L).step he
        | inr y =>
            have hstep := (D.togglePath L).step he
            exact ⟨hstep.1, fun h ↦ hstep.2 h.1⟩
    | inr y =>
        cases b with
        | inl x => exact D.backward_mem_localMatching L S hInitial r hq he
        | inr z => exact (D.togglePath L).step he
  first_free := fun y h ↦ D.source_unmatched L y h.1
  last_free := fun x h ↦ D.request_unmatched L x h.1

def localSwitchedEdges : Set (V × V) := (D.localTogglePath L S hInitial r hq).projectedEdges

theorem localSwitchedEdges_biUnique :
    Relator.BiUnique (fun x y ↦ (x, y) ∈ D.localSwitchedEdges L S hInitial r hq) :=
  (D.localTogglePath L S hInitial r hq).projectedEdges_biUnique (D.localMatching_biUnique L)

theorem localSwitchedEdges_edgeBalance (x : V) :
    edgeBalance (D.localSwitchedEdges L S hInitial r hq) x =
      edgeBalance (D.localBaseEdges L) x +
        propInt (x = D.departure) - propInt (x = L.requestVertex r) :=
  (D.localTogglePath L S hInitial r hq).projectedEdges_edgeBalance (D.localMatching_biUnique L) x

theorem localSwitchedEdges_subset_switchedEdges :
    D.localSwitchedEdges L S hInitial r hq ⊆ D.switchedEdges L := by
  rintro e ⟨he | he, hne⟩
  · exact ⟨Or.inl ⟨he.1.1, he.2⟩, hne⟩
  · exact ⟨Or.inr he, hne⟩

theorem localSwitchedEdges_noReverseRay :
    ¬ ContainsReverseDirectedRay (D.localSwitchedEdges L S hInitial r hq) := by
  rintro ⟨R, hR⟩
  exact D.switchedEdges_noReverseRay L
    ⟨R, fun n ↦ D.localSwitchedEdges_subset_switchedEdges L S hInitial r hq (hR n)⟩

#print axioms backward_mem_localMatching
#print axioms localSwitchedEdges_biUnique
#print axioms localSwitchedEdges_edgeBalance
#print axioms localSwitchedEdges_noReverseRay

end PortAugmentation
end Erdos599.GroundingAllMarkerAuxiliary.Input
