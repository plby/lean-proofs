/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.GroundingAllMarkerBlockingSet
import ErdosProblems.Erdos599.PopularLayers

/-!
# Actual attachment requests and normalized stationary in-fans

Requests are precisely the non-source vertices of the all-marker auxiliary
cut. Their physical entry is their receiving port, which is unique even
across the three different request sorts. The popular separator supplies
local stationary fans. The proved good-subfan theorem normalizes them
against the entire cut, rather than inferring avoidance from strict-roof
containment alone.
-/

noncomputable section

namespace Erdos599.GroundingAllMarkerAuxiliary.Input

open Set Cardinal DirectedPath Alternating GroundingAllMarkerPorts

universe u

variable {V I : Type u} {G : DWeb V} (L : Input G I) {kappa : Cardinal.{u}}

abbrev Request (C : Set L.Vertex) := (C \ L.web.source : Set L.Vertex)

theorem exists_receiving_of_not_source {a : L.Vertex} (ha : a ∉ L.web.source) :
    ∃ x : V, L.receiving a = some x := by
  cases a with
  | source i => exact (ha ⟨i, rfl⟩).elim
  | marker y => exact ⟨y.1, rfl⟩
  | edge e => exact ⟨e.1.2, rfl⟩
  | off x => exact ⟨x.1, rfl⟩

def requestVertex {C : Set L.Vertex} (r : L.Request C) : V :=
  Classical.choose (L.exists_receiving_of_not_source r.2.2)

theorem request_receiving {C : Set L.Vertex} (r : L.Request C) :
    L.receiving r.1 = some (L.requestVertex r) :=
  Classical.choose_spec (L.exists_receiving_of_not_source r.2.2)

/-- Distinct requests, including ones on different cut edges of one
original owner, have distinct physical receiving entries. -/
theorem requestVertex_injective (C : Set L.Vertex) :
    Function.Injective (L.requestVertex (C := C)) := by
  intro r s hrs
  apply Subtype.ext
  exact L.receiving_unique (L.request_receiving r) (hrs ▸ L.request_receiving s)

theorem request_cases {C : Set L.Vertex} (r : L.Request C) :
    (∃ y : L.markers, r.1 = Vertex.marker y) ∨
    (∃ e : {e : V × V // e ∈ familyEdges L.reference.paths}, r.1 = Vertex.edge e) ∨
    (∃ x : {x : V // x ∉ G.vertexSet L.reference.paths}, r.1 = Vertex.off x) := by
  cases h : r.1 with
  | source i => exact (r.2.2 ⟨i, h.symm⟩).elim
  | marker y => exact Or.inl ⟨y, rfl⟩
  | edge e => exact Or.inr (Or.inl ⟨e, rfl⟩)
  | off x => exact Or.inr (Or.inr ⟨x, rfl⟩)

theorem requests_card_le {U : Popular.KappaIndexed L.web kappa}
    (S : Popular.PopularSeparator U) : #(L.Request S.cut) ≤ kappa :=
  Cardinal.lift_le.1 S.card_diff_source

def rawRequestFan {U : Popular.KappaIndexed L.web kappa}
    (S : Popular.PopularSeparator U) (r : L.Request S.cut) :
    Popular.JoinedFamily L.web {r.1} :=
  Classical.choose ((S.locally_popular r.1 r.2.1).resolve_left r.2.2)

theorem rawRequestFan_stationary {U : Popular.KappaIndexed L.web kappa}
    (S : Popular.PopularSeparator U) (r : L.Request S.cut) :
    Stationary.IsStationaryBelow kappa
      (Popular.initialIndicesOf U (L.rawRequestFan S r).paths
        (L.rawRequestFan S r).starts_in_source) :=
  (Classical.choose_spec ((S.locally_popular r.1 r.2.1).resolve_left r.2.2)).1

theorem rawRequestFan_support_subset {U : Popular.KappaIndexed L.web kappa}
    (S : Popular.PopularSeparator U) (r : L.Request S.cut)
    {p : FinitePath L.web.graph} (hp : p ∈ (L.rawRequestFan S r).paths) :
    p.support ⊆ L.web.strictRoof S.cut ∪ {r.1} :=
  (Classical.choose_spec ((S.locally_popular r.1 r.2.1).resolve_left r.2.2)).2 p hp

def normalizedRequestFan {U : Popular.KappaIndexed L.web kappa}
    (S : Popular.PopularSeparator U) (r : L.Request S.cut) :
    Popular.JoinedFamily L.web {r.1} :=
  Popular.goodJoinedFamily (L.rawRequestFan S r) S.cut

theorem normalizedRequestFan_stationary {U : Popular.KappaIndexed L.web kappa}
    (S : Popular.PopularSeparator U) (r : L.Request S.cut) :
    Stationary.IsStationaryBelow kappa
      (Popular.initialIndicesOf U (L.normalizedRequestFan S r).paths
        (L.normalizedRequestFan S r).starts_in_source) :=
  Popular.goodJoinedFamily_stationary U (L.rawRequestFan S r) S.cut
    (L.rawRequestFan_stationary S r) S.not_strongly_popular

theorem normalizedRequestFan_cut_normalized {U : Popular.KappaIndexed L.web kappa}
    (S : Popular.PopularSeparator U) (r : L.Request S.cut)
    {p : FinitePath L.web.graph} (hp : p ∈ (L.normalizedRequestFan S r).paths) :
    p.support ∩ S.cut ⊆ {r.1} :=
  Popular.goodJoinedFamily_normalized (L.rawRequestFan S r) S.cut hp

theorem normalizedRequestFan_support_subset {U : Popular.KappaIndexed L.web kappa}
    (S : Popular.PopularSeparator U) (r : L.Request S.cut)
    {p : FinitePath L.web.graph} (hp : p ∈ (L.normalizedRequestFan S r).paths) :
    p.support ⊆ L.web.strictRoof S.cut ∪ {r.1} :=
  L.rawRequestFan_support_subset S r hp.1

theorem normalizedRequestFan_finish {U : Popular.KappaIndexed L.web kappa}
    (S : Popular.PopularSeparator U) (r : L.Request S.cut)
    {p : FinitePath L.web.graph} (hp : p ∈ (L.normalizedRequestFan S r).paths) :
    p.finish = r.1 := (L.normalizedRequestFan S r).ends_in_join hp

theorem normalizedRequestFan_start_not_cut {U : Popular.KappaIndexed L.web kappa}
    (S : Popular.PopularSeparator U) (r : L.Request S.cut)
    {p : FinitePath L.web.graph} (hp : p ∈ (L.normalizedRequestFan S r).paths) :
    p.start ∉ S.cut := by
  intro hpC
  have hstart : p.start = r.1 := L.normalizedRequestFan_cut_normalized S r hp
    ⟨p.start_mem_support, hpC⟩
  exact r.2.2 (hstart ▸ (L.normalizedRequestFan S r).starts_in_source hp)

#print axioms requestVertex_injective
#print axioms requests_card_le
#print axioms normalizedRequestFan_stationary
#print axioms normalizedRequestFan_cut_normalized

end Erdos599.GroundingAllMarkerAuxiliary.Input
