/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.GroundingAllMarkerPortSwitch
import ErdosProblems.Erdos599.GroundingAllMarkerRequestInitials

/-!
# A finite set of actual fragments for each auxiliary route

Uncut edge gadgets in a finite route select finitely many surviving
fragments. The request contributes at most one more fragment, exactly
when its receiving vertex is on the reference. No whole bad original
owner is substituted for one of its cut fragments.
-/

noncomputable section

namespace Erdos599.GroundingAllMarkerAuxiliary.Input

open Set Cardinal DirectedPath Alternating GroundingAllMarkerPorts

universe u

variable {V I : Type u} {G : DWeb V} (L : Input G I)

abbrev RouteEdge (C : Set L.Vertex) (q : FinitePath L.web.graph) :=
  {e : {e : V × V // e ∈ familyEdges L.reference.paths} //
    Vertex.edge e ∈ q.support ∧ e.1 ∉ L.cutEdges C}

theorem routeEdge_finite (C : Set L.Vertex) (q : FinitePath L.web.graph) :
    Finite (L.RouteEdge C q) := by
  have hinj : Function.Injective
      (Vertex.edge : {e : V × V // e ∈ familyEdges L.reference.paths} → L.Vertex) :=
    fun _ _ h ↦ Vertex.edge.inj h
  have hf := Set.Finite.preimage hinj.injOn q.support_finite
  exact (hf.subset (fun _ h ↦ h.1)).to_subtype

def routeFragment (C : Set L.Vertex) (q : FinitePath L.web.graph)
    (e : L.RouteEdge C q) : L.CutFragment := L.edgeFragment C e.1 e.2.2

theorem routeFragment_mem (C : Set L.Vertex) (q : FinitePath L.web.graph)
    (e : L.RouteEdge C q) : L.routeFragment C q e ∈ L.cutFragments C :=
  L.edgeFragment_mem C e.1 e.2.2

theorem routeFragment_edge (C : Set L.Vertex) (q : FinitePath L.web.graph)
    (e : L.RouteEdge C q) : e.1.1 ∈ (L.routeFragment C q e).path.edgeSet :=
  L.edgeFragment_edge C e.1 e.2.2

def selectedRequestFragments (C : Set L.Vertex) (r : L.Request C) : Set L.CutFragment := by
  classical
  exact if h : L.requestVertex r ∈ G.vertexSet L.reference.paths then
    {L.requestFragment ⟨r, (L.requestFragment_exists_iff_mem_reference C r).2 h⟩}
  else ∅

theorem selectedRequestFragments_finite (C : Set L.Vertex) (r : L.Request C) :
    (L.selectedRequestFragments C r).Finite := by
  classical
  unfold selectedRequestFragments
  split_ifs
  · exact Set.finite_singleton _
  · exact Set.finite_empty

theorem selectedRequestFragments_spec (C : Set L.Vertex) (r : L.Request C)
    {P : L.CutFragment} (hP : P ∈ L.selectedRequestFragments C r) :
    P ∈ L.cutFragments C ∧ P.path.initial = L.requestVertex r := by
  classical
  unfold selectedRequestFragments at hP
  split_ifs at hP with h
  · obtain rfl := hP
    exact ⟨L.requestFragment_mem _, L.requestFragment_initial _⟩
  · exact hP.elim

theorem selectedRequestFragments_nonempty (C : Set L.Vertex) (r : L.Request C)
    (hr : L.requestVertex r ∈ G.vertexSet L.reference.paths) :
    (L.selectedRequestFragments C r).Nonempty := by
  classical
  simp only [selectedRequestFragments, dif_pos hr, Set.singleton_nonempty]

def localFragments (C : Set L.Vertex) (q : FinitePath L.web.graph) (r : L.Request C) :
    Set L.CutFragment := Set.range (L.routeFragment C q) ∪ L.selectedRequestFragments C r

theorem localFragments_finite (C : Set L.Vertex) (q : FinitePath L.web.graph) (r : L.Request C) :
    (L.localFragments C q r).Finite := by
  let := L.routeEdge_finite C q
  exact (Set.finite_range (L.routeFragment C q)).union (L.selectedRequestFragments_finite C r)

theorem localFragments_mem (C : Set L.Vertex) (q : FinitePath L.web.graph) (r : L.Request C)
    {P : L.CutFragment} (hP : P ∈ L.localFragments C q r) : P ∈ L.cutFragments C := by
  rcases hP with ⟨e, rfl⟩ | hP
  · exact L.routeFragment_mem C q e
  · exact (L.selectedRequestFragments_spec C r hP).1

variable {kappa : Cardinal.{u}} {U : Popular.KappaIndexed L.web kappa}
  (S : Popular.PopularSeparator U) (hInitial : ∀ i, (L.record i).initial ∉ L.markers)
  (hInitials : G.initialSet L.reference.paths ⊆ G.source ∪ L.markers)

include hInitials

theorem routeFragment_grounded (r : L.Request S.cut) {q : FinitePath L.web.graph}
    (hq : q ∈ (L.shortenedRecordFan S r hInitial).paths) (e : L.RouteEdge S.cut q) :
    L.CutFragmentGrounded (L.routeFragment S.cut q e) := by
  by_contra hhang
  have hdisj := L.shortenedRecordFan_avoids_hanging_fragment S r hInitial hInitials hq
    (L.routeFragment_mem S.cut q e) hhang
  exact Set.disjoint_left.mp hdisj e.2.1 (L.routeFragment_edge S.cut q e)

theorem localFragments_initial_profile (r : L.Request S.cut) {q : FinitePath L.web.graph}
    (hq : q ∈ (L.shortenedRecordFan S r hInitial).paths)
    {P : L.CutFragment} (hP : P ∈ L.localFragments S.cut q r) :
    L.CutFragmentGrounded P ∨ P.path.initial = L.requestVertex r := by
  rcases hP with ⟨e, rfl⟩ | hP
  · exact Or.inl (L.routeFragment_grounded S hInitial hInitials r hq e)
  · exact Or.inr (L.selectedRequestFragments_spec S.cut r hP).2

#print axioms localFragments_finite
#print axioms localFragments_mem
#print axioms localFragments_initial_profile

end Erdos599.GroundingAllMarkerAuxiliary.Input
