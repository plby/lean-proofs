/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.GroundingAllMarkerStoppedMatching

/-!
# Internal route matching pairs survive stopping and origin truncation

Both contracted reference-edge pairs and off-reference identity pairs
remain available internally. Truncation at a finite record's terminal
deletes no edge of that record; a shortened ray-origin route uses no
represented port on its ray, so truncation cannot delete its pairs either.
-/

namespace Erdos599.GroundingAllMarkerAuxiliary.Input

open Set Cardinal DirectedPath Alternating GroundingAllMarkerPorts

universe u

variable {V I : Type u} {G : DWeb V} (L : Input G I)

theorem originStoppedMatching_of_finite_terminal (C : Set L.Vertex) (i : I)
    (f : FinitePath G.graph) (hi : L.record i = .inl f) {x y : V}
    (h : L.stoppedMatching C x y) : L.originStoppedMatching C i f.finish x y := by
  refine ⟨h, ?_⟩
  intro hx
  have href := L.residualMatching_subset_reference C (L.stoppedMatching_subset_residual C h)
  rcases href with he | ⟨_, hxOff⟩
  · simp only [familyEdges, Set.mem_iUnion] at he
    obtain ⟨P, hP, heP⟩ := he
    have hPi : P = L.record i := DWeb.IsWarp.eq_of_mem_support L.reference.disjoint
      hP (L.record_mem i) (P.edgeSet_subset_support_prod heP).1 hx
    have heF : (x, y) ∈ f.edgeSet := by simpa only [hPi, hi, Path.edgeSet] using heP
    refine ⟨GroundingCut.beforeEq_terminal (by rw [hi]; rfl) hx, ?_⟩
    exact (Walk.finish_ne_edge_source f.walk f.isPath heF).symm
  · exact (hxOff ⟨L.record i, L.record_mem i, hx⟩).elim

variable {kappa : Cardinal.{u}} {U : Popular.KappaIndexed L.web kappa}
  (S : Popular.PopularSeparator U) (hInitial : ∀ i, (L.record i).initial ∉ L.markers)

theorem shortenedRecordFan_internal_stoppedMatching (r : L.Request S.cut)
    {q : FinitePath L.web.graph} (hq : q ∈ (L.shortenedRecordFan S r hInitial).paths)
    {a : L.Vertex} (ha : a ∈ q.support) (har : a ≠ r.1) {x y : V}
    (hsend : L.sending a = some x) (hreceive : L.receiving a = some y) :
    L.stoppedMatching S.cut x y := by
  have haCut : a ∉ S.cut := fun h ↦
    har (L.shortenedRecordFan_cut_normalized S r hInitial hq ⟨ha, h⟩)
  cases a with
  | source i => simp [receiving] at hreceive
  | marker z => simp [sending] at hsend
  | edge e =>
      have heCut : e.1 ∉ L.cutEdges S.cut := fun h ↦ haCut h.2
      obtain ⟨P, hP, heP⟩ := L.exists_cutFragment_containing_edge S.cut e.2 heCut
      have heStop := L.shortenedRecordFan_internal_edge_mem_stopped S hInitial r hq e heP ha har
      exact Or.inl ⟨P, hP, (Option.some.inj hsend) ▸ (Option.some.inj hreceive) ▸ heStop⟩
  | off z =>
      have hzx : z.1 = x := Option.some.inj hsend
      have hzy : z.1 = y := Option.some.inj hreceive
      refine Or.inr ⟨hzx.symm.trans hzy, hzx ▸ z.2, ?_⟩
      rintro ⟨hx, hcut⟩
      exact haCut (by simpa only [← hzx] using hcut)

theorem shortenedRecordFan_internal_originMatching_finite (r : L.Request S.cut)
    {q : FinitePath L.web.graph} (hq : q ∈ (L.shortenedRecordFan S r hInitial).paths)
    (i : I) (f : FinitePath G.graph) (hi : L.record i = .inl f)
    {a : L.Vertex} (ha : a ∈ q.support) (har : a ≠ r.1) {x y : V}
    (hsend : L.sending a = some x) (hreceive : L.receiving a = some y) :
    L.originStoppedMatching S.cut i f.finish x y :=
  L.originStoppedMatching_of_finite_terminal S.cut i f hi
    (L.shortenedRecordFan_internal_stoppedMatching S hInitial r hq ha har hsend hreceive)

/-- The departure point can be anywhere on the origin ray: the shortened
route has already removed every represented port of that ray. -/
theorem shortenedRecordFan_internal_originMatching_ray (r : L.Request S.cut)
    {q : FinitePath L.web.graph} (hq : q ∈ (L.shortenedRecordFan S r hInitial).paths)
    (i : I) (ray : Ray G.graph) (hi : L.record i = .inr ray) (hqi : q.start = .source i)
    (departure : V) {a : L.Vertex} (ha : a ∈ q.support) (har : a ≠ r.1) {x y : V}
    (hsend : L.sending a = some x) (hreceive : L.receiving a = some y) :
    L.originStoppedMatching S.cut i departure x y := by
  refine ⟨L.shortenedRecordFan_internal_stoppedMatching S hInitial r hq ha har hsend hreceive, ?_⟩
  intro hx
  have hxRay : x ∈ ray.support := by simpa only [hi, Path.support] using hx
  exact ((L.shortenedRecordFan_own_ray_ports S r hInitial hq i ray hqi hi ha hxRay).1 hsend).elim

#print axioms originStoppedMatching_of_finite_terminal
#print axioms shortenedRecordFan_internal_stoppedMatching
#print axioms shortenedRecordFan_internal_originMatching_finite
#print axioms shortenedRecordFan_internal_originMatching_ray

end Erdos599.GroundingAllMarkerAuxiliary.Input
