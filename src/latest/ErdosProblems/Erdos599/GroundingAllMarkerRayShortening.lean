/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.GroundingAllMarkerPrunedFans

/-!
# Last-own-carrier shortening of ray-source paths

A receiving port on a grounded record belongs to its own edge carrier.
Thus leaving that carrier is a genuine original forward departure, not
an identity join. The last-contact suffix can be prefixed directly by
the ray source, preserving endpoints and using only old support vertices.
-/

namespace Erdos599.GroundingAllMarkerAuxiliary.Input

open Set DirectedPath Alternating GroundingAllMarkerPorts

universe u

variable {V I : Type u} {G : DWeb V} (L : Input G I)

theorem record_support_disjoint_markers (i : I)
    (hi : (L.record i).initial ∉ L.markers) : Disjoint (L.record i).support L.markers := by
  apply Set.disjoint_left.mpr
  intro x hxi hxM
  obtain ⟨p, hp, hpx⟩ := L.markers_initial hxM
  have heq : L.record i = p := DWeb.IsWarp.eq_of_mem_support L.reference.disjoint
    (L.record_mem i) hp hxi (hpx ▸ p.initial_mem_support)
  have hinit : (L.record i).initial = x := (congrArg Path.initial heq).trans hpx
  exact hi (hinit.symm ▸ hxM)

/-- With its initial marker excluded, every receiving port on a record
is represented by one of that record's edge gadgets. -/
theorem receiving_mem_recordCarrier (i : I) (hi : (L.record i).initial ∉ L.markers)
    {a : L.Vertex} {x : V} (ha : L.receiving a = some x) (hx : x ∈ (L.record i).support) :
    a ∈ L.recordCarrier i := by
  cases a with
  | source j => simp [receiving] at ha
  | marker y =>
      have hyx : y.1 = x := Option.some.inj ha
      exact (Set.disjoint_left.mp (L.record_support_disjoint_markers i hi) hx (hyx ▸ y.2)).elim
  | off y =>
      have hyx : y.1 = x := Option.some.inj ha
      exact (y.2 ⟨L.record i, L.record_mem i, hyx.symm ▸ hx⟩).elim
  | edge e =>
      have hey : e.1.2 = x := Option.some.inj ha
      have heRef := e.2
      simp only [familyEdges, Set.mem_iUnion] at heRef
      obtain ⟨p, hp, heP⟩ := heRef
      have heq : p = L.record i := DWeb.IsWarp.eq_of_mem_support L.reference.disjoint
        hp (L.record_mem i) (p.edgeSet_subset_support_prod heP).2 (hey.symm ▸ hx)
      change e.1 ∈ (L.record i).edgeSet
      exact heq ▸ heP

/-- Every arc leaving a ray record's carrier has a real original edge
departure and arrives outside that record. -/
theorem ray_carrier_exit (i : I) (r : Ray G.graph) (hi : L.record i = .inr r)
    (hinit : (L.record i).initial ∉ L.markers) {a b : L.Vertex}
    (ha : a ∈ L.recordCarrier i) (hb : b ∉ L.recordCarrier i)
    (hab : L.web.graph.Adj a b) :
    ∃ x ∈ r.support, ∃ y, G.graph.Adj x y ∧ L.receiving b = some y ∧ y ∉ r.support := by
  have hcore : ∃ x ∈ r.support, ∃ y, G.graph.Adj x y ∧ L.receiving b = some y := by
    cases a with
    | source j =>
        change j = i at ha
        subst j
        obtain ⟨_, y, hy, hforward | hproxy⟩ := hab
        · obtain ⟨x, hx, _⟩ := hforward
          simp [sending, hi] at hx
        · obtain ⟨j, s, hij, hjs, x, hx, hxy⟩ := hproxy
          have hij' : i = j := Vertex.source.inj hij
          subst j
          have hsr : s = r := Sum.inr.inj (hjs.symm.trans hi)
          subst s
          exact ⟨x, hx, y, hxy, hy⟩
    | marker y => exact ha.elim
    | off x => exact ha.elim
    | edge e =>
        obtain ⟨_, y, hy, hforward | hproxy⟩ := hab
        · obtain ⟨x, hx, hstep⟩ := hforward
          have hex : e.1.1 = x := Option.some.inj hx
          have hxRecord : x ∈ (L.record i).support :=
            hex ▸ ((L.record i).edgeSet_subset_support_prod ha).1
          have hxRay : x ∈ r.support := by simpa only [hi, Path.support] using hxRecord
          rcases hstep.1 with hxy | hxy
          · exact ⟨x, hxRay, y, hxy, hy⟩
          · exact (hb (L.receiving_mem_recordCarrier i hinit hy (hxy ▸ hxRecord))).elim
        · obtain ⟨j, s, hsource, _⟩ := hproxy
          cases hsource
  obtain ⟨x, hx, y, hxy, hy⟩ := hcore
  refine ⟨x, hx, y, hxy, hy, ?_⟩
  intro hyRay
  apply hb (L.receiving_mem_recordCarrier i hinit hy ?_)
  simpa only [hi, Path.support] using hyRay

private theorem ray_shortcut_from_carrier (i : I) (r : Ray G.graph)
    (hi : L.record i = .inr r) (hinit : (L.record i).initial ∉ L.markers)
    {a b : L.Vertex} (w : Walk L.web.graph a b)
    (ha : a ∈ L.recordCarrier i) (hb : b ∉ L.recordCarrier i)
    (havoid : ∀ z ∈ w.support.tail, z ∉ L.recordCarrier i) (hpath : w.IsPath) :
    ∃ q : Walk L.web.graph (.source i) b, q.IsPath ∧
      (∀ z ∈ q.support, z = .source i ∨ z ∈ w.support) ∧
      (∀ z ∈ q.support, z ∈ L.recordCarrier i → z = .source i) := by
  cases w with
  | nil => exact (hb ha).elim
  | @cons a c b hac tail =>
      have hc : c ∉ L.recordCarrier i := havoid c (by
        simpa only [Walk.support_cons, List.tail_cons] using tail.start_mem_support)
      obtain ⟨x, hx, y, hxy, hy, _hyOutside⟩ := L.ray_carrier_exit i r hi hinit ha hc hac
      have hsc : Vertex.source i ≠ c := by
        intro h
        apply hc
        rw [← h]
        exact rfl
      have hnew : L.web.graph.Adj (.source i) c :=
        ⟨hsc, y, hy, Or.inr ⟨i, r, rfl, hi, x, hx, hxy⟩⟩
      have htailPath : tail.support.Nodup := (List.nodup_cons.mp hpath).2
      refine ⟨.cons hnew tail, ?_, ?_, ?_⟩
      · apply List.nodup_cons.mpr
        refine ⟨?_, htailPath⟩
        intro hs
        exact havoid (.source i) hs rfl
      · intro z hz
        simp only [Walk.support_cons, List.mem_cons] at hz ⊢
        exact hz.elim Or.inl (fun hz ↦ Or.inr (Or.inr hz))
      · intro z hz hzOwn
        simp only [Walk.support_cons, List.mem_cons] at hz
        exact hz.elim id (fun hz ↦ (havoid z hz hzOwn).elim)

/-- Shortening preserves the original finite-path endpoints, simplicity
and support containment, and removes all own-record gadgets. -/
theorem exists_ray_record_shortening (i : I) (r : Ray G.graph)
    (hi : L.record i = .inr r) (hinit : (L.record i).initial ∉ L.markers)
    (p : FinitePath L.web.graph) (hstart : p.start = .source i)
    (hfinish : p.finish ∉ L.recordCarrier i) :
    ∃ q : FinitePath L.web.graph, q.start = p.start ∧ q.finish = p.finish ∧
      q.support ⊆ p.support ∧ q.support ∩ L.recordCarrier i ⊆ {Vertex.source i} := by
  have hmeet : p.walk.Meets (L.recordCarrier i) := by
    refine ⟨p.start, p.start_mem_support, ?_⟩
    rw [hstart]
    exact rfl
  let H := p.walk.lastHit (L.recordCarrier i) hmeet
  have hpath : H.walk.IsPath := H.support_suffix.sublist.nodup p.isPath
  obtain ⟨w, hwPath, hwSub, hwOwn⟩ := L.ray_shortcut_from_carrier i r hi hinit H.walk
    H.startpoint_mem hfinish (fun _ hz ↦ H.no_mem_after hz) hpath
  refine ⟨⟨.source i, p.finish, w, hwPath⟩, hstart.symm, rfl, ?_, ?_⟩
  · intro z hz
    rcases hwSub z hz with rfl | hz
    · exact hstart ▸ p.start_mem_support
    · exact H.support_subset hz
  · intro z hz
    exact hwOwn z hz.1 hz.2

#print axioms receiving_mem_recordCarrier
#print axioms ray_carrier_exit
#print axioms exists_ray_record_shortening

end Erdos599.GroundingAllMarkerAuxiliary.Input
