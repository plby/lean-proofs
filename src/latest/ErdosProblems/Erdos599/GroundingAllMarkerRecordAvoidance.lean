/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.GroundingAllMarkerResidualEncoding

/-!
# Entire surviving record owners avoid the residual escape region

Every sending port on a record is represented in its carrier: by the
source at a finite terminal, or by its outgoing reference-edge gadget.
The existing carrier reachability theorem includes rays using their real
proxy departures. Concatenating a carrier path with a recontracted escape
would violate the auxiliary separator. This excludes every vertex of each
uncut record, not only finite terminals or selected representatives.
-/

namespace Erdos599.GroundingAllMarkerAuxiliary.Input

open Set DirectedPath Alternating GroundingAllMarkerPorts

universe u

variable {V I : Type u} {G : DWeb V} (L : Input G I)

theorem cutAvoidingWalk_trans (C : Set L.Vertex) {a b c : L.Vertex}
    (hab : L.CutAvoidingWalk C a b) (hbc : L.CutAvoidingWalk C b c) :
    L.CutAvoidingWalk C a c := by
  obtain ⟨p, hp⟩ := hab
  obtain ⟨q, hq⟩ := hbc
  refine ⟨p.append q, ?_⟩
  intro z hz
  rw [Walk.support_append, List.mem_append] at hz
  exact hz.elim (hp z) (fun hz ↦ hq z (List.mem_of_mem_tail hz))

/-- Every original record vertex has a sending-port representative in
the record's actual carrier. The ray case always uses an outgoing edge. -/
theorem exists_recordCarrier_sending (i : I) {x : V}
    (hx : x ∈ (L.record i).support) :
    ∃ a ∈ L.recordCarrier i, L.sending a = some x := by
  have hedge : (∃ y, (x, y) ∈ (L.record i).edgeSet) →
      ∃ a ∈ L.recordCarrier i, L.sending a = some x := by
    rintro ⟨y, hxy⟩
    have heY : (x, y) ∈ familyEdges L.reference.paths := by
      simp only [familyEdges, Set.mem_iUnion]
      exact ⟨L.record i, L.record_mem i, hxy⟩
    exact ⟨.edge ⟨(x, y), heY⟩, hxy, rfl⟩
  cases hi : L.record i with
  | inl f =>
      by_cases hxf : x = f.finish
      · refine ⟨.source i, rfl, ?_⟩
        simp only [sending, hi, Path.terminal?, hxf]
      · apply hedge
        have hxfSupport : x ∈ f.support := by simpa only [hi, Path.support] using hx
        obtain ⟨y, hxy⟩ := FinitePath.exists_outgoing_edge_of_mem_support_of_ne_finish
          f hxfSupport hxf
        exact ⟨y, by simpa only [hi, Path.edgeSet] using hxy⟩
  | inr r =>
      apply hedge
      have hxr : x ∈ r.support := by simpa only [hi, Path.support] using hx
      obtain ⟨n, rfl⟩ := hxr
      refine ⟨r (n + 1), ?_⟩
      rw [hi]
      exact ⟨n, rfl⟩

theorem recordCarrier_disjoint_cut_of_not_bad (C : Set L.Vertex) {i : I}
    (hi : i ∉ L.badRecords C) : Disjoint (L.recordCarrier i) C := by
  apply Set.disjoint_left.mpr
  intro a ha haC
  exact hi ((L.recordCarrier_meets_cut_iff C i).mp ⟨a, ha, haC⟩)

theorem cutAvoidingWalk_to_recordCarrier (C : Set L.Vertex) {i : I}
    (hi : i ∉ L.badRecords C) {a : L.Vertex} (ha : a ∈ L.recordCarrier i) :
    L.CutAvoidingWalk C (.source i) a := by
  obtain ⟨p, hstart, hfinish, hsupp⟩ := L.recordCarrier_internally_reachable i a ha
  rcases p with ⟨s, t, w, hpath⟩
  change s = Vertex.source i at hstart
  change t = a at hfinish
  subst s
  subst t
  exact ⟨w, fun _ hz ↦
    Set.disjoint_left.mp (L.recordCarrier_disjoint_cut_of_not_bad C hi) (hsupp hz)⟩

theorem not_escapes_of_mem_uncut_record (C : Set L.Vertex)
    (hC : Popular.IsSeparator L.web C) {i : I} (hi : i ∉ L.badRecords C)
    {x : V} (hx : x ∈ (L.record i).support) : ¬ L.Escapes C (.inl x) := by
  intro hescape
  obtain ⟨a, ha, hsend⟩ := L.exists_recordCarrier_sending i hx
  have haC : a ∉ C :=
    Set.disjoint_left.mp (L.recordCarrier_disjoint_cut_of_not_bad C hi) ha
  obtain ⟨y, hay⟩ := L.cutAvoidingWalk_of_sending_escape C hsend haC hescape
  exact L.not_cutAvoidingWalk_source_marker C hC i y
    (L.cutAvoidingWalk_trans C (L.cutAvoidingWalk_to_recordCarrier C hi ha) hay)

theorem record_disjoint_escapeRegion (C : Set L.Vertex)
    (hC : Popular.IsSeparator L.web C) {i : I}
    (hiC : Vertex.source i ∉ C)
    (hiEdges : Disjoint (L.record i).edgeSet (L.cutEdges C)) :
    Disjoint (L.record i).support (L.escapeRegion C) := by
  have hi : i ∉ L.badRecords C := by
    rintro (hsource | ⟨e, he, heC⟩)
    · exact hiC hsource
    · exact Set.disjoint_left.mp hiEdges he heC
  exact Set.disjoint_left.mpr (fun _ hx ↦ L.not_escapes_of_mem_uncut_record C hC hi hx)

#print axioms exists_recordCarrier_sending
#print axioms cutAvoidingWalk_to_recordCarrier
#print axioms not_escapes_of_mem_uncut_record
#print axioms record_disjoint_escapeRegion

end Erdos599.GroundingAllMarkerAuxiliary.Input
