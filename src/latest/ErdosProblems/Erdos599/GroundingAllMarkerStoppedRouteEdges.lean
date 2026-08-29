/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.GroundingAllMarkerStoppedFragments
import ErdosProblems.Erdos599.GroundingAllMarkerIndependentGeometry

/-!
# The selected routes retain their backward edges after stopping

Shortened paths are not assumed to belong to the original normalized
fan. Their support-containment certificates transfer the nonescape
theorem from an actual original fan member. Internal sending ports also
avoid default terminal blockers and the off-reference part of the cut.
-/

namespace Erdos599.GroundingAllMarkerAuxiliary.Input

open Set Cardinal DirectedPath Alternating GroundingAllMarkerPorts

universe u

variable {V I : Type u} {G : DWeb V} (L : Input G I) {kappa : Cardinal.{u}}
  {U : Popular.KappaIndexed L.web kappa} (S : Popular.PopularSeparator U)
  (hInitial : ∀ i, (L.record i).initial ∉ L.markers)

theorem shortenedRecordFan_sending_not_escape (r : L.Request S.cut)
    {q : FinitePath L.web.graph} (hq : q ∈ (L.shortenedRecordFan S r hInitial).paths)
    {a : L.Vertex} (ha : a ∈ q.support) (har : a ≠ r.1) {x : V}
    (hsend : L.sending a = some x) : x ∉ L.escapeRegion S.cut := by
  obtain ⟨p, rfl⟩ := hq
  exact L.normalizedRequestFan_sending_not_escape S r
    (L.goodRecordFan_subset_normalized S r (L.prunedRecordFan_subset_good S r p.2))
    ((L.shortenedPrunedPath_spec S r hInitial p).2.2.1 ha) har hsend

theorem shortenedRecordFan_receiving_not_escape (r : L.Request S.cut)
    {q : FinitePath L.web.graph} (hq : q ∈ (L.shortenedRecordFan S r hInitial).paths)
    {a : L.Vertex} (ha : a ∈ q.support) (har : a ≠ r.1) {x : V}
    (hreceive : L.receiving a = some x) : ¬ L.Escapes S.cut (.inr x) := by
  obtain ⟨p, rfl⟩ := hq
  exact L.normalizedRequestFan_receiving_not_escape S r
    (L.goodRecordFan_subset_normalized S r (L.prunedRecordFan_subset_good S r p.2))
    ((L.shortenedPrunedPath_spec S r hInitial p).2.2.1 ha) har hreceive

/-- The reversed edge of every internal gadget is still an edge of its
actual stopped fragment, not merely of its uncut parent. -/
theorem shortenedRecordFan_internal_edge_mem_stopped (r : L.Request S.cut)
    {q : FinitePath L.web.graph} (hq : q ∈ (L.shortenedRecordFan S r hInitial).paths)
    {P : L.CutFragment}
    (e : {e : V × V // e ∈ familyEdges L.reference.paths})
    (heP : e.1 ∈ P.path.edgeSet) (heq : Vertex.edge e ∈ q.support)
    (her : Vertex.edge e ≠ r.1) : e.1 ∈ (L.stoppedFragment S.cut P).edgeSet :=
  L.edge_mem_stoppedFragment_of_tail_not_escape S.cut heP
    (L.shortenedRecordFan_sending_not_escape S hInitial r hq heq her rfl)

/-- Finite source terminals, internal edge tails and internal off-reference
ports all avoid the blocking set. Ray departures have no represented
sending port and are handled separately by their whole-record avoidance. -/
theorem shortenedRecordFan_sending_not_blockingSet (r : L.Request S.cut)
    {q : FinitePath L.web.graph} (hq : q ∈ (L.shortenedRecordFan S r hInitial).paths)
    {a : L.Vertex} (ha : a ∈ q.support) (har : a ≠ r.1) {x : V}
    (hsend : L.sending a = some x) : x ∉ L.blockingSet S.cut := by
  have haCut : a ∉ S.cut := fun h ↦
    har (L.shortenedRecordFan_cut_normalized S r hInitial hq ⟨ha, h⟩)
  have hxR := L.shortenedRecordFan_sending_not_escape S hInitial r hq ha har hsend
  cases a with
  | source i =>
      have hstart : Vertex.source i = q.start := by
        by_contra hne
        obtain ⟨b, hb⟩ := FinitePath.exists_incoming_edge_of_mem_support_of_ne_start q ha hne
        exact L.not_adj_to_source b i (q.edgeSet_subset_adj hb)
      obtain ⟨j, hqj, hjGood⟩ := L.shortenedRecordFan_start_good_record S r hInitial hq
      have hij : i = j := Vertex.source.inj (hstart.trans hqj)
      subst j
      exact Set.disjoint_left.mp (L.goodRecordVertices_disjoint_blockingSet S.cut S.separates)
        ⟨i, hjGood, G.terminal_mem_support hsend⟩
  | marker y => simp [sending] at hsend
  | edge e =>
      have hex : e.1.1 = x := Option.some.inj hsend
      have heCut : e.1 ∉ L.cutEdges S.cut := fun he ↦ haCut he.2
      have heResidual : L.residualMatching S.cut x e.1.2 := hex ▸ Or.inl ⟨e.2, heCut⟩
      rintro (hxOff | hxEscape | hxEnd)
      · exact L.not_mem_cutOff_of_mem_reference S.cut
          (hex ▸ (familyEdges_subset_vertexSet_prod L.reference.paths e.2).1) hxOff
      · exact hxR hxEscape.2.1
      · exact hxEnd.2.2.1 e.1.2 heResidual
  | off z =>
      have hzx : z.1 = x := Option.some.inj hsend
      rintro (hxOff | hxEscape | hxEnd)
      · obtain ⟨hx, hcut⟩ := hxOff
        exact haCut (by simpa only [← hzx] using hcut)
      · exact z.2 (hzx ▸ hxEscape.1)
      · exact z.2 (hzx ▸ hxEnd.1)

theorem independentSelectedPath_internal_edge_mem_stopped (r : L.Request S.cut)
    {P : L.CutFragment}
    (e : {e : V × V // e ∈ familyEdges L.reference.paths})
    (heP : e.1 ∈ P.path.edgeSet)
    (heq : Vertex.edge e ∈ (L.independentSelectedPath S hInitial r).support)
    (her : Vertex.edge e ≠ r.1) : e.1 ∈ (L.stoppedFragment S.cut P).edgeSet :=
  L.shortenedRecordFan_internal_edge_mem_stopped S hInitial r
    (L.independentSelectedPath_mem S hInitial r) e heP heq her

theorem independentSelectedPath_sending_not_blockingSet (r : L.Request S.cut)
    {a : L.Vertex} (ha : a ∈ (L.independentSelectedPath S hInitial r).support)
    (har : a ≠ r.1) {x : V} (hsend : L.sending a = some x) :
    x ∉ L.blockingSet S.cut :=
  L.shortenedRecordFan_sending_not_blockingSet S hInitial r
    (L.independentSelectedPath_mem S hInitial r) ha har hsend

#print axioms shortenedRecordFan_internal_edge_mem_stopped
#print axioms shortenedRecordFan_sending_not_blockingSet
#print axioms independentSelectedPath_internal_edge_mem_stopped
#print axioms independentSelectedPath_sending_not_blockingSet

end Erdos599.GroundingAllMarkerAuxiliary.Input
