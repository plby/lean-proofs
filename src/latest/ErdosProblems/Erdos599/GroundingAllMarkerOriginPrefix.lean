/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.GroundingAllMarkerLocalFragments

/-!
# The actual origin prefix and its retained matching edges

A departure is a certified vertex on a good origin record, not an
invented terminal for a ray. The finite initial prefix through it is
exactly the retained matching relation on that record.
-/

noncomputable section

namespace Erdos599.GroundingAllMarkerAuxiliary.Input.PortAugmentation

open Set DirectedPath Alternating GroundingAllMarkerPorts

universe u

variable {V I : Type u} {G : DWeb V} (L : Input G I)
  {C : Set L.Vertex} {q : FinitePath L.web.graph} {r : L.Request C}
  (D : L.PortAugmentation C q r)

def originPrefix : FinitePath G.graph :=
  Classical.choose (GroundingPathPrefix.exists_initialFinitePrefix
    (L.record D.origin) D.departure_mem)

theorem originPrefix_spec :
    (D.originPrefix L).start = (L.record D.origin).initial ∧
      (D.originPrefix L).finish = D.departure ∧
      (D.originPrefix L).support ⊆ (L.record D.origin).support ∧
      (D.originPrefix L).edgeSet ⊆ (L.record D.origin).edgeSet :=
  Classical.choose_spec (GroundingPathPrefix.exists_initialFinitePrefix
    (L.record D.origin) D.departure_mem)

theorem originPrefix_edge_mem_matching (hC : Popular.IsSeparator L.web C) {x y : V}
    (he : (x, y) ∈ (D.originPrefix L).edgeSet) :
    L.originStoppedMatching C D.origin D.departure x y := by
  have hspec := D.originPrefix_spec L
  have heOrigin := hspec.2.2.2 he
  have hxOrigin := ((L.record D.origin).edgeSet_subset_support_prod heOrigin).1
  refine ⟨Or.inl ⟨L.recordFragment D.origin,
    L.recordFragment_mem C D.origin D.origin_good, ?_⟩, ?_⟩
  · exact L.edge_mem_stoppedFragment_of_tail_not_escape C heOrigin
      (L.not_escapes_of_mem_uncut_record C hC D.origin_good hxOrigin)
  · intro _
    have hbefore := (GroundingInitialPrefixOrder.mem_edgeSet_iff_before_finish
      (L.record D.origin) (D.originPrefix L) hspec.1 hspec.2.2).1 he
    exact hspec.2.1 ▸ hbefore.2

theorem matching_edge_mem_originPrefix {x y : V}
    (h : L.originStoppedMatching C D.origin D.departure x y)
    (hx : x ∈ (L.record D.origin).support) : (x, y) ∈ (D.originPrefix L).edgeSet := by
  have hspec := D.originPrefix_spec L
  have heOrigin : (x, y) ∈ (L.record D.origin).edgeSet := by
    rcases L.residualMatching_subset_reference C
        (L.stoppedMatching_subset_residual C h.1) with he | ⟨_, hxOff⟩
    · simp only [familyEdges, Set.mem_iUnion] at he
      obtain ⟨P, hP, heP⟩ := he
      have hPi : P = L.record D.origin := DWeb.IsWarp.eq_of_mem_support L.reference.disjoint
        hP (L.record_mem D.origin) (P.edgeSet_subset_support_prod heP).1 hx
      exact hPi ▸ heP
    · exact (hxOff ⟨L.record D.origin, L.record_mem D.origin, hx⟩).elim
  apply (GroundingInitialPrefixOrder.mem_edgeSet_iff_before_finish
    (L.record D.origin) (D.originPrefix L) hspec.1 hspec.2.2).2
  exact ⟨heOrigin, hspec.2.1.symm ▸ h.2 hx⟩

theorem departure_eq_initial_of_prefix_noIncoming
    (hfree : ¬ HasIncoming (D.originPrefix L).edgeSet D.departure) :
    D.departure = (L.record D.origin).initial := by
  have hspec := D.originPrefix_spec L
  by_contra hne
  have hx : D.departure ∈ (D.originPrefix L).support :=
    hspec.2.1 ▸ (D.originPrefix L).finish_mem_support
  have hstart : D.departure ≠ (D.originPrefix L).start := by rwa [hspec.1]
  exact hfree (FinitePath.exists_incoming_edge_of_mem_support_of_ne_start
    (D.originPrefix L) hx hstart)

#print axioms originPrefix_edge_mem_matching
#print axioms matching_edge_mem_originPrefix
#print axioms departure_eq_initial_of_prefix_noIncoming

end Erdos599.GroundingAllMarkerAuxiliary.Input.PortAugmentation
