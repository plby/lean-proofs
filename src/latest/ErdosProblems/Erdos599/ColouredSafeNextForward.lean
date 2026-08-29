/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.ColouredSafeForwardContact

/-!
# Producing the next forward fragment and its reference predecessor

This is an existence construction from a ready finite prefix, not a next-step
oracle. Finite character supplies the current owner's terminal suffix;
balance supplies an unused forward incidence; first-contact selection and
the residual continuation lemmas supply the new contact and predecessor.
-/

namespace Erdos599.ColouredSafeReverseReachability

open Set DirectedPath Alternating
open Alternating.SwitchingCore.RelationalInterval

universe u

variable {V : Type u} {Gamma : DWeb V} {W Y : Set Gamma.DPath}

structure NextForwardContact (Q : FiniteColouredOccurrenceWord W Y) where
  path : FinitePath Gamma.graph
  join : Q.vertex (Fin.last Q.length) = path.start
  nontrivial : path.start ≠ path.finish
  edges : path.edgeSet ⊆ familyEdges W
  fresh : Disjoint path.edgeSet Q.forwardEdges
  first_contact : path.support ∩
      (Gamma.vertexSet Y \ removedInterior Q.backwardEdges) ⊆
    {path.start, path.finish}
  finish_not_interior : path.finish ∉ removedInterior Q.backwardEdges
  incoming_unused : ¬HasIncoming Q.forwardEdges path.finish
  finish_outside : path.finish ∉ reverseReachable W Y (Q.vertex 0)
  owner : FinitePath Gamma.graph
  owner_mem : (Sum.inl owner : Gamma.DPath) ∈ Y
  finish_mem : path.finish ∈ owner.support
  predecessor : V
  predecessor_edge : (predecessor, path.finish) ∈ owner.edgeSet
  predecessor_outside : predecessor ∉ reverseReachable W Y (Q.vertex 0)

theorem NextForwardContact.contact_geometry
    {Q : FiniteColouredOccurrenceWord W Y} (K : NextForwardContact Q) :
    K.path.support ∩ Gamma.vertexSet Y ⊆
      {K.path.start, K.path.finish} ∪ removedInterior Q.backwardEdges := by
  rintro x ⟨hxp, hxY⟩
  by_cases hxR : x ∈ removedInterior Q.backwardEdges
  · exact Or.inr hxR
  · exact Or.inl (K.first_contact ⟨hxp, hxY, hxR⟩)

/-- A ready prefix is either the initial empty-forward word or ends after
a genuine backward transition. No continuation data is assumed. -/
theorem exists_nextForwardContact
    (hW : Gamma.IsWarp W) (hY : Gamma.IsWarp Y)
    (hWfin : Gamma.HasFiniteCharacter W) (hYfin : Gamma.HasFiniteCharacter Y)
    (hsource : Gamma.initialSet Y ⊆ Gamma.initialSet W)
    (hterminal : Gamma.terminalFrontier W ∩ Gamma.vertexSet Y ⊆
      Gamma.terminalFrontier Y)
    (Q : FiniteColouredOccurrenceWord W Y) (hQ : Q.IsIntervalSafe)
    (hfirst : Q.vertex 0 ∈ Gamma.initialSet W)
    (hfirstOff : Q.vertex 0 ∉ Gamma.vertexSet Y)
    (hcurrent : Q.vertex (Fin.last Q.length) ∈ Gamma.vertexSet W)
    (hphase : (Q.forwardEdges = ∅ ∧ Q.vertex (Fin.last Q.length) = Q.vertex 0) ∨
      HasOutgoing Q.backwardEdges (Q.vertex (Fin.last Q.length)))
    (hnotC : Q.vertex (Fin.last Q.length) ∉ reverseReachable W Y (Q.vertex 0)) :
    Nonempty (NextForwardContact Q) := by
  classical
  let a := Q.vertex (Fin.last Q.length)
  have haNotTerm : a ∉ Gamma.terminalFrontier W := by
    intro hat
    rcases hphase with ⟨_, haFirst⟩ | hback
    · have hfirstTerm : Q.vertex 0 ∈ Gamma.terminalFrontier W := by
        simpa only [a, haFirst] using hat
      have hsC := initial_mem_reverseReachable_of_terminal hW hWfin
        hfirst hfirstTerm hfirstOff
      apply hnotC
      simpa only [haFirst] using hsC
    · obtain ⟨b, hab⟩ := hback
      have haY : a ∈ Gamma.vertexSet Y :=
        (familyEdges_subset_vertexSet_prod Y (Q.backwardEdges_subset_familyEdges hab)).1
      have haTermY := hterminal ⟨hat, haY⟩
      rw [terminalFrontier_eq_vertexSet_diff_hasOutgoing hY hYfin] at haTermY
      exact haTermY.2 ⟨b, Q.backwardEdges_subset_familyEdges hab⟩
  obtain ⟨owner, hownerW, haOwner⟩ := hcurrent
  obtain ⟨p, rfl⟩ := hWfin hownerW
  let tail := p.suffixFrom a haOwner
  have htailStart : tail.start = a := p.suffixFrom_start a haOwner
  have htailFinish : tail.finish = p.finish := p.suffixFrom_finish a haOwner
  have htailEdges : tail.edgeSet ⊆ familyEdges W := by
    intro e he
    simp only [familyEdges, Set.mem_iUnion]
    exact ⟨.inl p, hownerW, p.suffixFrom_edgeSet_subset a haOwner he⟩
  have htailTerminal : tail.finish ∈ Gamma.terminalFrontier W :=
    ⟨.inl p, hownerW, by simp only [DWeb.terminal?_finite, htailFinish]⟩
  have htailNe : tail.start ≠ tail.finish := by
    intro heq
    exact haNotTerm (htailStart ▸ (heq ▸ htailTerminal))
  have hstart : tail.start ∈ Gamma.vertexSet Y →
      HasOutgoing Q.backwardEdges tail.start := by
    intro haY
    rw [htailStart]
    rcases hphase with ⟨_, haFirst⟩ | hback
    · have haY' : a ∈ Gamma.vertexSet Y := by
        simpa only [htailStart] using haY
      exact (hfirstOff (by simpa only [a, haFirst] using haY')).elim
    · exact hback
  have hstartF : ¬HasOutgoing Q.forwardEdges tail.start := by
    rw [htailStart]
    rcases hphase with ⟨hzero, _⟩ | hback
    · simp [hzero, HasOutgoing]
    · exact hQ.no_forward_outgoing_at_backward_exit hW hY hYfin hfirstOff hback
  have hsourceTail : Q.forwardEdges = ∅ ∨ Q.vertex 0 ∉ tail.support := by
    rcases hphase with ⟨hzero, _⟩ | hback
    · exact Or.inl hzero
    · right
      apply forward_fragment_avoids_initial hW hWfin hfirst tail htailEdges
      intro heq
      obtain ⟨b, hab⟩ := hback
      have haY := (familyEdges_subset_vertexSet_prod Y
        (Q.backwardEdges_subset_familyEdges hab)).1
      exact hfirstOff (heq.symm ▸ (htailStart.symm ▸ haY))
  have htailJoin : Q.vertex (Fin.last Q.length) = tail.start := htailStart.symm
  obtain ⟨f, _hfsub, hfstart, hfne, hfY, hfEdges, hffresh, hfirstContact, hfUnused⟩ :=
    exists_first_forward_contact hW hY hYfin hterminal Q hQ tail htailJoin
      htailEdges htailNe htailTerminal hstart hstartF hsourceTail
      (htailStart ▸ hnotC)
  have hfJoin : Q.vertex (Fin.last Q.length) = f.start :=
    htailJoin.trans hfstart.symm
  have hfOutside : f.finish ∉ reverseReachable W Y (Q.vertex 0) :=
    finish_not_reverseReachable_of_start_not f hfEdges (hfJoin ▸ hnotC)
  obtain ⟨Yowner, hYowner, hfinishOwner⟩ := hfY.1
  obtain ⟨L, rfl⟩ := hYfin hYowner
  have hfinishNe : f.finish ≠ L.start := by
    intro heq
    have hLstart : L.start ∈ Gamma.initialSet Y := ⟨.inl L, hYowner, rfl⟩
    have hfInitial := hsource (heq ▸ hLstart)
    rw [initialSet_eq_vertexSet_diff_hasIncoming hW hWfin] at hfInitial
    obtain ⟨b, hb⟩ := FinitePath.exists_edge_to_of_mem_of_ne_start f
      f.finish_mem_support hfne.symm
    exact hfInitial.2 ⟨b, hfEdges hb⟩
  obtain ⟨y, _hyOrder, hyEdge⟩ :=
    exists_predecessor_occurrence_edge L hfinishOwner hfinishNe
  have hyY : (y, f.finish) ∈ familyEdges Y := by
    simp only [familyEdges, Set.mem_iUnion]
    exact ⟨.inl L, hYowner, hyEdge⟩
  have hyOutside : y ∉ reverseReachable W Y (Q.vertex 0) :=
    reference_predecessor_not_reverseReachable hW f hfEdges hfne hyY (hfJoin ▸ hnotC)
  exact ⟨⟨f, hfJoin, hfne, hfEdges, hffresh, hfirstContact, hfY.2,
    hfUnused, hfOutside, L, hYowner, hfinishOwner, y, hyEdge, hyOutside⟩⟩

#print axioms exists_nextForwardContact

end Erdos599.ColouredSafeReverseReachability
