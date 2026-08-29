/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.ColouredSafeReverseReachability
import ErdosProblems.Erdos599.FiniteColouredOccurrenceTerminalStep

/-!
# Actual first-contact selection for the safe occurrence recursion

A contact-free terminal suffix gives a safe outward word and a literal
reverse residual continuation. Thus a current vertex outside the reverse
reachable set cannot have such a suffix. The first later reference contact
is selected from a finite path, and all its forward edges are proved fresh.
-/

namespace Erdos599.ColouredSafeReverseReachability

open Set DirectedPath Alternating
open Alternating.SwitchingCore.RelationalInterval
open ColouredResidualPortContinuation

universe u

variable {V : Type u} {Gamma : DWeb V} {W Y : Set Gamma.DPath}

/-- An old initial cannot occur strictly after the start of a forward
fragment in its warp. -/
theorem forward_fragment_avoids_initial
    (hW : Gamma.IsWarp W) (hWfin : Gamma.HasFiniteCharacter W)
    {s : V} (hs : s ∈ Gamma.initialSet W)
    (p : FinitePath Gamma.graph) (hp : p.edgeSet ⊆ familyEdges W)
    (hne : s ≠ p.start) : s ∉ p.support := by
  intro hsp
  rw [initialSet_eq_vertexSet_diff_hasIncoming hW hWfin] at hs
  obtain ⟨a, ha⟩ := FinitePath.exists_edge_to_of_mem_of_ne_start p hsp hne
  exact hs.2 ⟨a, hp ha⟩

/-- The zero-length initial-terminal case is itself reverse reachable;
the completed matching uses its isolated diagonal. -/
theorem initial_mem_reverseReachable_of_terminal
    (hW : Gamma.IsWarp W) (hWfin : Gamma.HasFiniteCharacter W)
    {s : V} (hs : s ∈ Gamma.initialSet W)
    (ht : s ∈ Gamma.terminalFrontier W) (hsY : s ∉ Gamma.vertexSet Y) :
    s ∈ reverseReachable W Y s := by
  have hsSR : s ∈ safelyReachable W Y s :=
    ⟨⟨ht, hsY⟩, FiniteColouredOccurrenceWord.emptyAt s,
      FiniteColouredOccurrenceWord.emptyAt_isIntervalSafe s, rfl, rfl⟩
  have hsin := hs
  have hsout := ht
  rw [initialSet_eq_vertexSet_diff_hasIncoming hW hWfin] at hsin
  rw [terminalFrontier_eq_vertexSet_diff_hasOutgoing hW hWfin] at hsout
  have hno : s ∉ TwoWarpMatchingTraversal.edgeCarrier W := by
    rintro (h | h)
    · exact hsout.2 h
    · exact hsin.2 h
  refine ⟨s, hsSR, Relation.ReflTransGen.single ?_⟩
  change completedReferenceMatching W s s
  exact Or.inr ⟨rfl, hno, Set.notMem_empty _, Set.notMem_empty _⟩

/-- A fresh contact-free terminal suffix constructs an actual member of
the reverse reachable set. This is not an assumed continuation predicate. -/
theorem mem_reverseReachable_of_contact_free_tail
    (hY : Gamma.IsWarp Y) (hYfin : Gamma.HasFiniteCharacter Y)
    (hpure : Gamma.terminalFrontier W ∩ Gamma.vertexSet Y ⊆
      Gamma.terminalFrontier Y)
    (Q : FiniteColouredOccurrenceWord W Y) (hQ : Q.IsIntervalSafe)
    (p : FinitePath Gamma.graph)
    (hjoin : Q.vertex (Fin.last Q.length) = p.start)
    (hp : p.edgeSet ⊆ familyEdges W) (hne : p.start ≠ p.finish)
    (hfresh : Disjoint p.edgeSet Q.forwardEdges)
    (ht : p.finish ∈ Gamma.terminalFrontier W)
    (hstart : p.start ∈ Gamma.vertexSet Y → HasOutgoing Q.backwardEdges p.start)
    (hno : p.support ∩ (Gamma.vertexSet Y \ removedInterior Q.backwardEdges) ⊆
      {p.start}) : p.start ∈ reverseReachable W Y (Q.vertex 0) := by
  have htOff : p.finish ∉ Gamma.vertexSet Y := by
    apply terminal_outside_reference_of_no_new_contact hY hYfin
      Q.backwardEdges_subset_familyEdges hpure ht
    intro hm
    exact hne (Set.mem_singleton_iff.mp (hno ⟨p.finish_mem_support, hm⟩)).symm
  have hcontact : p.support ∩ Gamma.vertexSet Y ⊆
      {p.start, p.finish} ∪ removedInterior Q.backwardEdges := by
    rintro x ⟨hxp, hxY⟩
    by_cases hxR : x ∈ removedInterior Q.backwardEdges
    · exact Or.inr hxR
    · exact Or.inl (Set.mem_insert_iff.mpr
        (Or.inl (Set.mem_singleton_iff.mp (hno ⟨hxp, hxY, hxR⟩))))
  let Q' := Q.appendForwardPath p hjoin hp hfresh
  have hQ' : Q'.IsIntervalSafe :=
    hQ.appendForwardPath_of_terminal_offReference hY hYfin p
      hjoin hp hfresh htOff hstart hcontact
  refine ⟨p.finish, ⟨⟨ht, htOff⟩, Q', hQ', ?_, ?_⟩, ?_⟩
  · exact Q.appendForwardPath_first p hjoin hp hfresh
  · exact Q.appendForwardPath_last p hjoin hp hfresh
  · exact finiteReferencePath_receiver_finish_reaches_start_of_edges p hp hne

/-- Choose the actual first later reference contact. The terminal suffix
cannot be contact-free, because that would put its start in the reverse
reachable set. The output includes literal forward freshness and absence
of an old incoming forward edge at the contact, needed by Rule 2. -/
theorem exists_first_forward_contact
    (hW : Gamma.IsWarp W) (hY : Gamma.IsWarp Y)
    (hYfin : Gamma.HasFiniteCharacter Y)
    (hpure : Gamma.terminalFrontier W ∩ Gamma.vertexSet Y ⊆
      Gamma.terminalFrontier Y)
    (Q : FiniteColouredOccurrenceWord W Y) (hQ : Q.IsIntervalSafe)
    (p : FinitePath Gamma.graph)
    (hjoin : Q.vertex (Fin.last Q.length) = p.start)
    (hp : p.edgeSet ⊆ familyEdges W) (hne : p.start ≠ p.finish)
    (ht : p.finish ∈ Gamma.terminalFrontier W)
    (hstart : p.start ∈ Gamma.vertexSet Y → HasOutgoing Q.backwardEdges p.start)
    (hstartF : ¬HasOutgoing Q.forwardEdges p.start)
    (hsource : Q.forwardEdges = ∅ ∨ Q.vertex 0 ∉ p.support)
    (hnotC : p.start ∉ reverseReachable W Y (Q.vertex 0)) :
    ∃ f : FinitePath Gamma.graph,
      f.IsSubpathOf (.inl p) ∧ f.start = p.start ∧ f.start ≠ f.finish ∧
      f.finish ∈ Gamma.vertexSet Y \ removedInterior Q.backwardEdges ∧
      f.edgeSet ⊆ familyEdges W ∧ Disjoint f.edgeSet Q.forwardEdges ∧
      (f.support ∩ (Gamma.vertexSet Y \ removedInterior Q.backwardEdges) ⊆
        {f.start, f.finish}) ∧
      ¬HasIncoming Q.forwardEdges f.finish := by
  classical
  let T := (Gamma.vertexSet Y \ removedInterior Q.backwardEdges) \ {p.start}
  have hbalance (x : V) :
      edgeBalance Q.forwardEdges x - edgeBalance Q.backwardEdges x =
        propInt (x = Q.vertex 0) - propInt (x = p.start) := by
    simpa only [hjoin] using Q.edgeBalance_forward_sub_backward hW hY x
  have hfresh_of_first (f : FinitePath Gamma.graph)
      (hfsub : f.IsSubpathOf (.inl p)) (hfstart : f.start = p.start)
      (hfirst : f.support ∩ (Gamma.vertexSet Y \ removedInterior Q.backwardEdges) ⊆
        {f.start, f.finish}) : Disjoint f.edgeSet Q.forwardEdges := by
    rcases hsource with hzero | hsource
    · simp [hzero]
    · apply firstReferenceContact_forward_edges_fresh hW Q.forwardEdges_subset_familyEdges
        Q.backwardEdges_subset_familyEdges f (hfsub.2.trans hp)
        (hfstart ▸ hstartF) (fun h ↦ hsource (hfsub.1 h))
      · intro x
        simpa only [hfstart] using hbalance x
      · exact hfirst
  have hmeet : p.walk.Meets T := by
    by_contra hnoMeet
    have hno : p.support ∩ (Gamma.vertexSet Y \ removedInterior Q.backwardEdges) ⊆
        {p.start} := by
      rintro x ⟨hxp, hxT⟩
      by_contra hx
      exact hnoMeet ⟨x, hxp, hxT, hx⟩
    have hfirst : p.support ∩ (Gamma.vertexSet Y \ removedInterior Q.backwardEdges) ⊆
        {p.start, p.finish} := by
      intro x hx
      exact Set.mem_insert_iff.mpr (Or.inl (Set.mem_singleton_iff.mp (hno hx)))
    have hfresh := hfresh_of_first p ⟨Set.Subset.rfl, Set.Subset.rfl⟩ rfl hfirst
    exact hnotC (mem_reverseReachable_of_contact_free_tail hY hYfin hpure
      Q hQ p hjoin hp hne hfresh ht hstart hno)
  let f := p.firstHit T hmeet
  have hfstart : f.start = p.start := rfl
  have hfinishT : f.finish ∈ T := p.firstHit_finish_mem T hmeet
  have hfne : f.start ≠ f.finish := by
    intro heq
    exact hfinishT.2 (Set.mem_singleton_iff.mpr (heq.symm.trans hfstart))
  have hfsub : f.IsSubpathOf (.inl p) := p.firstHit_isSubpathOf T hmeet
  have hfirst : f.support ∩ (Gamma.vertexSet Y \ removedInterior Q.backwardEdges) ⊆
      {f.start, f.finish} := by
    rintro x ⟨hxf, hxT⟩
    by_cases hxs : x = f.start
    · exact Set.mem_insert_iff.mpr (Or.inl hxs)
    · have hxf' : x = f.finish := by
        by_contra hnefinish
        have hlast : x ≠ f.walk.support.getLast f.walk.support_ne_nil := by
          simpa only [f.walk.getLast_support] using hnefinish
        exact p.firstHit_no_mem_before T hmeet
          (List.mem_dropLast_of_mem_of_ne_getLast hxf hlast)
          ⟨hxT, fun h ↦ hxs (by simpa only [Set.mem_singleton_iff, hfstart] using h)⟩
      exact Set.mem_insert_of_mem _ (Set.mem_singleton_iff.mpr hxf')
  refine ⟨f, hfsub, hfstart, hfne, hfinishT.1, hfsub.2.trans hp,
    hfresh_of_first f hfsub hfstart hfirst, hfirst, ?_⟩
  rcases hsource with hzero | hsource
  · simp [hzero, HasIncoming]
  · apply firstReferenceContact_has_no_old_forward_incoming_of_balance hW
      Q.forwardEdges_subset_familyEdges Q.backwardEdges_subset_familyEdges
      f hfne (hfsub.2.trans hp) (hfstart ▸ hstartF)
      (fun h ↦ hsource (hfsub.1 h))
    · intro x
      simpa only [hfstart] using hbalance x
    · exact hfirst

/-- A reference-family edge whose head is outside the forward carrier
continues reverse reachability through the completed matching diagonal. -/
theorem reverseReachable_forward_of_head_outside
    {s a b : V} (hb : b ∈ reverseReachable W Y s)
    (hba : (b, a) ∈ familyEdges Y) (haW : a ∉ Gamma.vertexSet W) :
    a ∈ reverseReachable W Y s := by
  obtain ⟨t, ht, hreach⟩ := hb
  have hnoMatch : ¬completedReferenceMatching W b a := by
    rintro (he | he)
    · exact haW (familyEdges_subset_vertexSet_prod W he).2
    · exact not_self_mem_familyEdges Y a (he.1 ▸ hba)
  have hnoCarrier : a ∉ TwoWarpMatchingTraversal.edgeCarrier W := by
    rintro (⟨x, hx⟩ | ⟨x, hx⟩)
    · exact haW (familyEdges_subset_vertexSet_prod W hx).1
    · exact haW (familyEdges_subset_vertexSet_prod W hx).2
  have hdiag : ResidualStep W Y (.inr a) (.inl a) :=
    Or.inr ⟨rfl, hnoCarrier, Set.notMem_empty _, Set.notMem_empty _⟩
  exact ⟨t, ht, hreach.trans
    ((Relation.ReflTransGen.single
      (residualStep_forward_of_not_reference hba hnoMatch)).trans
        (Relation.ReflTransGen.single hdiag))⟩

/-- The immediate-predecessor occurrence also supplies the literal owner
edge, not merely ambient adjacency. -/
theorem exists_predecessor_occurrence_edge
    (owner : FinitePath Gamma.graph) {a : V}
    (ha : a ∈ owner.support) (hne : a ≠ owner.start) :
    ∃ b, Nonempty (FinitePath.OrderedOccurrence owner b a) ∧
      (b, a) ∈ owner.edgeSet := by
  obtain ⟨b, hocc, _hmid, hpair, _hadj⟩ :=
    owner.exists_predecessor_orderedOccurrence ha hne
  let q := owner.between hocc
  have hqstart : q.start = b := owner.between_start hocc
  have hqfinish : q.finish = a := owner.between_finish hocc
  have hqa : a ∈ q.support := hqfinish ▸ q.finish_mem_support
  have hqan : a ≠ q.start := by simpa only [hqstart] using hocc.ne.symm
  obtain ⟨x, hxa⟩ := FinitePath.exists_edge_to_of_mem_of_ne_start q hqa hqan
  have hxq : x ∈ q.walk.support := (q.edgeSet_subset_support_prod hxa).1
  have hxb : x = b := by
    have hx : x = b ∨ x = a := by simpa only [q, hpair, List.mem_cons,
      List.not_mem_nil, or_false] using hxq
    exact hx.resolve_right (fun h ↦
      FinitePath.no_outgoing_edge_at_finish q a (by simpa only [h, hqfinish] using hxa))
  have hba : (b, a) ∈ q.edgeSet := by simpa only [hxb] using hxa
  exact ⟨b, ⟨hocc⟩, owner.between_edgeSet_subset hocc hba⟩

/-- The first vertex outside the reverse reachable set on a reference
owner lies in the forward warp. This removes the need to assume reference
carrier containment or to suppress reference-only vertices. -/
theorem earliest_reference_exit_mem_forward
    (hsource : Gamma.initialSet Y ⊆ Gamma.initialSet W)
    {s : V} (owner : FinitePath Gamma.graph)
    (howner : (Sum.inl owner : Gamma.DPath) ∈ Y) {a : V}
    (ha : a ∈ owner.support)
    (haC : a ∉ reverseReachable W Y s)
    (hearlier : ∀ {b : V}, b ∈ owner.support →
      Nonempty (FinitePath.OrderedOccurrence owner b a) →
        b ∈ reverseReachable W Y s) : a ∈ Gamma.vertexSet W := by
  by_contra haW
  have han : a ≠ owner.start := by
    intro heq
    have hstartY : owner.start ∈ Gamma.initialSet Y := ⟨.inl owner, howner, rfl⟩
    obtain ⟨p, hpW, hpstart⟩ := hsource hstartY
    exact haW ⟨p, hpW, by simpa only [hpstart, ← heq] using p.initial_mem_support⟩
  obtain ⟨b, hbaOrder, hba⟩ := exists_predecessor_occurrence_edge owner ha han
  have hbC := hearlier (owner.edgeSet_subset_support_prod hba).1 hbaOrder
  have hbaY : (b, a) ∈ familyEdges Y := by
    simp only [familyEdges, Set.mem_iUnion]
    exact ⟨.inl owner, howner, hba⟩
  exact haC (reverseReachable_forward_of_head_outside hbC hbaY haW)

#print axioms reverseReachable_forward_of_head_outside
#print axioms earliest_reference_exit_mem_forward
#print axioms forward_fragment_avoids_initial
#print axioms initial_mem_reverseReachable_of_terminal
#print axioms mem_reverseReachable_of_contact_free_tail
#print axioms exists_first_forward_contact

end Erdos599.ColouredSafeReverseReachability
