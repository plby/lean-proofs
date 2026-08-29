/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.SplitGroundingGroundedFreshRelevantForwardComponentExchange

/-!
# Dynamic component exchange along a finite segment

The canonical grounding exchange was originally stated only for the fixed
source-reachable component warp.  A simultaneous augmenting chain must apply
the same operation to the warp produced by the preceding exchange.  This
file extracts the genuinely dynamic statement.

Starting at any vertex of a warp, retain the unique old component up to the
last point at which the proposed finite segment meets the current carrier,
then append the remaining segment.  The resulting family is again a warp,
has exactly the same initial set, and its terminal frontier is updated by
inserting the new endpoint and deleting exactly the old finite sink which
was traded.  If the old component is a ray, no sink is deleted.
-/

noncomputable section

open Set

namespace Erdos599
namespace GroundingDynamicComponentExchange

open DirectedPath Alternating

universe u

variable {V : Type u} {Gamma : DWeb V}

/-- One exact exchange step on an arbitrary current warp.  This is the
iterable form of the last-carrier-contact construction: unlike the canonical
specialization, the input warp and its current terminal frontier are explicit
and the output can be fed into the next step of the augmenting chain. -/
theorem exists_exchangeWarp_of_segment_with_terminalUpdate
    (W : Set Gamma.DPath) (hW : Gamma.IsWarp W)
    (segment : FinitePath Gamma.graph)
    (hstart : segment.start ∈ Gamma.vertexSet W) :
    ∃ (W' : Set Gamma.DPath) (q : FinitePath Gamma.graph),
      Gamma.IsWarp W' ∧
        Gamma.initialSet W' = Gamma.initialSet W ∧
        (Sum.inl q : Gamma.DPath) ∈ W' ∧
        q.start ∈ Gamma.initialSet W ∧
        q.finish = segment.finish ∧
        q.edgeSet ⊆ familyEdges W ∪ segment.edgeSet ∧
        segment.finish ∈ Gamma.terminalFrontier W' ∧
        ((∃ (old : FinitePath Gamma.graph) (contact : V),
            (Sum.inl old : Gamma.DPath) ∈ W ∧
            contact ∈ old.support ∧ contact ∈ segment.support ∧
            old.start ∈ Gamma.initialSet W ∧
            old.finish ∈ Gamma.terminalFrontier W ∧
            Gamma.terminalFrontier W' = insert segment.finish
              (Gamma.terminalFrontier W \ {old.finish})) ∨
          Gamma.terminalFrontier W' =
            insert segment.finish (Gamma.terminalFrontier W)) := by
  let hmeet : segment.walk.Meets (Gamma.vertexSet W) :=
    ⟨segment.start, segment.start_mem_support, hstart⟩
  let tail := segment.lastHit (Gamma.vertexSet W) hmeet
  have htailStartW : tail.start ∈ Gamma.vertexSet W :=
    segment.lastHit_start_mem (Gamma.vertexSet W) hmeet
  obtain ⟨p, hpW, hpTail⟩ := htailStartW
  obtain ⟨front, hfrontStart, hfrontFinish, hfrontSupport, hfrontEdges⟩ :=
    GroundingPathPrefix.exists_initialFinitePrefix p hpTail
  have hinter : front.support ∩ tail.support ⊆ {front.finish} := by
    intro z hz
    by_cases hzeq : z = tail.start
    · exact Set.mem_singleton_iff.mpr (hzeq.trans hfrontFinish.symm)
    · have hsupport : tail.walk.support =
          tail.start :: tail.walk.support.tail := by
        have h := (List.cons_head_tail tail.walk.support_ne_nil).symm
        simpa only [tail.walk.head_support] using h
      have hzTail : z ∈ tail.walk.support.tail := by
        have hzSupport : z ∈ tail.walk.support := hz.2
        rw [hsupport] at hzSupport
        rcases List.mem_cons.mp hzSupport with hzStart | hzTail
        · exact False.elim (hzeq hzStart)
        · exact hzTail
      have hzNotW : z ∉ Gamma.vertexSet W :=
        segment.lastHit_no_mem_after (Gamma.vertexSet W) hmeet hzTail
      exact False.elim (hzNotW ⟨p, hpW, hfrontSupport hz.1⟩)
  let q := front.appendFinite tail hfrontFinish.symm hinter
  let W' : Set Gamma.DPath := insert (.inl q : Gamma.DPath) (W \ {p})
  have hqDisjoint : Disjoint q.support (Gamma.vertexSet (W \ {p})) := by
    rw [Set.disjoint_left]
    intro z hzq hzRest
    rw [show q.support = front.support ∪ tail.support by
      exact front.support_appendFinite_eq_union tail hfrontFinish.symm hinter]
      at hzq
    obtain ⟨r, hrRest, hzR⟩ := hzRest
    rcases hzq with hzFront | hzTail
    · have hne : p ≠ r := by
        intro hpr
        subst r
        exact hrRest.2 (Set.mem_singleton p)
      exact Set.disjoint_left.mp (hW hpW hrRest.1 hne)
        (hfrontSupport hzFront) hzR
    · by_cases hzeq : z = tail.start
      · exact Set.disjoint_left.mp (hW hpW hrRest.1 (by
          intro hpr
          subst r
          exact hrRest.2 (Set.mem_singleton p)))
          (hzeq ▸ hpTail) hzR
      · have hsupport : tail.walk.support =
            tail.start :: tail.walk.support.tail := by
          have h := (List.cons_head_tail tail.walk.support_ne_nil).symm
          simpa only [tail.walk.head_support] using h
        have hzAfter : z ∈ tail.walk.support.tail := by
          have hzSupport : z ∈ tail.walk.support := hzTail
          rw [hsupport] at hzSupport
          rcases List.mem_cons.mp hzSupport with hzStart | hzAfter
          · exact False.elim (hzeq hzStart)
          · exact hzAfter
        exact (segment.lastHit_no_mem_after
          (Gamma.vertexSet W) hmeet hzAfter) ⟨r, hrRest.1, hzR⟩
  have hW' : Gamma.IsWarp W' :=
    DWeb.IsWarp.insert_finite_of_disjoint Gamma
      (DWeb.IsWarp.sdiff_singleton Gamma hW p) q hqDisjoint
  have hpInitial : p.initial ∈ Gamma.initialSet W := ⟨p, hpW, rfl⟩
  have hqStart : q.start = p.initial := by
    simpa only [q, FinitePath.appendFinite_start, hfrontStart]
  have hqFinish : q.finish = segment.finish := by
    have htailFinish : tail.finish = segment.finish := rfl
    simpa only [q, FinitePath.appendFinite_finish, htailFinish]
  have hqEdges : q.edgeSet ⊆ familyEdges W ∪ segment.edgeSet := by
    rw [show q.edgeSet = front.edgeSet ∪ tail.edgeSet by
      exact Blueprint.LinkageBlueprint.FinitePath.edgeSet_appendFinite
        front tail hfrontFinish.symm hinter]
    intro e he
    rcases he with heFront | heTail
    · left
      exact Set.mem_iUnion.2 ⟨p, Set.mem_iUnion.2
        ⟨hpW, hfrontEdges heFront⟩⟩
    · right
      exact segment.lastHit_edgeSet_subset
        (Gamma.vertexSet W) hmeet heTail
  have hW'Initial : Gamma.initialSet W' = Gamma.initialSet W := by
    change Gamma.initialSet (insert (.inl q : Gamma.DPath) (W \ {p})) = _
    rw [Gamma.initialSet_insert_finite,
      DWeb.IsWarp.initialSet_sdiff_singleton Gamma hW hpW, hqStart]
    ext x
    simp only [Set.mem_insert_iff, Set.mem_diff, Set.mem_singleton_iff]
    constructor
    · rintro (rfl | hx)
      · exact hpInitial
      · exact hx.1
    · intro hx
      by_cases hxp : x = p.initial
      · exact Or.inl hxp
      · exact Or.inr ⟨hx, hxp⟩
  have hterminalUpdate :
      ((∃ (old : FinitePath Gamma.graph) (contact : V),
          (Sum.inl old : Gamma.DPath) ∈ W ∧
          contact ∈ old.support ∧ contact ∈ segment.support ∧
          old.start ∈ Gamma.initialSet W ∧
          old.finish ∈ Gamma.terminalFrontier W ∧
          Gamma.terminalFrontier W' = insert segment.finish
            (Gamma.terminalFrontier W \ {old.finish})) ∨
        Gamma.terminalFrontier W' =
          insert segment.finish (Gamma.terminalFrontier W)) := by
    cases p with
    | inl old =>
        left
        refine ⟨old, tail.start, hpW, hpTail, ?_, ?_, ?_, ?_⟩
        · exact segment.lastHit_support_subset
            (Gamma.vertexSet W) hmeet tail.start_mem_support
        · exact ⟨.inl old, hpW, rfl⟩
        · exact ⟨.inl old, hpW, rfl⟩
        · change Gamma.terminalFrontier
            (insert (.inl q : Gamma.DPath) (W \ {Sum.inl old})) = _
          rw [Gamma.terminalFrontier_insert_finite,
            DWeb.IsWarp.terminalFrontier_sdiff_singleton Gamma hW hpW rfl]
          simpa only [hqFinish]
    | inr ray =>
        right
        have hremove : Gamma.terminalFrontier (W \ {Sum.inr ray}) =
            Gamma.terminalFrontier W := by
          ext x
          constructor
          · rintro ⟨r, hr, hrx⟩
            exact ⟨r, hr.1, hrx⟩
          · rintro ⟨r, hr, hrx⟩
            refine ⟨r, ⟨hr, ?_⟩, hrx⟩
            intro hre
            have hre' : r = Sum.inr ray := Set.mem_singleton_iff.mp hre
            subst r
            cases hrx
        change Gamma.terminalFrontier
            (insert (.inl q : Gamma.DPath) (W \ {Sum.inr ray})) = _
        rw [Gamma.terminalFrontier_insert_finite, hremove]
        simpa only [hqFinish]
  refine ⟨W', q, hW', hW'Initial, Set.mem_insert _ _, ?_, hqFinish,
    hqEdges, ?_, hterminalUpdate⟩
  · simpa only [hqStart] using hpInitial
  · exact ⟨.inl q, Set.mem_insert _ _, congrArg some hqFinish⟩

end GroundingDynamicComponentExchange
end Erdos599

#print axioms
  Erdos599.GroundingDynamicComponentExchange.exists_exchangeWarp_of_segment_with_terminalUpdate
