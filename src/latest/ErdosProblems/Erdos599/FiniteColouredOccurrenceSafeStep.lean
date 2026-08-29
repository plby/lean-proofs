/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.InfiniteColouredOccurrenceWord
import ErdosProblems.Erdos599.FiniteColouredOccurrenceSwitch
import ErdosProblems.Erdos599.SafeSwitchingRelationalContactStep

/-!
# Constructive safe forward/backward occurrence-word extension

This is the local Rule-1/Rule-2 constructor. It appends an actual forward
fragment and an actual backward reference interval, constructs coloured-edge
freshness, and proves the new interval and contact certificates. Choosing
the next contact and its lower endpoint is still the global recursion's task.
-/

namespace Erdos599.Alternating.FiniteColouredOccurrenceWord

open Set DirectedPath SwitchingCore.RelationalInterval

universe u

variable {V : Type u} {Gamma : DWeb V} {W Y : Set Gamma.DPath}

theorem IsIntervalSafe.exists_forward_backward_extension
    {Q : FiniteColouredOccurrenceWord W Y} (hQ : Q.IsIntervalSafe)
    (hY : Gamma.IsWarp Y) (hYfin : Gamma.HasFiniteCharacter Y)
    (p : FinitePath Gamma.graph)
    (hjoin : Q.vertex (Fin.last Q.length) = p.start)
    (hp : p.edgeSet ⊆ familyEdges W)
    (hfresh : Disjoint p.edgeSet Q.forwardEdges)
    (hstart : p.start ∈ Gamma.vertexSet Y → HasOutgoing Q.backwardEdges p.start)
    (hcontact : p.support ∩ Gamma.vertexSet Y ⊆
      {p.start, p.finish} ∪ removedInterior Q.backwardEdges)
    (owner : Gamma.DPath) (howner : owner ∈ Y)
    (old r : FinitePath Gamma.graph)
    (hold : old.IsSubpathOf owner) (hr : r.IsSubpathOf owner)
    (holdjoin : old.finish = r.start)
    (holdR : Q.backwardEdges ∩ owner.edgeSet = old.edgeSet)
    (hrend : r.finish = p.finish) (hrne : r.start ≠ r.finish) :
    ∃ Q' : FiniteColouredOccurrenceWord W Y, Q'.IsIntervalSafe ∧
      Q'.vertex 0 = Q.vertex 0 ∧
      Q'.vertex (Fin.last Q'.length) = r.start ∧
      Q'.length = Q.length + p.walk.length + r.walk.length ∧
      Q'.vertexSet = Q.vertexSet ∪ p.support ∪ r.support ∧
      Q'.forwardEdges = Q.forwardEdges ∪ p.edgeSet ∧
      Q'.backwardEdges = Q.backwardEdges ∪ r.edgeSet ∧ Q.Prefix Q' := by
  have hrY : r.edgeSet ⊆ familyEdges Y := by
    intro e he
    simp only [familyEdges, Set.mem_iUnion]
    exact ⟨owner, howner, hr.2 he⟩
  obtain ⟨hrfresh, _hRsub, hintervals⟩ := backward_interval_extension hY
    Q.backwardEdges_subset_familyEdges hQ.intervals owner howner old r
    hold hr holdjoin holdR
  let QF := Q.appendForwardPath p hjoin hp hfresh
  have hQFback : QF.backwardEdges = Q.backwardEdges :=
    Q.appendForwardPath_backwardEdges p hjoin hp hfresh
  have hQFforward : QF.forwardEdges = Q.forwardEdges ∪ p.edgeSet :=
    Q.appendForwardPath_forwardEdges p hjoin hp hfresh
  have hRjoin : QF.vertex (Fin.last QF.length) = r.finish := by
    rw [show QF.vertex (Fin.last QF.length) = p.finish from
      Q.appendForwardPath_last p hjoin hp hfresh, hrend]
  have hRfresh : Disjoint r.edgeSet QF.backwardEdges := by
    rwa [hQFback]
  let Q' := QF.appendBackwardPath r hRjoin hrY hRfresh
  have hQ'forward : Q'.forwardEdges = Q.forwardEdges ∪ p.edgeSet := by
    rw [show Q'.forwardEdges = QF.forwardEdges from
      QF.appendBackwardPath_forwardEdges r hRjoin hrY hRfresh, hQFforward]
  have hQ'back : Q'.backwardEdges = Q.backwardEdges ∪ r.edgeSet := by
    rw [show Q'.backwardEdges = QF.backwardEdges ∪ r.edgeSet from
      QF.appendBackwardPath_backwardEdges r hRjoin hrY hRfresh, hQFback]
  have hfinish : HasIncoming r.edgeSet p.finish := by
    obtain ⟨x, hx⟩ := FinitePath.exists_edge_to_of_mem_of_ne_start r
      r.finish_mem_support hrne.symm
    exact ⟨x, hrend ▸ hx⟩
  have hnewInc := new_forward_conflicting_edges_removed hY
    Q.backwardEdges_subset_familyEdges hrY p hstart (fun _ ↦ hfinish) hcontact
  have hnewPure : ∀ {x y : V}, (x, y) ∈ p.edgeSet →
      y ∉ Gamma.initialSet Y ∧ x ∉ Gamma.terminalFrontier Y :=
    new_forward_endpoint_pure hY hYfin Q.backwardEdges_subset_familyEdges hrY
      p hstart (fun _ ↦ hfinish) hcontact
  have hsafe : Q'.IsIntervalSafe := by
    constructor
    · intro a b x hax hbx
      rw [hQ'forward] at hax
      rw [hQ'back]
      exact hax.elim (fun h ↦ Or.inl (hQ.incoming_removed h hbx))
        (fun h ↦ hnewInc.1 h hbx)
    · intro x a b hxa hxb
      rw [hQ'forward] at hxa
      rw [hQ'back]
      exact hxa.elim (fun h ↦ Or.inl (hQ.outgoing_removed h hxb))
        (fun h ↦ hnewInc.2 h hxb)
    · intro p hpY
      rw [hQ'back]
      exact hintervals p hpY
    · intro x y hxy
      rw [hQ'forward] at hxy
      exact hxy.elim (fun h ↦ hQ.endpoint_pure h) (fun h ↦ hnewPure h)
  refine ⟨Q', hsafe, ?_, ?_, ?_, ?_, hQ'forward, hQ'back, ?_⟩
  · dsimp only [Q']
    rw [appendBackwardPath_first]
    exact Q.appendForwardPath_first p hjoin hp hfresh
  · exact QF.appendBackwardPath_last r hRjoin hrY hRfresh
  · dsimp only [Q', QF]
    simp only [appendBackwardPath_length, appendForwardPath_length]
  · dsimp only [Q']
    rw [appendBackwardPath_vertexSet]
    dsimp only [QF]
    rw [appendForwardPath_vertexSet]
  · exact (Q.prefix_appendForwardPath p hjoin hp hfresh).trans
      (QF.prefix_appendBackwardPath r hRjoin hrY hRfresh)

#print axioms IsIntervalSafe.exists_forward_backward_extension

end Erdos599.Alternating.FiniteColouredOccurrenceWord
