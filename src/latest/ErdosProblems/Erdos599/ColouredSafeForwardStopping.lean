/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.ColouredSafeFiniteAuxiliaryRemoval

/-!
# Safe stops along a forward continuation

A fresh forward fragment may be stopped at any off-reference point before
its reference contact. This is an actual safe word, not an assertion that
arbitrary chronological prefixes preserve interval safeness.
-/

namespace Erdos599.Alternating.ColouredSafeForwardStopping

open Set DirectedPath FiniteColouredOccurrenceWord
open SwitchingCore.RelationalInterval

universe u

variable {V : Type u} {Gamma : DWeb V} {W Y : Set Gamma.DPath}

theorem exists_safeWord_to_offReference_forwardPoint
    (hY : Gamma.IsWarp Y) (hYfin : Gamma.HasFiniteCharacter Y)
    (Q : FiniteColouredOccurrenceWord W Y) (hQ : Q.IsIntervalSafe)
    (p : FinitePath Gamma.graph)
    (hjoin : Q.vertex (Fin.last Q.length) = p.start)
    (hp : p.edgeSet ⊆ familyEdges W) (hfresh : Disjoint p.edgeSet Q.forwardEdges)
    (hfinish : p.finish ∈ Gamma.vertexSet Y)
    (hstart : p.start ∈ Gamma.vertexSet Y → HasOutgoing Q.backwardEdges p.start)
    (hcontact : p.support ∩ Gamma.vertexSet Y ⊆
      {p.start, p.finish} ∪ removedInterior Q.backwardEdges)
    {x : V} (hxp : x ∈ p.support) (hxOff : x ∉ Gamma.vertexSet Y) :
    ∃ P : FiniteColouredOccurrenceWord W Y, P.IsIntervalSafe ∧
      P.vertex 0 = Q.vertex 0 ∧ P.vertex (Fin.last P.length) = x ∧
      P.forwardEdges ⊆ Q.forwardEdges ∪ p.edgeSet := by
  classical
  have hmeet : p.walk.Meets {x} := ⟨x, hxp, Set.mem_singleton _⟩
  let q := p.firstHit {x} hmeet
  have hqstart : q.start = p.start := rfl
  have hqfinish : q.finish = x := Set.mem_singleton_iff.mp (p.firstHit_finish_mem {x} hmeet)
  have hqE : q.edgeSet ⊆ p.edgeSet := p.firstHit_edgeSet_subset {x} hmeet
  have hqV : q.support ⊆ p.support := p.firstHit_support_subset {x} hmeet
  have hnotFinish : p.finish ∉ q.support := by
    intro hmem
    have hne : p.finish ≠ q.finish := by
      intro heq
      exact hxOff ((heq.trans hqfinish) ▸ hfinish)
    obtain ⟨y, he⟩ := FinitePath.exists_outgoing_edge_of_mem_support_of_ne_finish q hmem hne
    exact FinitePath.no_outgoing_edge_at_finish p y (hqE he)
  have hqContact : q.support ∩ Gamma.vertexSet Y ⊆
      {q.start, q.finish} ∪ removedInterior Q.backwardEdges := by
    rintro y ⟨hyq, hyY⟩
    rcases hcontact ⟨hqV hyq, hyY⟩ with he | hi
    · rcases he with he | he
      · exact Or.inl (Or.inl (he.trans hqstart.symm))
      · exact False.elim (hnotFinish (Set.mem_singleton_iff.mp he ▸ hyq))
    · exact Or.inr hi
  let P := Q.appendForwardPath q (hjoin.trans hqstart.symm) (hqE.trans hp)
    (hfresh.mono_left hqE)
  refine ⟨P, hQ.appendForwardPath_of_terminal_offReference hY hYfin q
    (hjoin.trans hqstart.symm) (hqE.trans hp) (hfresh.mono_left hqE)
    (hqfinish ▸ hxOff) (fun hs ↦ hstart (hqstart ▸ hs)) hqContact, ?_, ?_, ?_⟩
  · exact Q.appendForwardPath_first q _ _ _
  · exact (Q.appendForwardPath_last q _ _ _).trans hqfinish
  · rw [Q.appendForwardPath_forwardEdges]
    exact Set.union_subset_union_right _ hqE

/-- A fixed finite carrier cannot contain an infinite occurrence word,
even when the two ambient families themselves have infinite carriers. -/
theorem infiniteWord_vertexSet_infinite (Q : InfiniteColouredOccurrenceWord W Y) :
    Q.vertexSet.Infinite := by
  intro hfinite
  let H := Q.vertexSet
  let K : Set (Direction × (V × V)) :=
    ({.forward, .backward} : Set Direction) ×ˢ (H ×ˢ H)
  have hK : K.Finite :=
    ((Set.finite_singleton Direction.backward).insert Direction.forward).prod
      (hfinite.prod hfinite)
  apply hK.not_infinite
  apply Set.infinite_of_injective_forall_mem Q.occurrence_injective
  intro n
  cases hd : Q.direction n with
  | forward => exact ⟨by simp, ⟨n, rfl⟩, ⟨n + 1, rfl⟩⟩
  | backward => exact ⟨by simp, ⟨n + 1, rfl⟩, ⟨n, rfl⟩⟩

#print axioms exists_safeWord_to_offReference_forwardPoint
#print axioms infiniteWord_vertexSet_infinite

end Erdos599.Alternating.ColouredSafeForwardStopping
