/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.LambdaRawOwnerTrace
import ErdosProblems.Erdos599.GroundingGroundedRecordTraceReachability
import ErdosProblems.Erdos599.GroundingPathPrefix

/-!
# A genuine source prefix followed by an owner-avoiding raw suffix

The last contact is taken in the actual auxiliary path. The retained suffix
keeps all of its signed order, including repeated original vertices. This
construction handles both ordinary finite sources and proxy sources.
-/

noncomputable section

namespace Erdos599
namespace PopularAuxiliary.Input

open Set DirectedPath Alternating PopularSwitching
open GroundingGroundedRecordTraceReachability

universe u

variable {V I : Type u} {Gamma : DWeb V}
variable (L : PopularAuxiliary.Input Gamma I)

/-- Actual last-owner attachment data, including the original auxiliary
arc, its deterministic connector, and a genuine finite source prefix. -/
structure RawOwnerAttachment (H : Gamma.DPath) (p : FinitePath L.lambda.graph) where
  tail : FinitePath L.lambda.graph
  tail_finish : tail.finish = p.finish
  tail_support_suffix : tail.walk.support <:+ p.walk.support
  origin : L.LV
  origin_arc : (origin, tail.start) ∈ p.edgeSet
  anchor : V
  nextVertex : V
  connector_eq : L.chosenConnector? origin tail.start = some (anchor, nextVertex)
  connector : L.ForwardConnector origin tail.start anchor nextVertex
  anchor_mem_owner : anchor ∈ H.support
  next_not_mem_owner : nextVertex ∉ H.support
  tail_avoids_owner : Disjoint tail.support (ladderTrace L H)
  sourcePrefix : FinitePath Gamma.graph
  sourcePrefix_start : sourcePrefix.start = H.initial
  sourcePrefix_finish : sourcePrefix.finish = anchor
  sourcePrefix_support : sourcePrefix.support ⊆ H.support
  sourcePrefix_edges : sourcePrefix.edgeSet ⊆ H.edgeSet

variable {L}

theorem RawOwnerAttachment.tail_support_subset {H : Gamma.DPath}
    {p : FinitePath L.lambda.graph} (A : L.RawOwnerAttachment H p) :
    A.tail.support ⊆ p.support := A.tail_support_suffix.subset

theorem RawOwnerAttachment.tail_edges_subset {H : Gamma.DPath}
    {p : FinitePath L.lambda.graph} (A : L.RawOwnerAttachment H p) :
    A.tail.edgeSet ⊆ p.edgeSet :=
  A.tail.walk.edgeSet_subset_of_support_suffix p.walk A.tail_support_suffix

theorem RawOwnerAttachment.tail_no_proxy {H : Gamma.DPath}
    {p : FinitePath L.lambda.graph} (A : L.RawOwnerAttachment H p) :
    ∀ i : I, LambdaVertex.proxy i ∉ A.tail.support :=
  L.no_proxy_of_incoming_arc A.tail (p.edgeSet_subset_adj A.origin_arc)

theorem RawOwnerAttachment.anchor_ne_next {H : Gamma.DPath}
    {p : FinitePath L.lambda.graph} (A : L.RawOwnerAttachment H p) :
    A.anchor ≠ A.nextVertex := fun h ↦ A.next_not_mem_owner (h ▸ A.anchor_mem_owner)

theorem RawOwnerAttachment.prefix_starts_in_source {H : Gamma.DPath}
    {p : FinitePath L.lambda.graph} (A : L.RawOwnerAttachment H p)
    (hH : H.initial ∈ Gamma.source) : A.sourcePrefix.start ∈ Gamma.source :=
  A.sourcePrefix_start.symm ▸ hH

private theorem exists_cons_of_ne {D : Digraph V} {a b : V} (q : Walk D a b)
    (hne : a ≠ b) : ∃ c, ∃ (h : D.Adj a c) (w : Walk D c b), q = .cons h w := by
  cases q with
  | nil => exact False.elim (hne rfl)
  | cons h w => exact ⟨_, h, w, rfl⟩

variable (L)

/-- Every auxiliary path represented by its actual starting owner and
ending outside that owner's trace has a clean raw attachment. -/
theorem exists_rawOwnerAttachment (H : Gamma.DPath) (hH : H ∈ L.ladder.paths)
    (p : FinitePath L.lambda.graph) (hrep : Represents L H p.start)
    (hend : p.finish ∉ ladderTrace L H)
    (hfinal : ∀ i : I, p.finish ≠ .proxy i) : Nonempty (L.RawOwnerAttachment H p) := by
  suffices hdata : ∃ (q : FinitePath L.lambda.graph) (a : L.LV) (x y : V),
      q.finish = p.finish ∧ q.walk.support <:+ p.walk.support ∧
      (a, q.start) ∈ p.edgeSet ∧ L.chosenConnector? a q.start = some (x, y) ∧
      L.ForwardConnector a q.start x y ∧ x ∈ H.support ∧ y ∉ H.support ∧
      Disjoint q.support (ladderTrace L H) by
    obtain ⟨q, a, x, y, hqfinish, hqsuffix, haq, hchoice, hconnector, hx, hy, hav⟩ := hdata
    obtain ⟨qPrefix, hprefixStart, hprefixFinish, hprefixSupport, hprefixEdges⟩ :=
      GroundingPathPrefix.exists_initialFinitePrefix H hx
    exact ⟨{
      tail := q
      tail_finish := hqfinish
      tail_support_suffix := hqsuffix
      origin := a
      origin_arc := haq
      anchor := x
      nextVertex := y
      connector_eq := hchoice
      connector := hconnector
      anchor_mem_owner := hx
      next_not_mem_owner := hy
      tail_avoids_owner := hav
      sourcePrefix := qPrefix
      sourcePrefix_start := hprefixStart
      sourcePrefix_finish := hprefixFinish
      sourcePrefix_support := hprefixSupport
      sourcePrefix_edges := hprefixEdges }⟩
  by_cases hmeet : p.walk.Meets (ladderTrace L H)
  · let C := p.walk.lastHit (ladderTrace L H) hmeet
    have hne : C.startpoint ≠ p.finish := fun h ↦ hend (h ▸ C.startpoint_mem)
    obtain ⟨b, hab, w, hw⟩ := exists_cons_of_ne C.walk hne
    have hwPath : w.IsPath := by
      have h := C.isPath p.isPath
      rw [hw] at h
      exact (List.nodup_cons.1 h).2
    let q : FinitePath L.lambda.graph := ⟨b, p.finish, w, hwPath⟩
    have hqsuffix : q.walk.support <:+ p.walk.support := by
      exact (List.suffix_cons C.startpoint w.support).trans (by
        simpa only [hw, Walk.support_cons] using C.support_suffix)
    have hav : Disjoint q.support (ladderTrace L H) := by
      apply Set.disjoint_left.2
      intro z hz hzH
      apply C.no_mem_after _ hzH
      change z ∈ w.support at hz
      simpa only [hw, Walk.support_cons, List.tail_cons] using hz
    have hb : b ∉ ladderTrace L H :=
      fun hb ↦ Set.disjoint_left.1 hav q.start_mem_support hb
    obtain ⟨x, y, hchoice, hconnector, hx, hy⟩ :=
      L.chosenConnector_leaves_owner hH hab C.startpoint_mem hb
    have harc : (C.startpoint, b) ∈ p.edgeSet := by
      apply C.walk.edgeSet_subset_of_support_suffix p.walk C.support_suffix
      rw [hw]
      exact Or.inl rfl
    exact ⟨q, C.startpoint, x, y, rfl, hqsuffix, harc, hchoice, hconnector, hx, hy, hav⟩
  · rcases hrep with ⟨f, howner, hstart⟩ | ⟨i, howner, hstart⟩
    · exact False.elim <| hmeet ⟨p.start, p.walk.start_mem_support, by
        rw [hstart]
        apply (old_mem_ladderTrace_iff L H f.finish).2
        rw [howner]
        exact f.finish_mem_support⟩
    · have hne : p.start ≠ p.finish := fun h ↦ hfinal i (h.symm.trans hstart)
      obtain ⟨b, hab, w, hw⟩ := exists_cons_of_ne p.walk hne
      have hwPath : w.IsPath := by
        have h := p.isPath
        rw [hw] at h
        exact (List.nodup_cons.1 h).2
      let q : FinitePath L.lambda.graph := ⟨b, p.finish, w, hwPath⟩
      have hqsuffix : q.walk.support <:+ p.walk.support := by
        rw [hw, Walk.support_cons]
        exact List.suffix_cons p.start w.support
      have hav : Disjoint q.support (ladderTrace L H) := by
        apply Set.disjoint_left.2
        intro z hz hzH
        exact hmeet ⟨z, hqsuffix.subset hz, hzH⟩
      have hb : b ∉ ladderTrace L H :=
        fun hb ↦ Set.disjoint_left.1 hav q.start_mem_support hb
      obtain ⟨x, y, hchoice, hconnector, hx, hy⟩ :=
        L.chosenConnector_proxy_to_outside_owner hH howner
          (by simpa only [hstart] using hab) hb
      have harc : (p.start, b) ∈ p.edgeSet := by
        change (p.start, b) ∈ p.walk.edgeSet
        rw [hw]
        exact Or.inl rfl
      refine ⟨q, p.start, x, y, rfl, hqsuffix, harc, ?_, ?_, hx, hy, hav⟩
      · simpa only [hstart] using hchoice
      · simpa only [hstart] using hconnector

end PopularAuxiliary.Input
end Erdos599

#print axioms Erdos599.PopularAuxiliary.Input.exists_rawOwnerAttachment
#print axioms Erdos599.PopularAuxiliary.Input.RawOwnerAttachment.tail_no_proxy
