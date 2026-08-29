/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.LambdaRawOwnerAttachment
import ErdosProblems.Erdos599.LambdaRawSignedBalance

/-!
# Signed geometry of the clean raw owner suffix

Every signed suffix edge avoids the whole starting owner. Prepending the
actual attachment connector is therefore fresh; auxiliary head-port
uniqueness supplies the remaining incoming degree bound. The signed word
retains repeated original vertices and has its literal endpoint balance.
-/

noncomputable section

namespace Erdos599.PopularAuxiliary.Input

open Set DirectedPath Alternating PopularSwitching

universe u

variable {V I : Type u} {Gamma : DWeb V}
variable {L : PopularAuxiliary.Input Gamma I}

private theorem mem_trace_of_gadgetExit_mem_owner {H : Gamma.DPath}
    (hH : H ∈ L.ladder.paths) {a b : L.LV} {x : V}
    (hab : L.lambda.graph.Adj a b) (hexit : L.gadgetExit a = some x)
    (hx : x ∈ H.support) : a ∈ ladderTrace L H := by
  cases a with
  | old z =>
      have hzx : z = x := Option.some.inj hexit
      exact (old_mem_ladderTrace_iff L H z).2 (hzx.symm ▸ hx)
  | edge z w =>
      have hzx : z = x := Option.some.inj hexit
      apply (edge_mem_ladderTrace_iff L H z w).2
      exact L.referenceEdge_mem_owner_of_tail hH
        (L.familyEdge_of_adj_from_edge hab) (hzx.symm ▸ hx)
  | proxy i => simp at hexit

namespace RawOwnerAttachment

variable {H : Gamma.DPath} {p : FinitePath L.lambda.graph}
variable (A : L.RawOwnerAttachment H p)

/-- Both endpoints of every raw suffix connector avoid the starting owner. -/
theorem tail_connector_avoids_owner (hH : H ∈ L.ladder.paths) {e : V × V}
    (he : e ∈ L.selectedConnectorEdges A.tail) :
    e.1 ∉ H.support ∧ e.2 ∉ H.support := by
  obtain ⟨a, b, hab, hchoice⟩ := he
  have hc := L.chosenConnector?_eq_some hchoice
  have ha := (A.tail.edgeSet_subset_support_prod hab).1
  have hb := (A.tail.edgeSet_subset_support_prod hab).2
  constructor
  · intro hx
    rcases hc.1 with hexit | ⟨i, rfl, _hi⟩
    · exact Set.disjoint_left.1 A.tail_avoids_owner ha
        (mem_trace_of_gadgetExit_mem_owner hH
          (A.tail.edgeSet_subset_adj hab) hexit hx)
    · exact A.tail_no_proxy i ha
  · intro hy
    exact Set.disjoint_left.1 A.tail_avoids_owner hb
      (L.mem_trace_of_gadgetEntry_mem_owner hH
        (A.tail.edgeSet_subset_adj hab) hc.2.1 hy)

/-- A backward suffix gadget has neither endpoint on the removed owner. -/
theorem tail_represented_avoids_owner (hH : H ∈ L.ladder.paths) {e : V × V}
    (he : e ∈ L.representedEdges A.tail) :
    e.1 ∉ H.support ∧ e.2 ∉ H.support := by
  have hnot : e ∉ H.edgeSet := fun h ↦
    Set.disjoint_left.1 A.tail_avoids_owner he.1
      ((edge_mem_ladderTrace_iff L H e.1 e.2).2 h)
  exact ⟨fun h ↦ hnot (L.referenceEdge_mem_owner_of_tail hH he.2 h),
    fun h ↦ hnot (L.referenceEdge_mem_owner_of_head hH he.2 h)⟩

/-- The source hypothesis of the original path certifies every suffix gadget. -/
theorem tail_edgeNode_mem_familyEdges (hs : p.start ∈ L.lambda.source)
    {e : V × V} (he : LambdaVertex.edge e.1 e.2 ∈ A.tail.support) :
    e ∈ L.familyEdges :=
  L.edgeNode_mem_familyEdges_of_start_in_source p hs (A.tail_support_subset he)

/-- The suffix loses no backward edge under the proper-edge filter. -/
theorem tail_proper_backwardEdges (hs : p.start ∈ L.lambda.source) :
    directedSignedEdgeSet .backward (L.decodeProperSteps A.tail) =
      L.representedEdges A.tail := by
  rw [decodeProperSteps, directedSignedEdgeSet_properSignedSteps,
    L.backwardEdges_decodeWalkSteps A.tail.walk]
  ext e
  constructor
  · intro he
    exact ⟨he.1, A.tail_edgeNode_mem_familyEdges hs he.1⟩
  · intro he
    exact ⟨he.1, L.raw_familyEdge_ne he.2⟩

/-- The proper signed suffix avoids the removed owner in both directions. -/
theorem tail_signed_avoids_owner (hH : H ∈ L.ladder.paths)
    (hs : p.start ∈ L.lambda.source) {s : SignedEdge V}
    (hsigned : s ∈ L.decodeProperSteps A.tail) :
    s.edge.1 ∉ H.support ∧ s.edge.2 ∉ H.support := by
  cases hd : s.direction with
  | forward =>
      have he : s.edge ∈ directedSignedEdgeSet .forward (L.decodeProperSteps A.tail) :=
        ⟨s, hsigned, hd, rfl⟩
      rw [decodeProperSteps_forwardEdges] at he
      exact A.tail_connector_avoids_owner hH he.1
  | backward =>
      have he : s.edge ∈ directedSignedEdgeSet .backward (L.decodeProperSteps A.tail) :=
        ⟨s, hsigned, hd, rfl⟩
      rw [A.tail_proper_backwardEdges hs] at he
      exact A.tail_represented_avoids_owner hH he

/-- The clean suffix with its actual preceding forward connector. -/
def steps : List (SignedEdge V) :=
  SignedEdge.forward (A.anchor, A.nextVertex) :: L.decodeProperSteps A.tail

/-- The actual forward insertion relation of the attached signed word. -/
def forwardEdges : Set (V × V) :=
  {(A.anchor, A.nextVertex)} ∪ L.properSelectedConnectorEdges A.tail

theorem steps_forwardEdges : directedSignedEdgeSet .forward A.steps = A.forwardEdges := by
  simp only [steps, directedSignedEdgeSet_cons, SignedEdge.forward,
    ↓reduceIte, decodeProperSteps_forwardEdges, forwardEdges]

theorem steps_backwardEdges (hs : p.start ∈ L.lambda.source) :
    directedSignedEdgeSet .backward A.steps = L.representedEdges A.tail := by
  simp only [steps, directedSignedEdgeSet_cons, SignedEdge.forward,
    reduceCtorEq, ↓reduceIte, Set.empty_union, A.tail_proper_backwardEdges hs]

/-- The connector starts the word at the real attachment, not at a proxy. -/
theorem steps_runs {t : V} (ht : L.gadgetExit p.finish = some t) :
    RunsFromTo A.anchor t A.steps := by
  have htail : RunsFromTo A.nextVertex t (L.decodeProperSteps A.tail) :=
    (L.decodeWalkSteps_runs_from_entry A.tail.walk A.connector.2.1
      (by simpa only [A.tail_finish] using ht)).filter_selfLoops
  exact RunsFromTo.cons (SignedEdge.forward (A.anchor, A.nextVertex)) htail

/-- The attachment edge cannot repeat a signed edge of the clean suffix. -/
theorem steps_nodup (hL : L.HasBoundaryIncidence) (hH : H ∈ L.ladder.paths)
    (hs : p.start ∈ L.lambda.source) : A.steps.Nodup := by
  apply List.nodup_cons.2
  refine ⟨?_, hL.decodeProperSteps_nodup A.tail⟩
  intro he
  exact (A.tail_signed_avoids_owner hH hs he).1 A.anchor_mem_owner

/-- A suffix forward edge cannot enter the attachment's head: its unique
head port is the suffix start, which has no incoming auxiliary edge. -/
theorem no_tail_connector_into_next (hL : L.HasBoundaryIncidence) {x : V}
    (he : (x, A.nextVertex) ∈ L.properSelectedConnectorEdges A.tail) : False := by
  obtain ⟨⟨a, b, hab, hchoice⟩, hne⟩ := he
  have hb : b = A.tail.start :=
    (hL.forward_head_port (A.tail.edgeSet_subset_adj hab)
      (L.chosenConnector?_eq_some hchoice) hne).unique
        (hL.forward_head_port (p.edgeSet_subset_adj A.origin_arc)
          A.connector A.anchor_ne_next)
  apply Alternating.FinitePath.no_incoming_edge_at_start A.tail a
  simpa only [← hb] using hab

/-- Both endpoint degrees of the entire inserted forward relation are at most one. -/
theorem forwardEdges_biUnique (hL : L.HasBoundaryIncidence) (hH : H ∈ L.ladder.paths) :
    Relator.BiUnique (fun x y ↦ (x, y) ∈ A.forwardEdges) := by
  constructor
  · intro x z y hxy hzy
    rcases hxy with hxy | hxy <;> rcases hzy with hzy | hzy
    · exact congrArg Prod.fst ((Set.mem_singleton_iff.1 hxy).trans
        (Set.mem_singleton_iff.1 hzy).symm)
    · have hy : y = A.nextVertex := congrArg Prod.snd (Set.mem_singleton_iff.1 hxy)
      exact False.elim (A.no_tail_connector_into_next hL (hy ▸ hzy))
    · have hy : y = A.nextVertex := congrArg Prod.snd (Set.mem_singleton_iff.1 hzy)
      exact False.elim (A.no_tail_connector_into_next hL (hy ▸ hxy))
    · exact hL.properSelectedConnectorEdges_leftUnique A.tail hxy hzy
  · intro x y z hxy hxz
    rcases hxy with hxy | hxy <;> rcases hxz with hxz | hxz
    · exact congrArg Prod.snd ((Set.mem_singleton_iff.1 hxy).trans
        (Set.mem_singleton_iff.1 hxz).symm)
    · have hx : x = A.anchor := congrArg Prod.fst (Set.mem_singleton_iff.1 hxy)
      exact False.elim ((A.tail_connector_avoids_owner hH hxz.1).1
        (hx.symm ▸ A.anchor_mem_owner))
    · have hx : x = A.anchor := congrArg Prod.fst (Set.mem_singleton_iff.1 hxz)
      exact False.elim ((A.tail_connector_avoids_owner hH hxy.1).1
        (hx.symm ▸ A.anchor_mem_owner))
    · exact hL.properSelectedConnectorEdges_rightUnique_of_no_proxy
        A.tail A.tail_no_proxy hxy hxz

/-- Exact signed balance at the attachment and actual final gadget exit. -/
theorem direction_balance (hL : L.HasBoundaryIncidence) (hH : H ∈ L.ladder.paths)
    (hs : p.start ∈ L.lambda.source) {t : V}
    (ht : L.gadgetExit p.finish = some t) (x : V) :
    edgeBalance A.forwardEdges x - edgeBalance (L.representedEdges A.tail) x =
      propInt (x = A.anchor) - propInt (x = t) := by
  have hF : Relator.BiUnique
      (fun a b ↦ (a, b) ∈ directedSignedEdgeSet .forward A.steps) := by
    rw [A.steps_forwardEdges]
    exact A.forwardEdges_biUnique hL hH
  have hB : Relator.BiUnique
      (fun a b ↦ (a, b) ∈ directedSignedEdgeSet .backward A.steps) := by
    rw [A.steps_backwardEdges hs]
    exact ⟨fun _ _ _ h₁ h₂ ↦ L.raw_familyEdges_biUnique.1 h₁.2 h₂.2,
      fun _ _ _ h₁ h₂ ↦ L.raw_familyEdges_biUnique.2 h₁.2 h₂.2⟩
  simpa only [A.steps_forwardEdges, A.steps_backwardEdges hs] using
    (A.steps_runs ht).edgeBalance_forward_sub_backward (A.steps_nodup hL hH hs) hF hB x

#print axioms tail_signed_avoids_owner
#print axioms forwardEdges_biUnique
#print axioms direction_balance

end RawOwnerAttachment
end Erdos599.PopularAuxiliary.Input
