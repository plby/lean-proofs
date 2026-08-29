/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.LambdaRawOwnerSuffix

/-!
# Whole-owner replacement by the genuine source prefix

The reference owner is removed in full, the lossless raw suffix is switched
against all other reference edges, and its actual source prefix is restored.
All mixed incidences and the exact source-to-exit boundary are proved from
the attachment geometry, not assumed as a normalization certificate.
-/

noncomputable section

namespace Erdos599.PopularAuxiliary.Input.RawOwnerAttachment

open Set DirectedPath Alternating

universe u

variable {V I : Type u} {Gamma : DWeb V}
variable {L : PopularAuxiliary.Input Gamma I} {H : Gamma.DPath}
variable {p : FinitePath L.lambda.graph} (A : L.RawOwnerAttachment H p)

/-- The anchor-starting switch against the reference with its whole owner removed. -/
def switchEdges : Set (V × V) :=
  ((L.familyEdges \ H.edgeSet) \ L.representedEdges A.tail) ∪ A.forwardEdges

/-- The actual source-starting relation, restoring the genuine owner prefix. -/
def sourceEdges : Set (V × V) := A.switchEdges ∪ A.sourcePrefix.edgeSet

theorem backward_subset_ownerDeleted (hH : H ∈ L.ladder.paths) :
    L.representedEdges A.tail ⊆ L.familyEdges \ H.edgeSet := by
  intro e he
  exact ⟨he.2, fun h ↦ (A.tail_represented_avoids_owner hH he).1
    (H.edgeSet_subset_support_prod h).1⟩

/-- Even the first forward attachment removes every conflicting incoming edge. -/
theorem incoming_reference_represented (hL : L.HasBoundaryIncidence) {x y z : V}
    (hxy : (x, y) ∈ A.forwardEdges) (hzy : (z, y) ∈ L.familyEdges) :
    (z, y) ∈ L.representedEdges A.tail := by
  rcases hxy with hxy | hxy
  · have hy : y = A.nextVertex := congrArg Prod.snd (Set.mem_singleton_iff.1 hxy)
    subst y
    have hb := (hL.forward_head_port (p.edgeSet_subset_adj A.origin_arc)
      A.connector A.anchor_ne_next).eq_edge_of_reference hzy
    refine ⟨?_, hzy⟩
    rw [← hb]
    exact A.tail.start_mem_support
  · exact hL.incoming_reference_represented A.tail hxy hzy

/-- Outgoing conflicts either lie on the removed owner or are suffix gadgets. -/
theorem outgoing_ownerDeleted_represented (hL : L.HasBoundaryIncidence)
    (hH : H ∈ L.ladder.paths) {x y z : V}
    (hxy : (x, y) ∈ A.forwardEdges) (hxz : (x, z) ∈ L.familyEdges \ H.edgeSet) :
    (x, z) ∈ L.representedEdges A.tail := by
  rcases hxy with hxy | hxy
  · have hx : x = A.anchor := congrArg Prod.fst (Set.mem_singleton_iff.1 hxy)
    exact False.elim (hxz.2 (L.referenceEdge_mem_owner_of_tail hH hxz.1
      (hx.symm ▸ A.anchor_mem_owner)))
  · exact hL.outgoing_reference_represented_of_no_proxy A.tail A.tail_no_proxy hxy hxz.1

/-- All unused reference edges outside the owner survive with degree at most one. -/
theorem switchEdges_biUnique (hL : L.HasBoundaryIncidence) (hH : H ∈ L.ladder.paths) :
    Relator.BiUnique (fun x y ↦ (x, y) ∈ A.switchEdges) := by
  constructor
  · intro x z y hxy hzy
    rcases hxy with hxy | hxy <;> rcases hzy with hzy | hzy
    · exact L.raw_familyEdges_biUnique.1 hxy.1.1 hzy.1.1
    · exact False.elim (hxy.2 (A.incoming_reference_represented hL hzy hxy.1.1))
    · exact False.elim (hzy.2 (A.incoming_reference_represented hL hxy hzy.1.1))
    · exact (A.forwardEdges_biUnique hL hH).1 hxy hzy
  · intro x y z hxy hxz
    rcases hxy with hxy | hxy <;> rcases hxz with hxz | hxz
    · exact L.raw_familyEdges_biUnique.2 hxy.1.1 hxz.1.1
    · exact False.elim (hxy.2 (A.outgoing_ownerDeleted_represented hL hH hxz hxy.1))
    · exact False.elim (hxz.2 (A.outgoing_ownerDeleted_represented hL hH hxy hxz.1))
    · exact (A.forwardEdges_biUnique hL hH).2 hxy hxz

theorem retained_disjoint_forward (hL : L.HasBoundaryIncidence) :
    Disjoint ((L.familyEdges \ H.edgeSet) \ L.representedEdges A.tail) A.forwardEdges := by
  apply Set.disjoint_left.2
  intro e he hf
  exact he.2 (A.incoming_reference_represented hL hf he.1.1)

/-- The anchor switch has exactly the endpoint balance of its signed word. -/
theorem switchEdges_balance (hL : L.HasBoundaryIncidence) (hH : H ∈ L.ladder.paths)
    (hs : p.start ∈ L.lambda.source) {t : V}
    (ht : L.gadgetExit p.finish = some t) (x : V) :
    edgeBalance A.switchEdges x = edgeBalance (L.familyEdges \ H.edgeSet) x +
      propInt (x = A.anchor) - propInt (x = t) := by
  have hbase : Relator.BiUnique (fun a b ↦ (a, b) ∈ L.familyEdges \ H.edgeSet) :=
    ⟨fun _ _ _ h₁ h₂ ↦ L.raw_familyEdges_biUnique.1 h₁.1 h₂.1,
      fun _ _ _ h₁ h₂ ↦ L.raw_familyEdges_biUnique.2 h₁.1 h₂.1⟩
  have hbi := A.switchEdges_biUnique hL hH
  have hcalc := edgeBalance_sdiff_union_eq_add_sub (A.backward_subset_ownerDeleted hH)
    hbase.2 hbase.1 hbi.2 hbi.1 (A.retained_disjoint_forward hL) x
  have hdelta := A.direction_balance hL hH hs ht x
  change edgeBalance (((L.familyEdges \ H.edgeSet) \ L.representedEdges A.tail) ∪
    A.forwardEdges) x = _
  omega

/-- No switched edge enters the removed owner. -/
theorem switchEdges_head_avoids_owner (hH : H ∈ L.ladder.paths) {e : V × V}
    (he : e ∈ A.switchEdges) : e.2 ∉ H.support := by
  rcases he with he | he | he
  · exact fun h ↦ he.1.2 (L.referenceEdge_mem_owner_of_head hH he.1.1 h)
  · have hhead : e.2 = A.nextVertex := congrArg Prod.snd (Set.mem_singleton_iff.1 he)
    exact hhead.symm ▸ A.next_not_mem_owner
  · exact (A.tail_connector_avoids_owner hH he.1).2

/-- The attachment anchor is the only possible switched departure on the owner. -/
theorem switchEdges_tail_owner_eq_anchor (hH : H ∈ L.ladder.paths) {e : V × V}
    (he : e ∈ A.switchEdges) (hx : e.1 ∈ H.support) : e.1 = A.anchor := by
  rcases he with he | he | he
  · exact False.elim (he.1.2 (L.referenceEdge_mem_owner_of_tail hH he.1.1 hx))
  · exact congrArg Prod.fst (Set.mem_singleton_iff.1 he)
  · exact False.elim ((A.tail_connector_avoids_owner hH he.1).1 hx)

/-- The prefix is edge-disjoint from the whole anchor switch. -/
theorem switchEdges_disjoint_prefix (hH : H ∈ L.ladder.paths) :
    Disjoint A.switchEdges A.sourcePrefix.edgeSet := by
  apply Set.disjoint_left.2
  intro e he hp
  exact A.switchEdges_head_avoids_owner hH he
    (A.sourcePrefix_support (A.sourcePrefix.edgeSet_subset_support_prod hp).2)

/-- Restoring the genuine prefix creates no branch or merge. -/
theorem sourceEdges_biUnique (hL : L.HasBoundaryIncidence) (hH : H ∈ L.ladder.paths) :
    Relator.BiUnique (fun x y ↦ (x, y) ∈ A.sourceEdges) := by
  have hswitch := A.switchEdges_biUnique hL hH
  have hprefix := Alternating.FinitePath.edgeSet_biUnique A.sourcePrefix
  constructor
  · intro x z y hxy hzy
    rcases hxy with hxy | hxy <;> rcases hzy with hzy | hzy
    · exact hswitch.1 hxy hzy
    · exact False.elim (A.switchEdges_head_avoids_owner hH hxy
        (A.sourcePrefix_support (A.sourcePrefix.edgeSet_subset_support_prod hzy).2))
    · exact False.elim (A.switchEdges_head_avoids_owner hH hzy
        (A.sourcePrefix_support (A.sourcePrefix.edgeSet_subset_support_prod hxy).2))
    · exact hprefix.1 hxy hzy
  · intro x y z hxy hxz
    rcases hxy with hxy | hxy <;> rcases hxz with hxz | hxz
    · exact hswitch.2 hxy hxz
    · have hx := A.switchEdges_tail_owner_eq_anchor hH hxy
        (A.sourcePrefix_support (A.sourcePrefix.edgeSet_subset_support_prod hxz).1)
      have hfinish : x = A.sourcePrefix.finish := hx.trans A.sourcePrefix_finish.symm
      exact False.elim (Alternating.FinitePath.no_outgoing_edge_at_finish
        A.sourcePrefix z (hfinish ▸ hxz))
    · have hx := A.switchEdges_tail_owner_eq_anchor hH hxz
        (A.sourcePrefix_support (A.sourcePrefix.edgeSet_subset_support_prod hxy).1)
      have hfinish : x = A.sourcePrefix.finish := hx.trans A.sourcePrefix_finish.symm
      exact False.elim (Alternating.FinitePath.no_outgoing_edge_at_finish
        A.sourcePrefix y (hfinish ▸ hxy))
    · exact hprefix.2 hxy hxz

/-- Finite-path balance includes the possible trivial source prefix. -/
theorem sourcePrefix_balance (x : V) :
    edgeBalance A.sourcePrefix.edgeSet x =
      propInt (x = H.initial) - propInt (x = A.anchor) := by
  suffices h : edgeBalance A.sourcePrefix.edgeSet x =
      propInt (x = A.sourcePrefix.start) - propInt (x = A.sourcePrefix.finish) by
    simpa only [A.sourcePrefix_start, A.sourcePrefix_finish] using h
  by_cases hne : A.sourcePrefix.start ≠ A.sourcePrefix.finish
  · exact Alternating.FinitePath.edgeBalance_eq_endpoints A.sourcePrefix hne x
  · have heq := not_not.mp hne
    rw [edgeBalance, Alternating.FinitePath.hasOutgoing_edgeSet_iff,
      Alternating.FinitePath.hasIncoming_edgeSet_iff, heq, sub_self, sub_self]

/-- Exact balance at the genuine original source, including proxy attachments. -/
theorem sourceEdges_balance (hL : L.HasBoundaryIncidence) (hH : H ∈ L.ladder.paths)
    (hs : p.start ∈ L.lambda.source) {t : V}
    (ht : L.gadgetExit p.finish = some t) (x : V) :
    edgeBalance A.sourceEdges x = edgeBalance (L.familyEdges \ H.edgeSet) x +
      propInt (x = H.initial) - propInt (x = t) := by
  have hswitch := A.switchEdges_biUnique hL hH
  have hsource := A.sourceEdges_biUnique hL hH
  have hadd := edgeBalance_sdiff_union_eq_add_sub
    (E := A.switchEdges) (B := ∅) (F := A.sourcePrefix.edgeSet)
    (Set.empty_subset _) hswitch.2 hswitch.1
    (by simpa only [Set.sdiff_empty, sourceEdges] using hsource.2)
    (by simpa only [Set.sdiff_empty, sourceEdges] using hsource.1)
    (by simpa only [Set.sdiff_empty] using A.switchEdges_disjoint_prefix hH) x
  have hempty : edgeBalance (∅ : Set (V × V)) x = 0 := by
    simp [edgeBalance, HasOutgoing, HasIncoming, propInt]
  have hcalc : edgeBalance A.sourceEdges x =
      edgeBalance A.switchEdges x + edgeBalance A.sourcePrefix.edgeSet x := by
    simpa only [Set.sdiff_empty, sourceEdges, hempty, sub_zero] using hadd
  rw [hcalc, A.switchEdges_balance hL hH hs ht x, A.sourcePrefix_balance]
  omega

#print axioms switchEdges_biUnique
#print axioms sourceEdges_biUnique
#print axioms sourceEdges_balance

end Erdos599.PopularAuxiliary.Input.RawOwnerAttachment
