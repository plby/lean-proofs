/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.GroundingAllMarkerBlockingPoints
import ErdosProblems.Erdos599.GroundingFragmentPredecessor

/-!
# Blocked fragments have genuine grounded or attachable initials

A fragment starting at an uncut marker receives no blocker. The existing
literal cut-predecessor theorem then classifies every blocked fragment:
its own initial lies in the original source, is a cut marker, or is the
head of a cut edge of its parent. Grounding is never inferred from the
initial of the parent after that parent has been cut.
-/

namespace Erdos599.GroundingAllMarkerAuxiliary.Input

open Set DirectedPath Alternating GroundingAllMarkerPorts

universe u

variable {V I : Type u} {G : DWeb V} (L : Input G I)

def CutFragmentGrounded (P : L.CutFragment) : Prop := P.path.initial ∈ G.source

def CutFragmentAttachable (C : Set L.Vertex) (P : L.CutFragment) : Prop :=
  (∃ y : L.markers, Vertex.marker y ∈ C ∧ P.path.initial = y.1) ∨
  ∃ e : V × V, e ∈ L.cutEdges C ∧ e ∈ P.parent.edgeSet ∧ e.2 = P.path.initial

theorem cutFragment_initial_eq_parent_or_cutHead (C : Set L.Vertex)
    {P : L.CutFragment} (hP : P ∈ L.cutFragments C) :
    P.path.initial = P.parent.initial ∨
      ∃ e : V × V, e ∈ L.cutEdges C ∧ e ∈ P.parent.edgeSet ∧ e.2 = P.path.initial := by
  rcases GroundingFragmentPredecessor.initial_eq_parent_initial_or_hasCutPredecessor
      L.cutFragmentInput (L.cutFragmentTags C) P hP with hfirst | ⟨e, he, heP, hei⟩
  · exact Or.inl hfirst
  · exact Or.inr ⟨e, by simpa only [L.cutFragmentTags_CE C] using he, heP, hei⟩

/-- A nonattachable marker-initial fragment has no blocker, including its
initial vertex: the receiving marker port is an escape destination. -/
theorem cutFragment_disjoint_blockingSet_of_uncut_marker_initial
    (C : Set L.Vertex) {P : L.CutFragment} (hP : P ∈ L.cutFragments C)
    (y : L.markers) (hy : Vertex.marker y ∉ C) (hinitial : P.path.initial = y.1) :
    Disjoint P.path.support (L.blockingSet C) := by
  have hAllR := L.cutFragment_subset_escapeRegion_of_uncut_marker_initial C hP y hy hinitial
  apply Set.disjoint_left.mpr
  rintro x hxP (hxOff | hxEscape | hxEnd)
  · exact L.not_mem_cutOff_of_mem_reference C
      ⟨P.parent, P.parent_mem, P.support_subset hxP⟩ hxOff
  · by_cases hxi : x = P.path.initial
    · exact hxEscape.2.2.1 ⟨y, hinitial.symm.trans hxi.symm, hy⟩
    · exact hxEscape.2.2.2 (L.escaping_predecessor_of_before C hP
        ⟨GroundingFragmentWarp.initial_beforeEq_of_mem hxP, fun h ↦ hxi h.symm⟩
        (hAllR P.path.initial_mem_support))
  · exact hxEnd.2.1 (hAllR hxP)

/-- The complete initial classification uses only genuine reference
initial provenance and the actual represented edge cut. -/
theorem blockedFragment_grounded_or_attachable (C : Set L.Vertex)
    (hInitials : G.initialSet L.reference.paths ⊆ G.source ∪ L.markers)
    {P : L.CutFragment} (hP : P ∈ L.blockedFragments C) :
    L.CutFragmentGrounded P ∨ L.CutFragmentAttachable C P := by
  rcases L.cutFragment_initial_eq_parent_or_cutHead C hP.1 with hfirst | hcut
  · have hInitial : P.path.initial ∈ G.source ∪ L.markers :=
      hfirst ▸ hInitials ⟨P.parent, P.parent_mem, rfl⟩
    rcases hInitial with hsource | hmarker
    · exact Or.inl hsource
    · let y : L.markers := ⟨P.path.initial, hmarker⟩
      by_cases hy : Vertex.marker y ∈ C
      · exact Or.inr (Or.inl ⟨y, hy, rfl⟩)
      · obtain ⟨x, hxP, hxK⟩ := hP.2
        exact (Set.disjoint_left.mp
          (L.cutFragment_disjoint_blockingSet_of_uncut_marker_initial C hP.1 y hy rfl)
          hxP hxK).elim
  · exact Or.inr (Or.inr hcut)

/-- A good owner is not used by any blocked fragment; this is stronger
than merely excluding the finite terminal of a good record. -/
theorem blockedFragment_parent_ne_goodRecord (C : Set L.Vertex)
    (hC : Popular.IsSeparator L.web C) {P : L.CutFragment} (hP : P ∈ L.blockedFragments C)
    {i : I} (hi : i ∉ L.badRecords C) : P.parent ≠ L.record i := by
  intro hparent
  obtain ⟨x, hxP, hxK⟩ := hP.2
  have hxi : x ∈ (L.record i).support := hparent ▸ P.support_subset hxP
  exact Set.disjoint_left.mp (L.goodRecordVertices_disjoint_blockingSet C hC)
    ⟨i, hi, hxi⟩ hxK

#print axioms cutFragment_initial_eq_parent_or_cutHead
#print axioms cutFragment_disjoint_blockingSet_of_uncut_marker_initial
#print axioms blockedFragment_grounded_or_attachable
#print axioms blockedFragment_parent_ne_goodRecord

end Erdos599.GroundingAllMarkerAuxiliary.Input
