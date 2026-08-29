/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.HalfwayOutsideReferenceClaim2
import ErdosProblems.Erdos599.HalfwayInsideCutSplice

/-!
# Inside-fragment splicing with a pruned outside reference

The outside-reference repair deliberately cannot produce an
`OutsideCutConstruction` for the full reference: reference components
contained in the closed set have no literal outside initial.  The canonical
inside-family compiler never needs that false field.  It needs only the
locations of cut endpoints uncovered by the full reference, and those
locations follow monotonically from the boundary for the pruned reference.

This file proves that reduction and feeds the actually constructed
full-reference assignment into `concreteInsideFragmentSpliceOfCut`.
-/

noncomputable section

open Cardinal Set

namespace Erdos599
namespace Blueprint
namespace LinkageBlueprint

open DirectedPath _root_.Erdos599.Alternating

universe u

variable {V : Type u}
variable {Gamma : DWeb V} {Y : Set Gamma.DPath}
variable {kappa theta : Cardinal.{u}}
variable {W : Set Gamma.DPath} {X : Set V}

/-- The canonical inside carrier is contained in the closing set together
with the earlier-stage set, using only the boundary for the outside
reference. -/
theorem insideCutCarrier_subset_closure_union_before_of_outsideReference
    {before innerRoof outerRoof : Set V}
    (B : OutsideCutBoundary (Y := outsideReference Y X)
      W X before innerRoof outerRoof) :
    insideCutCarrier Y W X ⊆ X ∪ before := by
  intro x hx
  rcases hx with (hx | hx) | hx
  · exact Or.inl hx.2
  · apply Or.inr
    apply (B.source_location ?_).1
    exact ⟨hx.1, fun hxout ↦
      hx.2 (initialSet_outsideReference_subset hxout)⟩
  · apply Or.inr
    apply (B.terminal_location ?_).1
    exact ⟨hx.1, fun hxout ↦
      hx.2 (vertexSet_outsideReference_subset hxout)⟩

namespace CanonicalInsideCut

variable {F : OutsideFracturedWarp W X}

/-- Cardinality of the canonical inside family, without an impossible
full-reference cut package. -/
theorem card_paths_of_outsideReferenceBoundary
    {before innerRoof outerRoof : Set V}
    (I : CanonicalInsideCut (Y := Y) (kappa := kappa) W X)
    (B : OutsideCutBoundary (Y := outsideReference Y X)
      W X before innerRoof outerRoof)
    (hkappa : aleph0 ≤ kappa) (hX : #X ≤ kappa)
    (hbefore : #before ≤ kappa) :
    #I.insideFamily.paths ≤ kappa := by
  refine (mk_paths_le_mk_vertexSet_by_initial I.insideFamily).trans ?_
  rw [I.vertexSet_eq]
  refine (Cardinal.mk_subtype_mono
    (insideCutCarrier_subset_closure_union_before_of_outsideReference B)).trans ?_
  exact (Cardinal.mk_union_le X before).trans
    (Cardinal.add_le_of_le hkappa hX hbefore)

/-- Any set containing the closing set and earlier stage contains the
canonical inside carrier. -/
theorem vertexSet_subset_of_outsideReferenceBoundary
    {before innerRoof outerRoof Z : Set V}
    (I : CanonicalInsideCut (Y := Y) (kappa := kappa) W X)
    (B : OutsideCutBoundary (Y := outsideReference Y X)
      W X before innerRoof outerRoof)
    (hX : X ⊆ Z) (hbefore : before ⊆ Z) :
    I.insideFamily.vertexSet ⊆ Z := by
  rw [I.vertexSet_eq]
  intro x hx
  rcases insideCutCarrier_subset_closure_union_before_of_outsideReference B hx with
    hx | hx
  · exact hX hx
  · exact hbefore hx

/-- Terminal accounting for the full-reference assignment needs no
full-reference boundary.  Covered cut initials are handled separately;
uncovered ones are exactly sources of the literal assignment. -/
theorem terminalBoundary_of_outsideReference
    {C : ClubStageGeometry Gamma Y kappa theta}
    (I : CanonicalInsideCut (Y := Y) (kappa := kappa) W X)
    (F : OutsideFracturedWarp W X)
    (reference_cut_initials :
      CutSplit.initialVertices (outsideCarrier W X)
          (outsideFamilyEdges W X) X ∩ Gamma.initialSet Y ⊆ C.newSlice)
    (row_terminals : Gamma.terminalFrontier W ⊆ C.newSlice) :
    I.insideFamily.terminalSet ⊆
      {x | ∃ s : {z // z ∈
        Gamma.initialSet F.holes.paths \ Gamma.initialSet Y}, s.1 = x} ∪
        C.newSlice := by
  intro x hx
  rcases I.terminalSet_subset_cutInitial_union_terminalFrontier hx with
    hxcut | hxterminal
  · by_cases hxY : x ∈ Gamma.initialSet Y
    · exact Or.inr (reference_cut_initials ⟨hxcut, hxY⟩)
    · apply Or.inl
      refine ⟨⟨x, ?_, hxY⟩, rfl⟩
      rw [F.initialSet_eq]
      exact hxcut
  · exact Or.inr (row_terminals hxterminal)

end CanonicalInsideCut

variable {C : ClubStageGeometry Gamma Y kappa theta}
variable {old : LinkageBlueprint Gamma Y kappa}
variable {u : V}

/-- Scheduler-facing inside-splice constructor for the repaired
outside-reference assignment.  All literal cut, endpoint, carrier,
cardinality, old-real containment, and target-route containment fields are
derived here.  The remaining arguments are the genuine nonlocal Section 9
orientation, ray, stability, and accounting obligations. -/
noncomputable def concreteInsideFragmentSpliceOfOutsideReference
    (F : OutsideFracturedWarp W X)
    (B : OutsideCutBoundary (Y := outsideReference Y X)
      W X C.before C.innerRoof C.outerRoof)
    (A : OutsideReferenceClaim2Assignment
      (Y := Y) (before := C.before) (innerRoof := C.innerRoof)
      (outerRoof := C.outerRoof) F)
    (hW : Gamma.IsWarp W)
    (hXcard : #X ≤ kappa)
    (hXclosed : X ⊆ C.closedSet)
    (hXroof : X ⊆ C.outerRoof)
    (hclosed_roof : C.closedSet ⊆ C.outerRoof)
    (old_vertices_row : old.vertexSet ⊆ Gamma.vertexSet W)
    (old_vertices_closure : old.vertexSet ⊆ X)
    (old_edges_row : old.realPart.edges ⊆ familyEdges W)
    (hcycle : ¬ ContainsDirectedCycle
      ((insideCutFamilyOfWarp (Y := Y) (kappa := kappa) W X hW).edgeSet ∪
        assignedFiniteEdges A.bracket.assignment))
    (hreverse : ¬ ContainsReverseDirectedRay
      ((insideCutFamilyOfWarp (Y := Y) (kappa := kappa) W X hW).edgeSet ∪
        assignedFiniteEdges A.bracket.assignment))
    (reference_cut_initials :
      CutSplit.initialVertices (outsideCarrier W X)
          (outsideFamilyEdges W X) X ∩ Gamma.initialSet Y ⊆ C.newSlice)
    (row_terminals : Gamma.terminalFrontier W ⊆ C.newSlice)
    (covers_source : Gamma.source ⊆
      (insideCutFamilyOfWarp (Y := Y) (kappa := kappa) W X hW).initialSet ∪
        Gamma.initialSet
          (referencePathsMeeting Y C.newSlice \
            referencePathsMeeting Y
              (insideCutFamilyOfWarp (Y := Y) (kappa := kappa)
                W X hW).vertexSet))
    (covered_initial_not_assigned_target :
      Gamma.source ∩
          (insideCutFamilyOfWarp (Y := Y) (kappa := kappa) W X hW).initialSet ⊆
        {x | ¬ ∃ y, (y, x) ∈ assignedFiniteEdges A.bracket.assignment})
    (every_relation_ray_strong :
      ∀ r : Ray (imaginaryGraph Gamma Y kappa),
        r.edgeSet ⊆
            (insideCutFamilyOfWarp (Y := Y) (kappa := kappa) W X hW).edgeSet ∪
              assignedFiniteEdges A.bracket.assignment →
          (strongEdgeIndices r).Infinite)
    (inside_stable :
      (insideCutFamilyOfWarp (Y := Y) (kappa := kappa) W X hW).Stable
        C.newSlice C.persistent)
    (old_vertices_accounted : old.vertexSet ⊆
      ((insideCutFamilyOfWarp (Y := Y) (kappa := kappa) W X hW).terminalSet ∩
          old.terminalSet) ∪
        {x | ∃ y,
          (x, y) ∈ old.familyGraph.edges ∩
            ((insideCutFamilyOfWarp (Y := Y) (kappa := kappa)
              W X hW).edgeSet ∪ assignedFiniteEdges A.bracket.assignment)} ∪
          relationCompletedRealVertices (Gamma := Gamma)
            ((insideCutFamilyOfWarp (Y := Y) (kappa := kappa)
              W X hW).edgeSet ∪ assignedFiniteEdges A.bracket.assignment)
            (insideCutFamilyOfWarp (Y := Y) (kappa := kappa)
              W X hW).vertexSet Gamma.target)
    (preserved_old_terminal_not_assigned_source :
      (insideCutFamilyOfWarp (Y := Y) (kappa := kappa) W X hW).terminalSet ∩
          old.terminalSet ⊆
        {x | ¬ ∃ y, (x, y) ∈ assignedFiniteEdges A.bracket.assignment})
    (target_path : FinitePath Gamma.graph)
    (target_path_start : target_path.start = u)
    (target_path_finish : target_path.finish ∈ Gamma.target)
    (target_path_vertices_row : target_path.support ⊆ Gamma.vertexSet W)
    (target_path_vertices_closure : target_path.support ⊆ X)
    (target_path_edges_row : target_path.edgeSet ⊆ familyEdges W)
    (preserves_other_real_terminals :
      old.realPart.terminals \ {u} ⊆
        relationRealTerminals (Gamma := Gamma)
          ((insideCutFamilyOfWarp (Y := Y) (kappa := kappa)
            W X hW).edgeSet ∪ assignedFiniteEdges A.bracket.assignment)
          (insideCutFamilyOfWarp (Y := Y) (kappa := kappa)
            W X hW).vertexSet) :
    ConcreteInsideFragmentSplice C old A.bracket.assignment u := by
  let I : CanonicalInsideCut (Y := Y) (kappa := kappa) W X :=
    canonicalInsideCutOfWarp (Y := Y) (kappa := kappa) W X hW
  apply concreteInsideFragmentSpliceOfCut
    (C := C) (old := old) (F := F) (A := A.bracket.assignment)
    (u := u) (target_path := target_path)
    I hW hcycle hreverse
      (I.terminalBoundary_of_outsideReference F
        reference_cut_initials row_terminals)
  · exact I.vertexSet_subset_of_outsideReferenceBoundary B hXroof
      (C.before_subset_closedSet.trans hclosed_roof)
  · exact covers_source
  · exact covered_initial_not_assigned_target
  · exact I.vertexSet_subset_of_outsideReferenceBoundary B hXclosed
      C.before_subset_closedSet
  · exact I.card_paths_of_outsideReferenceBoundary B
      C.capacity_infinite hXcard C.before_card
  · exact every_relation_ray_strong
  · exact inside_stable
  · exact I.oldRealVertices_subset old old_vertices_row
      old_vertices_closure
  · exact I.oldRealEdges_subset old old_edges_row old_vertices_closure
  · exact old_vertices_accounted
  · exact preserved_old_terminal_not_assigned_source
  · exact target_path_start
  · exact target_path_finish
  · exact I.targetPath_support_subset target_path target_path_vertices_row
      target_path_vertices_closure
  · exact I.targetPath_edges_subset target_path target_path_edges_row
      target_path_vertices_closure
  · exact preserves_other_real_terminals

end LinkageBlueprint
end Blueprint
end Erdos599

