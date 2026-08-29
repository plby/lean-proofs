/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.HalfwayPostClosureDeadEndBoundary
import ErdosProblems.Erdos599.TwoWarpMatchingProjection

/-!
# The actual cut sources lie on the two-warp matching difference

An actual source of the fractured post-closure assignment is a closed
vertex at which the later interval row leaves the closing set.  Since the
closing set is closed under the limiting reference, that literal leaving
edge cannot also be a limiting-reference edge.  It is therefore a genuine
forward-exclusive matching edge.

This is only an incidence statement.  In particular, it does not claim
that the sending copy of the cut source is an unmatched endpoint of its
whole matching component: a reference edge or an identity matching edge
may precede it.  The component must be rooted at its actual unmatched end
before compilation.
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599.Blueprint.LinkageBlueprint.PostClosureMacroCompressorAssignment

open DirectedPath _root_.Erdos599.Alternating
open _root_.Erdos599.TwoWarpMatchingTraversal

universe u

variable {V : Type u} {Gamma : DWeb V} {Y : Set Gamma.DPath}
variable {kappa : Cardinal.{u}}
variable {C : ClubStageGeometry Gamma Y kappa (succ kappa)}
variable {globalZ seed : Set V} {z : V}
variable {Rlimit : LimitMoving931GlobalClosure C globalZ seed}
variable {T : PostClosureIntervalTransaction C globalZ seed z
  Rlimit.toDynamicMoving931GlobalClosure}

/-- Every actual assignment source has a literal interval-row edge which
leaves the closing set. -/
theorem assignmentSource_exists_intervalEdge_leaving
    (M : PostClosureMacroCompressorAssignment T)
    {x : V} (hx : x ∈ M.actualPostClosureAssignmentSources) :
    ∃ y, y ∉ Rlimit.closedSet ∧
      (x, y) ∈ familyEdges T.interval.ambientInterval := by
  have hxClosed : x ∈ Rlimit.closedSet := M.assignmentSource_mem_closedSet hx
  have hxCut : x ∈ CutSplit.initialVertices
      (outsideCarrier T.interval.ambientInterval Rlimit.closedSet)
      (outsideFamilyEdges T.interval.ambientInterval Rlimit.closedSet)
      Rlimit.closedSet := by
    have hxInitial := hx.1
    rw [M.fractured.outside.initialSet_eq] at hxInitial
    exact hxInitial
  rcases hxCut with hxExit | hxOutside
  · obtain ⟨_hxX, y, hxy⟩ := hxExit
    refine ⟨y, ?_, outsideFamilyEdges_subset
      T.interval.ambientInterval Rlimit.closedSet hxy⟩
    intro hyX
    exact hxy.2 ⟨hxClosed, hyX⟩
  · exact False.elim (hxOutside.2.1 hxClosed)

/-- The leaving interval edge at an actual assignment source is exclusive
to the forward matching against the global limiting reference. -/
theorem assignmentSource_exists_forwardExclusive
    (M : PostClosureMacroCompressorAssignment T)
    {x : V} (hx : x ∈ M.actualPostClosureAssignmentSources) :
    ∃ y, y ∉ Rlimit.closedSet ∧
      Exclusive T.interval.ambientInterval C.ladder.limitWarp x y := by
  obtain ⟨y, hyX, hxyW⟩ := M.assignmentSource_exists_intervalEdge_leaving hx
  refine ⟨y, hyX, matchingEdge_actual hxyW, ?_⟩
  rintro (hxyY | hxyIdentity)
  · simp only [familyEdges, Set.mem_iUnion] at hxyY
    obtain ⟨p, hpY, hxyP⟩ := hxyY
    have hpClosed : p.support ⊆ Rlimit.closedSet :=
      Rlimit.reference_closed p hpY
        ⟨x, (p.edgeSet_subset_support_prod hxyP).1,
          M.assignmentSource_mem_closedSet hx⟩
    exact hyX (hpClosed (p.edgeSet_subset_support_prod hxyP).2)
  · exact hyX (hxyIdentity.1 ▸ M.assignmentSource_mem_closedSet hx)

/-- Equivalently, the sending occurrence of the cut source has a genuine
first matching step whose projected head lies outside the closing set. -/
theorem assignmentSource_exists_forwardStep_leaving
    (M : PostClosureMacroCompressorAssignment T)
    {x : V} (hx : x ∈ M.actualPostClosureAssignmentSources) :
    ∃ y, y ∉ Rlimit.closedSet ∧
      Step T.interval.ambientInterval C.ladder.limitWarp
        (.inl x) (.inr y) := by
  obtain ⟨y, hyX, hxy⟩ := M.assignmentSource_exists_forwardExclusive hx
  exact ⟨y, hyX, hxy⟩

/-- The first successor port is not merely witnessed outside the closing
set: every possible matching successor of the sending occurrence has that
same outside projection.  This is the first-contact base case for the
forward-orbit cut. -/
theorem assignmentSource_successor_projects_outside
    (M : PostClosureMacroCompressorAssignment T)
    {x : V} (hx : x ∈ M.actualPostClosureAssignmentSources)
    {b : Port V}
    (hb : Step T.interval.ambientInterval C.ladder.limitWarp (.inl x) b) :
    projectPort b ∉ Rlimit.closedSet := by
  obtain ⟨y, hyX, hxy⟩ := M.assignmentSource_exists_forwardExclusive hx
  rcases step_cases hb with
    ⟨u, v, ha, hb, huv⟩ | ⟨u, v, ha, _hb, _huv⟩
  · have hu : x = u := Sum.inl.inj ha
    subst u
    have hv : v = y :=
      (matchingEdge_biUnique T.interval.ambientInterval_linkage.isWarp).2
        huv.1 hxy.1
    subst v
    rw [hb]
    exact hyX
  · cases ha

/-- Any matching step immediately preceding the sending occurrence of an
actual cut source projects to another closing-set contact.  A genuine
reference step stays in the set by global reference closure; an identity
step projects back to the source itself. -/
theorem assignmentSource_predecessor_projects_closed
    (M : PostClosureMacroCompressorAssignment T)
    {x : V} (hx : x ∈ M.actualPostClosureAssignmentSources)
    {a : Port V}
    (ha : Step T.interval.ambientInterval C.ladder.limitWarp a (.inl x)) :
    projectPort a ∈ Rlimit.closedSet := by
  rcases step_cases ha with
    ⟨u, v, _ha, hb, _huv⟩ | ⟨u, v, ha, hb, huv⟩
  · cases hb
  · have hu : x = u := Sum.inl.inj hb
    subst u
    rw [ha]
    change v ∈ Rlimit.closedSet
    rcases huv.1 with hvReference | hvIdentity
    · simp only [familyEdges, Set.mem_iUnion] at hvReference
      obtain ⟨p, hpY, hxp⟩ := hvReference
      have hpClosed : p.support ⊆ Rlimit.closedSet :=
        Rlimit.reference_closed p hpY
          ⟨x, (p.edgeSet_subset_support_prod hxp).1,
            M.assignmentSource_mem_closedSet hx⟩
      exact hpClosed (p.edgeSet_subset_support_prod hxp).2
    · exact hvIdentity.1.symm ▸ M.assignmentSource_mem_closedSet hx

/-- A predecessor of the sending occurrence is completely concrete.  It is
either a genuine global-reference edge leaving the source and staying in the
closing set, or the reference matching's identity edge at the same ambient
vertex.  Thus identity contraction is the only obstruction to treating a
source without a reference outgoing edge as unmatched. -/
theorem assignmentSource_predecessor_referenceEdge_or_identity
    (M : PostClosureMacroCompressorAssignment T)
    {x : V} (hx : x ∈ M.actualPostClosureAssignmentSources)
    {a : Port V}
    (ha : Step T.interval.ambientInterval C.ladder.limitWarp a (.inl x)) :
    (∃ y ∈ Rlimit.closedSet, a = .inr y ∧
      (x, y) ∈ familyEdges C.ladder.limitWarp) ∨ a = .inr x := by
  rcases step_cases ha with
    ⟨u, v, _ha, hb, _huv⟩ | ⟨u, v, ha, hb, huv⟩
  · cases hb
  · have hu : x = u := Sum.inl.inj hb
    subst u
    rcases huv.1 with hReference | hIdentity
    · left
      simp only [familyEdges, Set.mem_iUnion] at hReference
      obtain ⟨p, hpY, hxp⟩ := hReference
      have hpClosed : p.support ⊆ Rlimit.closedSet :=
        Rlimit.reference_closed p hpY
          ⟨x, (p.edgeSet_subset_support_prod hxp).1,
            M.assignmentSource_mem_closedSet hx⟩
      exact ⟨v, hpClosed (p.edgeSet_subset_support_prod hxp).2,
        ha, by
          simp only [familyEdges, Set.mem_iUnion]
          exact ⟨p, hpY, hxp⟩⟩
    · right
      rw [hIdentity.1]
      exact ha

/-- The actual matching source is eligible for every finite return contact
in the closing set.  This is the endpoint geometry needed when a first-return
prefix is compiled to a candidate strong imaginary edge. -/
theorem assignmentSource_hammockEligible_vertex
    (M : PostClosureMacroCompressorAssignment T)
    {x v : V} (hx : x ∈ M.actualPostClosureAssignmentSources)
    (hv : v ∈ Rlimit.closedSet) :
    HammockEligible Rlimit.closedSet C.ladder.limitStrictRoof
      C.ladder.limitRoof x (.vertex v) := by
  obtain ⟨y, _hy, hxy⟩ := M.assignmentSource_exists_intervalEdge_leaving hx
  exact T.hammockEligible_vertex_of_mem_intervalEdge Rlimit
    (M.assignmentSource_mem_closedSet hx) hxy hv

/-- The same actual matching source is eligible for a no-return infinite
component. -/
theorem assignmentSource_hammockEligible_infinity
    (M : PostClosureMacroCompressorAssignment T)
    {x : V} (hx : x ∈ M.actualPostClosureAssignmentSources) :
    HammockEligible Rlimit.closedSet C.ladder.limitStrictRoof
      C.ladder.limitRoof x .infinity := by
  obtain ⟨y, _hy, hxy⟩ := M.assignmentSource_exists_intervalEdge_leaving hx
  exact T.hammockEligible_infinity_of_mem_intervalEdge Rlimit
    (M.assignmentSource_mem_closedSet hx) hxy

/-- If the sending occurrence of an actual source has no predecessor in
the symmetric-difference traversal, the existing generic traversal theorem
may be applied there.  The hypothesis is kept explicit because it is false
for a general internal cut source. -/
theorem exists_matchingTraversal_of_assignmentSource_of_unmatched
    (M : PostClosureMacroCompressorAssignment T)
    {x : V} (hx : x ∈ M.actualPostClosureAssignmentSources)
    (hunmatched : ¬ ∃ y,
      Exclusive C.ladder.limitWarp T.interval.ambientInterval x y) :
    Nonempty (Traversal T.interval.ambientInterval C.ladder.limitWarp x) := by
  obtain ⟨y, _hyX, hxy⟩ := M.assignmentSource_exists_forwardExclusive hx
  exact exists_traversal T.interval.ambientInterval_linkage.isWarp
    (C.legal.warpStages (Ladder.finalStage (succ kappa))) x
    ⟨y, hxy⟩ hunmatched

#print axioms assignmentSource_exists_intervalEdge_leaving
#print axioms assignmentSource_exists_forwardExclusive
#print axioms assignmentSource_exists_forwardStep_leaving
#print axioms assignmentSource_successor_projects_outside
#print axioms assignmentSource_predecessor_projects_closed
#print axioms assignmentSource_predecessor_referenceEdge_or_identity
#print axioms assignmentSource_hammockEligible_vertex
#print axioms assignmentSource_hammockEligible_infinity
#print axioms exists_matchingTraversal_of_assignmentSource_of_unmatched

end Erdos599.Blueprint.LinkageBlueprint.PostClosureMacroCompressorAssignment
