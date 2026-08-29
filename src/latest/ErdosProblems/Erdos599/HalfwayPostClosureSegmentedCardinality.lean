/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.HalfwayPostClosureOldRoofIncidence

/-!
# Cardinal bounds for the actual segmented post-closure relation

Every uncovered fractured source belongs to the already chosen closing set.
There are therefore at most `kappa` actual assigned paths, each with a
countable vertex set.  Their union, together with the inside restriction,
has cardinality at most `kappa`.  These bounds require neither disjointness
of projected assignments nor a future relation-compatibility certificate.
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599.Blueprint.LinkageBlueprint

open DirectedPath _root_.Erdos599.Alternating

universe u

variable {V : Type u} {Gamma : DWeb V} {Y : Set Gamma.DPath}
variable {kappa : Cardinal.{u}}
variable {C : ClubStageGeometry Gamma Y kappa (succ kappa)}
variable {globalZ seed : Set V} {z : V}
variable {Rlimit : LimitMoving931GlobalClosure C globalZ seed}
variable {T : PostClosureIntervalTransaction C globalZ seed z
  Rlimit.toDynamicMoving931GlobalClosure}

namespace ClosedClassifiedContactSegmentation

/-- Every endpoint of a retained edge is an actual trace vertex, including
the endpoint pairs of imaginary shortcuts. -/
theorem retainedEdges_subset_vertexSet_prod
    {Q : AltPath Gamma.graph} {X persistent : Set V}
    (S : ClosedClassifiedContactSegmentation
      (Y := Y) (kappa := kappa) Q X persistent) :
    S.retainedEdges ⊆ Q.vertexSet ×ˢ Q.vertexSet := by
  intro e he
  rcases S.retainedEdges_subset_originalForward_union_shortcut he with
      hforward | hshortcut
  · simp only [AltPath.directionEdges, Set.mem_iUnion] at hforward
    obtain ⟨l, hl, _hdir, he⟩ := hforward
    have hend := l.path.edgeSet_subset_support_prod he
    exact ⟨Q.link_support_subset_vertexSet hl hend.1,
      Q.link_support_subset_vertexSet hl hend.2⟩
  · have hend := S.endpoints_mem_contactSet hshortcut
    exact ⟨S.contactSet_subset_vertexSet hend.1,
      S.contactSet_subset_vertexSet hend.2⟩

end ClosedClassifiedContactSegmentation

namespace PostClosureCompressorAssignment

/-- All assigned trace vertices, without identifying distinct fractured
sources whose projections might meet. -/
def actualAssignedVertices (A : PostClosureCompressorAssignment T) : Set V :=
  ⋃ s, (A.assignment.produced.bracket.assignment.assigned s).vertexSet

/-- Source absorption gives the actual assignment-index bound. -/
theorem mk_actualSources_le (A : PostClosureCompressorAssignment T) :
    #(Gamma.initialSet A.fractured.outside.holes.paths \
      Gamma.initialSet (outsideReference T.intervalReference Rlimit.closedSet) : Set V) ≤
        kappa :=
  (Cardinal.mk_subtype_mono
    (T.uncovered_initials_subset_closedSet Rlimit A.fractured)).trans Rlimit.card_le

/-- A union of at most `kappa` countable traces has at most `kappa`
vertices, even when distinct projected paths have contacts in common. -/
theorem mk_actualAssignedVertices_le (A : PostClosureCompressorAssignment T) :
    #A.actualAssignedVertices ≤ kappa := by
  apply (Cardinal.mk_iUnion_le _).trans
  apply Cardinal.mul_le_of_le C.capacity_infinite A.mk_actualSources_le
  apply ciSup_le'
  intro s
  exact (altPath_vertexSet_countable
    (A.assignment.produced.bracket.assignment.assigned s)).le_aleph0.trans
      C.capacity_infinite

/-- Every retained outside edge has both endpoints in the actual assignment
carrier, independently of cross-source bi-uniqueness. -/
theorem actualSegmentedRetainedEdges_subset_assignedVertices_prod
    (A : PostClosureCompressorAssignment T) :
    A.actualSegmentedRetainedEdges ⊆
      A.actualAssignedVertices ×ˢ A.actualAssignedVertices := by
  intro e he
  obtain ⟨s, hs⟩ := Set.mem_iUnion.1 he
  have hend :=
    (A.actualClosedClassifiedContactSegmentation s).retainedEdges_subset_vertexSet_prod hs
  exact ⟨Set.mem_iUnion.2 ⟨s, hend.1⟩,
    Set.mem_iUnion.2 ⟨s, hend.2⟩⟩

/-- A small explicit carrier for all actual fresh edges.  The closing set
also retains singleton inside vertices which need not be edge endpoints. -/
def actualPostClosureFreshCarrier
    (A : PostClosureCompressorAssignment T) : Set V :=
  Rlimit.closedSet ∪ A.actualAssignedVertices

theorem mk_actualPostClosureFreshCarrier_le
    (A : PostClosureCompressorAssignment T) :
    #A.actualPostClosureFreshCarrier ≤ kappa :=
  (Cardinal.mk_union_le Rlimit.closedSet A.actualAssignedVertices).trans
    (Cardinal.add_le_of_le C.capacity_infinite Rlimit.card_le
      A.mk_actualAssignedVertices_le)

theorem actualPostClosureFreshEdges_subset_freshCarrier_prod
    (A : PostClosureCompressorAssignment T) :
    A.actualPostClosureFreshEdges ⊆
      A.actualPostClosureFreshCarrier ×ˢ A.actualPostClosureFreshCarrier := by
  intro e he
  rcases he with hinside | houtside
  · exact ⟨Or.inl hinside.2.1, Or.inl hinside.2.2⟩
  · have hend := A.actualSegmentedRetainedEdges_subset_assignedVertices_prod houtside
    exact ⟨Or.inr hend.1, Or.inr hend.2⟩

/-- Adjoining a current blueprint of the prescribed capacity keeps the
whole explicit transaction carrier small. -/
theorem mk_current_union_actualPostClosureFreshCarrier_le
    (A : PostClosureCompressorAssignment T)
    (current : LinkageBlueprint Gamma C.ladder.limitWarp kappa)
    {currentClosed : Set V}
    (hcurrent : current.IsLinkageBlueprint
      C.newSlice currentClosed C.persistent) :
    #(current.vertexSet ∪ A.actualPostClosureFreshCarrier : Set V) ≤ kappa :=
  (Cardinal.mk_union_le current.vertexSet A.actualPostClosureFreshCarrier).trans
    (Cardinal.add_le_of_le C.capacity_infinite
      (current.mk_vertexSet_le_of_mk_paths_le C.capacity_infinite hcurrent.card_paths)
      A.mk_actualPostClosureFreshCarrier_le)

#print axioms mk_actualAssignedVertices_le
#print axioms actualPostClosureFreshEdges_subset_freshCarrier_prod
#print axioms mk_current_union_actualPostClosureFreshCarrier_le

end PostClosureCompressorAssignment
end Erdos599.Blueprint.LinkageBlueprint
