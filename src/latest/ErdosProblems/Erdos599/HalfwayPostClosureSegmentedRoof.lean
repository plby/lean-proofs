/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.HalfwayPostClosureSegmentedCardinality
import ErdosProblems.Erdos599.SliceRestrictedDelta

/-!
# Captured-roof containment of the actual segmented carrier

The finite interval reference has pure target boundary and starts below the
captured frontier, so it is roofed there.  Every forward assigned link lies
on the captured interval row, and every backward link lies on that interval
reference.  Thus the actual assignment carrier is roofed at the same later
stage.  No containment of the future residual linkage in the prior closing
set is assumed.
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

namespace PostClosureIntervalTransaction

/-- The actual canonical reference intervals lie under the captured later
frontier, independently of whether they are retained in the future row. -/
theorem intervalReference_vertices_subset_capturedRoof
    (T : PostClosureIntervalTransaction C globalZ seed z
      Rlimit.toDynamicMoving931GlobalClosure) :
    Gamma.vertexSet T.intervalReference ⊆ Rlimit.capturedGeometry.outerRoof := by
  apply CardinalInduction.SliceRestrictedDelta.linkage_vertexSet_subset_roof_of_initial
    Gamma T.intervalReference_isLinkageBetween
  · intro x hx
    exact C.legal.frontierChronology Rlimit.later.current_lt hx.1
  · exact T.intervalReference_target_pure

end PostClosureIntervalTransaction

namespace PostClosureCompressorAssignment

/-- Both directions of an actual assigned link stay in the later roof.
Forward links use the ambient row; backward links use the distinct local
interval reference. -/
theorem assigned_link_support_subset_capturedRoof
    (A : PostClosureCompressorAssignment T)
    (s : {x // x ∈ Gamma.initialSet A.fractured.outside.holes.paths \
      Gamma.initialSet (outsideReference T.intervalReference Rlimit.closedSet)})
    (l : Link Gamma.graph)
    (hl : l ∈ (A.assignment.produced.bracket.assignment.assigned s).links) :
    l.path.support ⊆ Rlimit.capturedGeometry.outerRoof := by
  have hrow : Gamma.vertexSet T.interval.ambientInterval ⊆
      Rlimit.capturedGeometry.outerRoof := by
    rintro x ⟨p, hp, hxp⟩
    exact T.interval.ambientInterval_in_outerRoof p hp hxp
  cases hd : l.direction with
  | forward =>
      have he := A.toPostClosureProducedAssignment
        |>.assigned_forwardLink_edges_subset_intervalFamily s l hl hd
      intro x hx
      by_cases hstart : x = l.path.start
      · subst x
        obtain ⟨v, hv⟩ :=
          Alternating.FinitePath.exists_outgoing_edge_of_mem_support_of_ne_finish
            l.path l.path.start_mem_support l.nontrivial
        exact hrow ((familyEdges_subset_vertexSet_prod
          T.interval.ambientInterval (he hv)).1)
      · obtain ⟨v, hv⟩ :=
          Alternating.FinitePath.exists_incoming_edge_of_mem_support_of_ne_start
            l.path hx hstart
        exact hrow ((familyEdges_subset_vertexSet_prod
          T.interval.ambientInterval (he hv)).2)
  | backward =>
      obtain ⟨p, hp, hsub⟩ :=
        (A.assignment.produced.bracket.bracket_safe s).isAlternating.2.1 l hl hd
      intro x hx
      exact T.intervalReference_vertices_subset_capturedRoof
        ⟨p, hp.1, hsub.1 hx⟩

/-- Every actual assigned trace, including its singleton branch, is roofed
at the captured later stage. -/
theorem assigned_vertices_subset_capturedRoof
    (A : PostClosureCompressorAssignment T)
    (s : {x // x ∈ Gamma.initialSet A.fractured.outside.holes.paths \
      Gamma.initialSet (outsideReference T.intervalReference Rlimit.closedSet)}) :
    (A.assignment.produced.bracket.assignment.assigned s).vertexSet ⊆
      Rlimit.capturedGeometry.outerRoof := by
  cases hQ : A.assignment.produced.bracket.assignment.assigned s with
  | trivial x =>
      intro v hv
      have hvx : v = x := by simpa only [AltPath.vertexSet, Set.mem_singleton_iff] using hv
      subst v
      have hstart := A.assignment.produced.bracket.assignment.starts_at s
      rw [hQ] at hstart
      change x = s.1 at hstart
      exact Rlimit.later.subset_roof
        (hstart ▸ T.uncovered_initials_subset_closedSet Rlimit A.fractured s.2)
  | finite Q =>
      intro x hx
      obtain ⟨i, hxi⟩ := Set.mem_iUnion.1 hx
      exact A.assigned_link_support_subset_capturedRoof s (Q.link i)
        (by rw [hQ]; exact ⟨i, rfl⟩) hxi
  | infinite Q =>
      intro x hx
      obtain ⟨i, hxi⟩ := Set.mem_iUnion.1 hx
      exact A.assigned_link_support_subset_capturedRoof s (Q.link i)
        (by rw [hQ]; exact ⟨i, rfl⟩) hxi

theorem actualAssignedVertices_subset_capturedRoof
    (A : PostClosureCompressorAssignment T) :
    A.actualAssignedVertices ⊆ Rlimit.capturedGeometry.outerRoof := by
  intro x hx
  obtain ⟨s, hs⟩ := Set.mem_iUnion.1 hx
  exact A.assigned_vertices_subset_capturedRoof s hs

/-- The same explicit carrier that has the proved cardinal bound also
satisfies the later-stage roof condition. -/
theorem actualPostClosureFreshCarrier_subset_capturedRoof
    (A : PostClosureCompressorAssignment T) :
    A.actualPostClosureFreshCarrier ⊆ Rlimit.capturedGeometry.outerRoof := by
  intro x hx
  rcases hx with hclosed | hassigned
  · exact Rlimit.later.subset_roof hclosed
  · exact A.actualAssignedVertices_subset_capturedRoof hassigned

/-- Old blueprint vertices remain roofed at the captured later frontier;
adding the actual fresh carrier therefore preserves the roof condition. -/
theorem current_union_actualPostClosureFreshCarrier_subset_capturedRoof
    (A : PostClosureCompressorAssignment T)
    (current : LinkageBlueprint Gamma C.ladder.limitWarp kappa)
    {currentClosed : Set V}
    (hcurrent : current.IsLinkageBlueprint
      C.newSlice currentClosed C.persistent) :
    current.vertexSet ∪ A.actualPostClosureFreshCarrier ⊆
      Rlimit.capturedGeometry.outerRoof := by
  intro x hx
  rcases hx with hold | hfresh
  · exact Gamma.roof_cut (C.legal.frontierChronology Rlimit.later.current_lt)
      (hcurrent.vertices_roofed hold)
  · exact A.actualPostClosureFreshCarrier_subset_capturedRoof hfresh

#print axioms assigned_vertices_subset_capturedRoof
#print axioms actualPostClosureFreshCarrier_subset_capturedRoof
#print axioms current_union_actualPostClosureFreshCarrier_subset_capturedRoof

end PostClosureCompressorAssignment
end Erdos599.Blueprint.LinkageBlueprint
