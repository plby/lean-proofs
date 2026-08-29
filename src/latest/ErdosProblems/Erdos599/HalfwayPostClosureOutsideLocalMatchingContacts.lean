/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.HalfwayPostClosureLocalMatchingOrbit
import ErdosProblems.Erdos599.TwoWarpMatchingPrefixContacts

/-!
# Literal contact coverage in the actual outside-local matching orbit

The exact reference used by the fractured assignment is the subfamily of
captured interval-reference paths disjoint from the closed set.  Therefore
both exposed contacts of a first-return orbit lie outside its carrier.  The
captured interval boundary also rules out the two wrong-parity endpoint
cases for every literal ambient-row edge.  The generic prefix contact
theorem then proves that every remaining forward/reference contact is
represented by an adjacent backward matching step before projection.
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

private theorem closed_not_mem_outsideReference_vertexSet
    {x : V} (hx : x ∈ Rlimit.closedSet) :
    x ∉ Gamma.vertexSet
      (outsideReference T.intervalReference Rlimit.closedSet) := by
  intro hxout
  exact Set.disjoint_left.1
    (vertexSet_outsideReference_disjoint
      (Gamma := Gamma) (Y := T.intervalReference)
      (X := Rlimit.closedSet)) hxout hx

/-- Every endpoint contact of every literal forward step of an actual
finite first-return prefix is covered by an adjacent outside-reference step.
This is a pre-projection statement. -/
theorem outsideLocalFinite_forward_vertex_contacts_covered
    (M : PostClosureMacroCompressorAssignment T)
    {x : V} (hx : x ∈ M.actualPostClosureAssignmentSources)
    (P : FinitePortPrefix T.interval.ambientInterval
      (outsideReference T.intervalReference Rlimit.closedSet) x)
    (hterminal : P.projectedVertex
      ⟨P.lastIndex, Nat.lt_succ_self _⟩ ∈ Rlimit.closedSet)
    (i : Fin P.lastIndex) {a b : V}
    (hleft : P.port i.castSucc = .inl a)
    (hright : P.port i.succ = .inr b)
    (hab : (a, b) ∈ familyEdges T.interval.ambientInterval) :
    (a ∈ Gamma.vertexSet
        (outsideReference T.intervalReference Rlimit.closedSet) →
      P.ReferenceCovered (.inl a)) ∧
    (b ∈ Gamma.vertexSet
        (outsideReference T.intervalReference Rlimit.closedSet) →
      P.ReferenceCovered (.inr b)) := by
  apply P.forward_vertex_contacts_covered
    T.interval.ambientInterval_linkage.isWarp
    (outsideReference_isWarp T.intervalReference_isLinkageBetween.isWarp)
  · exact closed_not_mem_outsideReference_vertexSet
      (M.assignmentSource_mem_closedSet hx)
  · exact closed_not_mem_outsideReference_vertexSet hterminal
  · exact hleft
  · exact hright
  · exact T.ambientInterval_edge_tail_not_mem_outsideIntervalReference_terminalFrontier
      hab
  · exact T.ambientInterval_edge_head_not_mem_outsideIntervalReference_initialSet
      hab

/-- Infinite no-return analogue: the only exposed endpoint is its root,
which lies in the closed set and hence outside the outside reference. -/
theorem outsideLocalInfinite_forward_vertex_contacts_covered
    (M : PostClosureMacroCompressorAssignment T)
    {x : V} (hx : x ∈ M.actualPostClosureAssignmentSources)
    (P : InfinitePortPrefix T.interval.ambientInterval
      (outsideReference T.intervalReference Rlimit.closedSet) x)
    (i : Nat) {a b : V}
    (hleft : P.port i = .inl a)
    (hright : P.port (i + 1) = .inr b)
    (hab : (a, b) ∈ familyEdges T.interval.ambientInterval) :
    (a ∈ Gamma.vertexSet
        (outsideReference T.intervalReference Rlimit.closedSet) →
      P.ReferenceCovered (.inl a)) ∧
    (b ∈ Gamma.vertexSet
        (outsideReference T.intervalReference Rlimit.closedSet) →
      P.ReferenceCovered (.inr b)) := by
  apply P.forward_vertex_contacts_covered
    T.interval.ambientInterval_linkage.isWarp
    (outsideReference_isWarp T.intervalReference_isLinkageBetween.isWarp)
  · exact closed_not_mem_outsideReference_vertexSet
      (M.assignmentSource_mem_closedSet hx)
  · exact hleft
  · exact hright
  · exact T.ambientInterval_edge_tail_not_mem_outsideIntervalReference_terminalFrontier
      hab
  · exact T.ambientInterval_edge_head_not_mem_outsideIntervalReference_initialSet
      hab

#print axioms outsideLocalFinite_forward_vertex_contacts_covered
#print axioms outsideLocalInfinite_forward_vertex_contacts_covered

end Erdos599.Blueprint.LinkageBlueprint.PostClosureMacroCompressorAssignment
