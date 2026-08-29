/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.HalfwayPostClosureMatchingOrbit
import ErdosProblems.Erdos599.HalfwayIntervalGlobalReferenceEmbedding
import ErdosProblems.Erdos599.HalfwayPostClosureIntervalReferenceEndpointExclusion

/-!
# The actual matching orbit against the finite interval reference

The fractured assignment is constructed against the finite captured
`intervalReference`.  Its members embed in the limiting warp, so reference
closure still proves that the literal leaving row edge is exclusive.  This
gives the endpoint-aligned local matching orbit without identifying global
marker endpoints with interval-row endpoints.
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

/-- The actual cut-source edge is also exclusive against the finite local
interval reference.  Any local reference edge is an edge of its limiting
owner and would force both endpoints into the reference-closed set. -/
theorem assignmentSource_exists_localForwardExclusive
    (M : PostClosureMacroCompressorAssignment T)
    {x : V} (hx : x ∈ M.actualPostClosureAssignmentSources) :
    ∃ y, y ∉ Rlimit.closedSet ∧
      Exclusive T.interval.ambientInterval T.intervalReference x y := by
  obtain ⟨y, hyOutside, hxyRow⟩ :=
    M.assignmentSource_exists_intervalEdge_leaving hx
  refine ⟨y, hyOutside, matchingEdge_actual hxyRow, ?_⟩
  rintro (hxyReference | hxyIdentity)
  · have hxyGlobal : (x, y) ∈ familyEdges C.ladder.limitWarp :=
      T.intervalGlobalReferenceEmbedding.familyEdges_subset hxyReference
    simp only [familyEdges, Set.mem_iUnion] at hxyGlobal
    obtain ⟨p, hpGlobal, hpxy⟩ := hxyGlobal
    have hpClosed : p.support ⊆ Rlimit.closedSet :=
      Rlimit.reference_closed p hpGlobal
        ⟨x, (p.edgeSet_subset_support_prod hpxy).1,
          M.assignmentSource_mem_closedSet hx⟩
    exact hyOutside (hpClosed (p.edgeSet_subset_support_prod hpxy).2)
  · exact hyOutside (hxyIdentity.1 ▸ M.assignmentSource_mem_closedSet hx)

/-- Sending the actual cut source therefore starts a genuine local
two-warp matching step. -/
theorem assignmentSource_exists_localForwardStep_leaving
    (M : PostClosureMacroCompressorAssignment T)
    {x : V} (hx : x ∈ M.actualPostClosureAssignmentSources) :
    ∃ y, y ∉ Rlimit.closedSet ∧
      Step T.interval.ambientInterval T.intervalReference
        (.inl x) (.inr y) := by
  obtain ⟨y, hy, hxy⟩ := M.assignmentSource_exists_localForwardExclusive hx
  exact ⟨y, hy, hxy⟩

/-- The complete honest first-return/stopped/infinite alternative for the
endpoint-aligned finite interval reference. -/
theorem exists_actualLocalForwardOrbitOutcome
    (M : PostClosureMacroCompressorAssignment T)
    {x : V} (hx : x ∈ M.actualPostClosureAssignmentSources) :
    Nonempty (ForwardOrbitOutcome T.interval.ambientInterval
      T.intervalReference Rlimit.closedSet x) := by
  apply exists_forwardOrbitOutcome
    T.interval.ambientInterval_linkage.isWarp
    T.intervalReference_isLinkageBetween.isWarp
    (M.assignmentSource_mem_closedSet hx)
  obtain ⟨y, _hy, hxy⟩ :=
    M.assignmentSource_exists_localForwardStep_leaving hx
  exact ⟨.inr y, hxy⟩

/-- The exact local reference of the fractured assignment consists only of
interval-reference members disjoint from the closed set.  Thus its outgoing
matching step is exclusive without any exposed contact at the cut source. -/
theorem assignmentSource_exists_outsideLocalForwardExclusive
    (M : PostClosureMacroCompressorAssignment T)
    {x : V} (hx : x ∈ M.actualPostClosureAssignmentSources) :
    ∃ y, y ∉ Rlimit.closedSet ∧
      Exclusive T.interval.ambientInterval
        (outsideReference T.intervalReference Rlimit.closedSet) x y := by
  obtain ⟨y, hyOutside, hxyRow⟩ :=
    M.assignmentSource_exists_intervalEdge_leaving hx
  refine ⟨y, hyOutside, matchingEdge_actual hxyRow, ?_⟩
  rintro (hxyReference | hxyIdentity)
  · simp only [familyEdges, Set.mem_iUnion] at hxyReference
    obtain ⟨p, hpOutside, hpxy⟩ := hxyReference
    exact Set.disjoint_left.1 hpOutside.2
      (p.edgeSet_subset_support_prod hpxy).1
      (M.assignmentSource_mem_closedSet hx)
  · exact hyOutside (hxyIdentity.1 ▸ M.assignmentSource_mem_closedSet hx)

/-- Every outside-local matching successor of the sending cut occurrence is
the same literal row head, hence lies outside the closed set. -/
theorem assignmentSource_outsideLocal_successor_projects_outside
    (M : PostClosureMacroCompressorAssignment T)
    {x : V} (hx : x ∈ M.actualPostClosureAssignmentSources)
    {b : Port V}
    (hb : Step T.interval.ambientInterval
      (outsideReference T.intervalReference Rlimit.closedSet) (.inl x) b) :
    projectPort b ∉ Rlimit.closedSet := by
  obtain ⟨y, hyOutside, hxy⟩ :=
    M.assignmentSource_exists_outsideLocalForwardExclusive hx
  rcases step_cases hb with
    ⟨u, v, ha, hb, huv⟩ | ⟨u, v, ha, _hb, _huv⟩
  · have hu : x = u := Sum.inl.inj ha
    subst u
    have hv : v = y :=
      (matchingEdge_biUnique T.interval.ambientInterval_linkage.isWarp).2
        huv.1 hxy.1
    subst v
    rw [hb]
    exact hyOutside
  · cases ha

/-- The source-faithful matching orbit: both finite-return endpoints lie
off this reference, while every interior reference contact is represented
by the literal two-matching traversal. -/
theorem exists_actualOutsideLocalForwardOrbitOutcome
    (M : PostClosureMacroCompressorAssignment T)
    {x : V} (hx : x ∈ M.actualPostClosureAssignmentSources) :
    Nonempty (ForwardOrbitOutcome T.interval.ambientInterval
      (outsideReference T.intervalReference Rlimit.closedSet)
      Rlimit.closedSet x) := by
  apply exists_forwardOrbitOutcome
    T.interval.ambientInterval_linkage.isWarp
    (T.intervalReference_isLinkageBetween.isWarp.subset
      (outsideReference_subset
        (Y := T.intervalReference) (X := Rlimit.closedSet)))
    (M.assignmentSource_mem_closedSet hx)
  obtain ⟨y, _hy, hxy⟩ :=
    M.assignmentSource_exists_outsideLocalForwardExclusive hx
  exact ⟨.inr y, hxy⟩

/-- A distinct first return of the exact outside-local orbit has the root
uniqueness required by its finite chronological-erasure compiler. -/
theorem actualOutsideLocalFirstReturn_projectedRoot_unique
    (M : PostClosureMacroCompressorAssignment T)
    {x : V} (hx : x ∈ M.actualPostClosureAssignmentSources)
    (P : FinitePortPrefix T.interval.ambientInterval
      (outsideReference T.intervalReference Rlimit.closedSet) x)
    (hinterior : ∀ i : Fin (P.lastIndex + 1),
      0 < i.1 → i.1 < P.lastIndex →
        P.projectedVertex i ∉ Rlimit.closedSet)
    (hterminal : P.projectedVertex
      ⟨P.lastIndex, Nat.lt_succ_self _⟩ ≠ x) :
    ∀ i, P.projectedVertex i = P.projectedVertex 0 → i.1 = 0 := by
  exact P.projectedRoot_unique_of_first_return
    (M.assignmentSource_mem_closedSet hx) hinterior hterminal

/-- Endpoint eligibility is independent of the reference used to expose
the actual matching orbit. -/
theorem actualOutsideLocalFirstReturn_hammockEligible
    (M : PostClosureMacroCompressorAssignment T)
    {x : V} (hx : x ∈ M.actualPostClosureAssignmentSources)
    (P : FinitePortPrefix T.interval.ambientInterval
      (outsideReference T.intervalReference Rlimit.closedSet) x)
    (hterminal : P.projectedVertex
      ⟨P.lastIndex, Nat.lt_succ_self _⟩ ∈ Rlimit.closedSet) :
    HammockEligible Rlimit.closedSet C.ladder.limitStrictRoof
      C.ladder.limitRoof x
        (.vertex (P.projectedVertex
          ⟨P.lastIndex, Nat.lt_succ_self _⟩)) := by
  exact M.assignmentSource_hammockEligible_vertex hx hterminal

/-- Infinite-end eligibility for the exact outside-local no-return orbit. -/
theorem actualOutsideLocalInfinite_hammockEligible
    (M : PostClosureMacroCompressorAssignment T)
    {x : V} (hx : x ∈ M.actualPostClosureAssignmentSources)
    (_P : InfinitePortPrefix T.interval.ambientInterval
      (outsideReference T.intervalReference Rlimit.closedSet) x) :
    HammockEligible Rlimit.closedSet C.ladder.limitStrictRoof
      C.ladder.limitRoof x .infinity :=
  M.assignmentSource_hammockEligible_infinity hx

#print axioms assignmentSource_exists_localForwardExclusive
#print axioms assignmentSource_exists_localForwardStep_leaving
#print axioms exists_actualLocalForwardOrbitOutcome
#print axioms assignmentSource_exists_outsideLocalForwardExclusive
#print axioms assignmentSource_outsideLocal_successor_projects_outside
#print axioms exists_actualOutsideLocalForwardOrbitOutcome
#print axioms actualOutsideLocalFirstReturn_projectedRoot_unique
#print axioms actualOutsideLocalFirstReturn_hammockEligible
#print axioms actualOutsideLocalInfinite_hammockEligible

end Erdos599.Blueprint.LinkageBlueprint.PostClosureMacroCompressorAssignment
