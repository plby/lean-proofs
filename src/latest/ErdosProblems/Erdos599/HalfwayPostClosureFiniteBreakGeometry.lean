/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.HalfwayPostClosureFiniteInternalSafety
import ErdosProblems.Erdos599.HalfwayPostClosureContactEligibility
import ErdosProblems.Erdos599.HalfwayPostClosureAssignedLinkGeometry
import ErdosProblems.Erdos599.HalfwayFiniteRunWalkOccurrenceOrder
import ErdosProblems.Erdos599.HalfwayFiniteInputDirectionEdgeCoverage

/-!
# Concrete geometry of finite post-closure break intervals

Once the two endpoints of an actual finite assignment have been absorbed by
the closing set, every displayed break point lies in that set.  Backward
links avoid it, so the raw edge leaving each nonfinal break point is forward
and hence is a literal edge of the later interval row.  This supplies the
finite hammock eligibility required by Claim 2.
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599.Alternating

open DirectedPath

universe u

variable {V : Type u} {D : Digraph V}

namespace FiniteRunWalk

theorem breakPoint_mem_of_endpoints_mem
    (W : FiniteRunWalk D) (X : Set V)
    (hinitial : W.vertex 0 ∈ X)
    (hterminal : W.vertex W.finalPosition ∈ X)
    (i : Fin (W.breakCount X + 1)) :
    W.breakPoint X i ∈ X := by
  rcases W.breakPosition_endpoint_or_mem X i with hzero | hfinal | hmem
  · simpa [breakPoint, hzero] using hinitial
  · simpa [breakPoint, hfinal] using hterminal
  · exact hmem

end FiniteRunWalk

namespace RunCompressor.FiniteInput

/-- At a closing-set vertex the outgoing raw coordinate cannot be backward,
because every backward link of the parent trace avoids the closing set. -/
theorem colour_eq_forward_of_vertex_mem
    (S : FiniteInput D) (X : Set V)
    (hbackwardOff : ∀ l ∈ (AltPath.finite
        S.toFiniteRunWalk.toFiniteTrace).links,
      l.direction = .backward → Disjoint l.path.support X)
    (k : Fin S.lastEdge) (hkX : S.vertex k.1 ∈ X) :
    S.colour k = .forward := by
  cases hcolour : S.colour k with
  | forward => rfl
  | backward =>
      have hraw := S.rawEdge_mem_directionEdges k
      rw [hcolour] at hraw
      simp only [AltPath.directionEdges, Set.mem_iUnion] at hraw
      obtain ⟨l, hl, hdir, he⟩ := hraw
      have hkSupport : S.vertex k.1 ∈ l.path.support := by
        have := (l.path.edgeSet_subset_support_prod he).2
        simpa only [rawEdge, hcolour] using this
      exact False.elim
        (Set.disjoint_left.1 (hbackwardOff l hl hdir) hkSupport hkX)

end RunCompressor.FiniteInput
end Erdos599.Alternating

namespace Erdos599.Blueprint.LinkageBlueprint.PostClosureCompressorAssignment

open DirectedPath _root_.Erdos599.Alternating

universe u

variable {V : Type u} {Gamma : DWeb V} {Y : Set Gamma.DPath}
variable {kappa : Cardinal.{u}}
variable {C : ClubStageGeometry Gamma Y kappa (succ kappa)}
variable {globalZ seed : Set V} {z : V}
variable {Rlimit : LimitMoving931GlobalClosure C globalZ seed}
variable {T : PostClosureIntervalTransaction C globalZ seed z
  Rlimit.toDynamicMoving931GlobalClosure}

theorem finite_rawEdge_mem_intervalFamily
    (A : PostClosureCompressorAssignment T)
    (s : {x // x ∈ Gamma.initialSet A.fractured.outside.holes.paths \
      Gamma.initialSet (outsideReference T.intervalReference Rlimit.closedSet)})
    (S : RunCompressor.FiniteInput Gamma.graph)
    (hS : A.assignment.produced.bracket.assignment.assigned s =
      .finite S.toFiniteRunWalk.toFiniteTrace)
    (k : Fin S.lastEdge) (hkX : S.vertex k.1 ∈ Rlimit.closedSet) :
    (S.vertex k.1, S.vertex (k.1 + 1)) ∈
      familyEdges T.interval.ambientInterval := by
  have hbackwardOff : ∀ l ∈ (AltPath.finite
      S.toFiniteRunWalk.toFiniteTrace).links,
      l.direction = .backward → Disjoint l.path.support Rlimit.closedSet := by
    intro l hl hdir
    apply A.toPostClosureProducedAssignment.assigned_backwardLink_disjoint_closedSet
      s l
    · rw [hS]
      exact hl
    · exact hdir
  have hcolour : S.colour k = .forward :=
    S.colour_eq_forward_of_vertex_mem Rlimit.closedSet hbackwardOff k hkX
  have hraw := S.rawEdge_mem_directionEdges k
  rw [hcolour] at hraw
  simp only [AltPath.directionEdges, Set.mem_iUnion] at hraw
  obtain ⟨l, hl, hdir, he⟩ := hraw
  have hrow :=
    A.toPostClosureProducedAssignment.assigned_forwardLink_edges_subset_intervalFamily
      s l (by rw [hS]; exact hl) hdir he
  simpa only [RunCompressor.FiniteInput.rawEdge, hcolour] using hrow

/-- If the two actual assignment endpoints have been absorbed, every finite
contact interval has precisely the endpoint eligibility required by the
global closing hammock. -/
theorem finite_breakInterval_hammockEligible
    (A : PostClosureCompressorAssignment T)
    (s : {x // x ∈ Gamma.initialSet A.fractured.outside.holes.paths \
      Gamma.initialSet (outsideReference T.intervalReference Rlimit.closedSet)})
    (S : RunCompressor.FiniteInput Gamma.graph)
    (hS : A.assignment.produced.bracket.assignment.assigned s =
      .finite S.toFiniteRunWalk.toFiniteTrace)
    (hinitial : S.vertex 0 ∈ Rlimit.closedSet)
    (hterminal : S.vertex S.lastEdge ∈ Rlimit.closedSet)
    (i : Fin (S.finiteWalk.breakCount Rlimit.closedSet)) :
    HammockEligible Rlimit.closedSet C.ladder.limitStrictRoof
      C.ladder.limitRoof
      (S.finiteWalk.breakPoint Rlimit.closedSet i.castSucc)
      (.vertex (S.finiteWalk.breakPoint Rlimit.closedSet i.succ)) := by
  have huX : S.finiteWalk.breakPoint Rlimit.closedSet i.castSucc ∈
      Rlimit.closedSet := by
    apply S.finiteWalk.breakPoint_mem_of_endpoints_mem Rlimit.closedSet
    · exact hinitial
    · rw [S.finiteWalk_finalPosition]
      exact hterminal
  have hvX : S.finiteWalk.breakPoint Rlimit.closedSet i.succ ∈
      Rlimit.closedSet := by
    apply S.finiteWalk.breakPoint_mem_of_endpoints_mem Rlimit.closedSet
    · exact hinitial
    · rw [S.finiteWalk_finalPosition]
      exact hterminal
  let k : Fin S.lastEdge :=
    ⟨S.finiteWalk.breakPosition Rlimit.closedSet i.castSucc, by
      have hlt := S.finiteWalk.consecutiveBreak_position_lt
        Rlimit.closedSet i
      have hle := S.finiteWalk.breakPosition_le_final
        Rlimit.closedSet i.succ
      rw [S.finiteWalk_finalPosition] at hle
      omega⟩
  have huX' : S.vertex k.1 ∈ Rlimit.closedSet := by
    change S.vertex
      (S.finiteWalk.breakPosition Rlimit.closedSet i.castSucc) ∈
        Rlimit.closedSet
    exact huX
  have hedge := A.finite_rawEdge_mem_intervalFamily s S hS k huX'
  apply T.hammockEligible_vertex_of_mem_intervalEdge Rlimit huX
    (w := S.vertex (k.1 + 1))
  · change (S.vertex
        (S.finiteWalk.breakPosition Rlimit.closedSet i.castSucc),
      S.vertex
        (S.finiteWalk.breakPosition Rlimit.closedSet i.castSucc + 1)) ∈
        familyEdges T.interval.ambientInterval
    exact hedge
  · exact hvX

end Erdos599.Blueprint.LinkageBlueprint.PostClosureCompressorAssignment

#print axioms Erdos599.Alternating.RunCompressor.FiniteInput.colour_eq_forward_of_vertex_mem
#print axioms Erdos599.Blueprint.LinkageBlueprint.PostClosureCompressorAssignment.finite_breakInterval_hammockEligible
