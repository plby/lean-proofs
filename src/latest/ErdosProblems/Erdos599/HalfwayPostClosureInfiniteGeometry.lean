/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.HalfwayInfiniteSuffixInternalSafety
import ErdosProblems.Erdos599.HalfwayInfiniteInputDirectionEdgeCoverage
import ErdosProblems.Erdos599.HalfwayPostClosureCompressorAssignment
import ErdosProblems.Erdos599.HalfwayPostClosureAssignedLinkGeometry
import ErdosProblems.Erdos599.HalfwayPostClosureContactEligibility

/-!
# Actual post-closure infinite-compressor interval geometry

Bounded coordinate intervals and the final shifted suffix inherit the
global limiting-reference safety of the actual assignment.  At every
closing-set contact, the outgoing raw edge is a literal forward edge of the
post-closure interval row, hence supplies the exact hammock eligibility.
-/

noncomputable section

open Cardinal Order Set

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

/-- Every bounded coordinate interval of an actual infinite assigned trace
is internally safe for the global limiting reference. -/
theorem infinite_coordinateInterval_internallySafe
    (A : PostClosureCompressorAssignment T)
    (s : {x // x ∈ Gamma.initialSet A.fractured.outside.holes.paths \
      Gamma.initialSet (outsideReference T.intervalReference Rlimit.closedSet)})
    (S : RunCompressor.InfiniteInput Gamma.graph)
    (hchange : ∀ n, ∃ m, n < m ∧ S.colour m ≠ S.colour n)
    (hS : A.assignment.produced.bracket.assignment.assigned s =
      .infinite (S.toInfiniteRunWalk hchange).toInfiniteTrace)
    (a b : Nat) (hab : a < b) :
    InternallySafe C.ladder.limitWarp
      (.finite (S.coordinateInterval a b hab).toFiniteRunWalk.toFiniteTrace) := by
  have hparent : InternallySafe C.ladder.limitWarp
      (.infinite (S.toInfiniteRunWalk hchange).toInfiniteTrace) := by
    rw [← hS]
    exact A.toPostClosureProducedAssignment.assigned_internallySafe_global s
  let H := A.toPostClosureProducedAssignment.assigned_backward_global s
  let I : Type u := H.Index
  have hP :
      (A.assignment.produced.bracket.assignment.assigned s
        ).IndexedBackwardProvenance C.ladder.limitWarp I := H.certificate
  have P :
      (AltPath.infinite (S.toInfiniteRunWalk hchange).toInfiniteTrace
        ).IndexedBackwardProvenance C.ladder.limitWarp I := hS ▸ hP
  exact hparent.infiniteCoordinateInterval S hchange a b hab P

/-- The exact infinite suffix after the last contact is likewise internally
safe for the global limiting reference. -/
theorem infinite_shift_internallySafe
    (A : PostClosureCompressorAssignment T)
    (s : {x // x ∈ Gamma.initialSet A.fractured.outside.holes.paths \
      Gamma.initialSet (outsideReference T.intervalReference Rlimit.closedSet)})
    (S : RunCompressor.InfiniteInput Gamma.graph)
    (hchange : ∀ n, ∃ m, n < m ∧ S.colour m ≠ S.colour n)
    (hS : A.assignment.produced.bracket.assignment.assigned s =
      .infinite (S.toInfiniteRunWalk hchange).toInfiniteTrace)
    (a : Nat) :
    InternallySafe C.ladder.limitWarp
      (.infinite ((S.shift a).toInfiniteRunWalk
        (S.shift_changes hchange a)).toInfiniteTrace) := by
  have hparent : InternallySafe C.ladder.limitWarp
      (.infinite (S.toInfiniteRunWalk hchange).toInfiniteTrace) := by
    rw [← hS]
    exact A.toPostClosureProducedAssignment.assigned_internallySafe_global s
  let H := A.toPostClosureProducedAssignment.assigned_backward_global s
  let I : Type u := H.Index
  have hP :
      (A.assignment.produced.bracket.assignment.assigned s
        ).IndexedBackwardProvenance C.ladder.limitWarp I := H.certificate
  have P :
      (AltPath.infinite (S.toInfiniteRunWalk hchange).toInfiniteTrace
        ).IndexedBackwardProvenance C.ladder.limitWarp I := hS ▸ hP
  exact hparent.infiniteShift S hchange a P

/-- At a closed raw coordinate of the actual infinite assignment, its
outgoing edge is forward and belongs to the literal interval family. -/
theorem infinite_rawEdge_mem_intervalFamily
    (A : PostClosureCompressorAssignment T)
    (s : {x // x ∈ Gamma.initialSet A.fractured.outside.holes.paths \
      Gamma.initialSet (outsideReference T.intervalReference Rlimit.closedSet)})
    (S : RunCompressor.InfiniteInput Gamma.graph)
    (hchange : ∀ n, ∃ m, n < m ∧ S.colour m ≠ S.colour n)
    (hS : A.assignment.produced.bracket.assignment.assigned s =
      .infinite (S.toInfiniteRunWalk hchange).toInfiniteTrace)
    (n : Nat) (hnX : S.vertex n ∈ Rlimit.closedSet) :
    (S.vertex n, S.vertex (n + 1)) ∈
      familyEdges T.interval.ambientInterval := by
  have hbackwardOff : ∀ l ∈ (AltPath.infinite
      (S.toInfiniteRunWalk hchange).toInfiniteTrace).links,
      l.direction = .backward → Disjoint l.path.support Rlimit.closedSet := by
    intro l hl hdir
    apply A.toPostClosureProducedAssignment.assigned_backwardLink_disjoint_closedSet
      s l
    · rw [hS]
      exact hl
    · exact hdir
  have hcolour : S.colour n = .forward :=
    S.colour_eq_forward_of_vertex_mem hchange Rlimit.closedSet
      hbackwardOff n hnX
  have hraw := S.rawEdge_mem_directionEdges hchange n
  rw [hcolour] at hraw
  simp only [AltPath.directionEdges, Set.mem_iUnion] at hraw
  obtain ⟨l, hl, hdir, he⟩ := hraw
  have hrow :=
    A.toPostClosureProducedAssignment.assigned_forwardLink_edges_subset_intervalFamily
      s l (by rw [hS]; exact hl) hdir he
  simpa only [RunCompressor.InfiniteInput.rawEdge, hcolour] using hrow

/-- Consecutive infinite-compressor contacts have the exact finite endpoint
eligibility used by Claim 2. -/
theorem infinite_coordinateInterval_hammockEligible
    (A : PostClosureCompressorAssignment T)
    (s : {x // x ∈ Gamma.initialSet A.fractured.outside.holes.paths \
      Gamma.initialSet (outsideReference T.intervalReference Rlimit.closedSet)})
    (S : RunCompressor.InfiniteInput Gamma.graph)
    (hchange : ∀ n, ∃ m, n < m ∧ S.colour m ≠ S.colour n)
    (hS : A.assignment.produced.bracket.assignment.assigned s =
      .infinite (S.toInfiniteRunWalk hchange).toInfiniteTrace)
    (a b : Nat) (haX : S.vertex a ∈ Rlimit.closedSet)
    (hbX : S.vertex b ∈ Rlimit.closedSet) :
    HammockEligible Rlimit.closedSet C.ladder.limitStrictRoof
      C.ladder.limitRoof (S.vertex a) (.vertex (S.vertex b)) := by
  have hedge := A.infinite_rawEdge_mem_intervalFamily s S hchange hS a haX
  exact T.hammockEligible_vertex_of_mem_intervalEdge
    Rlimit haX hedge hbX

/-- The last contact also has the exact infinite-end eligibility used by
the popularity branch of Claim 2. -/
theorem infinite_shift_hammockEligible
    (A : PostClosureCompressorAssignment T)
    (s : {x // x ∈ Gamma.initialSet A.fractured.outside.holes.paths \
      Gamma.initialSet (outsideReference T.intervalReference Rlimit.closedSet)})
    (S : RunCompressor.InfiniteInput Gamma.graph)
    (hchange : ∀ n, ∃ m, n < m ∧ S.colour m ≠ S.colour n)
    (hS : A.assignment.produced.bracket.assignment.assigned s =
      .infinite (S.toInfiniteRunWalk hchange).toInfiniteTrace)
    (a : Nat) (haX : S.vertex a ∈ Rlimit.closedSet) :
    HammockEligible Rlimit.closedSet C.ladder.limitStrictRoof
      C.ladder.limitRoof (S.vertex a) .infinity := by
  have hedge := A.infinite_rawEdge_mem_intervalFamily s S hchange hS a haX
  exact T.hammockEligible_infinity_of_mem_intervalEdge Rlimit haX hedge

end Erdos599.Blueprint.LinkageBlueprint.PostClosureCompressorAssignment

#print axioms Erdos599.Blueprint.LinkageBlueprint.PostClosureCompressorAssignment.infinite_coordinateInterval_internallySafe
#print axioms Erdos599.Blueprint.LinkageBlueprint.PostClosureCompressorAssignment.infinite_shift_internallySafe
#print axioms Erdos599.Blueprint.LinkageBlueprint.PostClosureCompressorAssignment.infinite_rawEdge_mem_intervalFamily
