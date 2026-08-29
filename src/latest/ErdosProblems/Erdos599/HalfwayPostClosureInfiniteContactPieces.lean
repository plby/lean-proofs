/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.HalfwayInfiniteContactPieceGeometry
import ErdosProblems.Erdos599.HalfwayPostClosureInfiniteGeometry
import ErdosProblems.Erdos599.HalfwayClosedClassifiedContactSegmentation

/-!
# Classified pieces of an actual post-closure infinite compressor trace

Every bounded interval between consecutive closing-set contacts is either
wholly closed or has the endpoint-covered Claim-2 classification.  When
there are only finitely many contacts, the genuine shifted infinite suffix
has the infinite endpoint-covered classification.  All pieces retain their
literal order, direction, and containment in the original compressor trace.
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

/-- The literal coordinate interval between two consecutive contacts,
classified unless it lies wholly in the closing set. -/
noncomputable def infiniteCoordinateContactPiece
    (A : PostClosureCompressorAssignment T)
    (s : {x // x ∈ Gamma.initialSet A.fractured.outside.holes.paths \
      Gamma.initialSet (outsideReference T.intervalReference Rlimit.closedSet)})
    (S : RunCompressor.InfiniteInput Gamma.graph)
    (hchange : ∀ n, ∃ m, n < m ∧ S.colour m ≠ S.colour n)
    (hS : A.assignment.produced.bracket.assignment.assigned s =
      .infinite (S.toInfiniteRunWalk hchange).toInfiniteTrace)
    (a b : Nat) (hab : a < b)
    (haX : S.vertex a ∈ Rlimit.closedSet)
    (hbX : S.vertex b ∈ Rlimit.closedSet)
    (hinterior : Disjoint
      (hammockInterior (S.vertex a) (.vertex (S.vertex b))
        (.finite (S.coordinateInterval a b hab).toFiniteRunWalk.toFiniteTrace))
      Rlimit.closedSet) :
    ClassifiedOrClosedFiniteContactPiece
      (Y := C.ladder.limitWarp) (kappa := kappa)
      (.infinite (S.toInfiniteRunWalk hchange).toInfiniteTrace)
      Rlimit.closedSet (S.vertex a) (S.vertex b) := by
  classical
  let Q : AltPath Gamma.graph :=
    .finite (S.coordinateInterval a b hab).toFiniteRunWalk.toFiniteTrace
  by_cases hinside : Q.vertexSet ⊆ Rlimit.closedSet
  · exact .closed {
      path := Q
      starts_at := by
        change (S.coordinateInterval a b hab).toFiniteRunWalk.toFiniteTrace.initial =
          S.vertex a
        exact S.coordinateInterval_trace_initial a b hab
      ends_at := by
        change some
          (S.coordinateInterval a b hab).toFiniteRunWalk.toFiniteTrace.terminal =
          some (S.vertex b)
        congr 1
        exact S.coordinateInterval_trace_terminal a b hab
      contained := hinside
      forwardEdges_subset_original :=
        S.coordinateInterval_directionEdges_subset hchange a b hab .forward
      vertexSet_subset_original :=
        S.coordinateInterval_vertexSet_subset hchange a b hab
      edgeSet_subset_original :=
        S.coordinateInterval_edgeSet_subset hchange a b hab }
  · exact .classified {
      path := Q
      starts_at := by
        change (S.coordinateInterval a b hab).toFiniteRunWalk.toFiniteTrace.initial =
          S.vertex a
        exact S.coordinateInterval_trace_initial a b hab
      ends_at := by
        change some
          (S.coordinateInterval a b hab).toFiniteRunWalk.toFiniteTrace.terminal =
          some (S.vertex b)
        congr 1
        exact S.coordinateInterval_trace_terminal a b hab
      classification := (classifyFinite
        Rlimit.hammock_closed Rlimit.reference_closed
        (fun _ _ => A.infinite_coordinateInterval_hammockEligible
          s S hchange hS a b haX hbX)
        (fun _ _ => A.infinite_coordinateInterval_internallySafe
          s S hchange hS a b hab)
        (by
          change (S.coordinateInterval a b hab).toFiniteRunWalk.toFiniteTrace.initial =
            S.vertex a
          exact S.coordinateInterval_trace_initial a b hab)
        (by
          change some
            (S.coordinateInterval a b hab).toFiniteRunWalk.toFiniteTrace.terminal =
            some (S.vertex b)
          congr 1
          exact S.coordinateInterval_trace_terminal a b hab)
        hinterior hinside
        (fun _ => haX) (fun _ => hbX)).some
      forwardEdges_subset_original :=
        S.coordinateInterval_directionEdges_subset hchange a b hab .forward
      vertexSet_subset_original :=
        S.coordinateInterval_vertexSet_subset hchange a b hab
      edgeSet_subset_original :=
        S.coordinateInterval_edgeSet_subset hchange a b hab }

@[simp] theorem infiniteCoordinateContactPiece_path
    (A : PostClosureCompressorAssignment T)
    (s : {x // x ∈ Gamma.initialSet A.fractured.outside.holes.paths \
      Gamma.initialSet (outsideReference T.intervalReference Rlimit.closedSet)})
    (S : RunCompressor.InfiniteInput Gamma.graph)
    (hchange : ∀ n, ∃ m, n < m ∧ S.colour m ≠ S.colour n)
    (hS : A.assignment.produced.bracket.assignment.assigned s =
      .infinite (S.toInfiniteRunWalk hchange).toInfiniteTrace)
    (a b : Nat) (hab : a < b)
    (haX : S.vertex a ∈ Rlimit.closedSet)
    (hbX : S.vertex b ∈ Rlimit.closedSet)
    (hinterior : Disjoint
      (hammockInterior (S.vertex a) (.vertex (S.vertex b))
        (.finite (S.coordinateInterval a b hab).toFiniteRunWalk.toFiniteTrace))
      Rlimit.closedSet) :
    (A.infiniteCoordinateContactPiece s S hchange hS a b hab haX hbX
      hinterior).path =
      .finite (S.coordinateInterval a b hab).toFiniteRunWalk.toFiniteTrace := by
  classical
  simp only [infiniteCoordinateContactPiece]
  split <;> rfl

/-- The genuine infinite suffix after the final contact. -/
noncomputable def infiniteContactTail
    (A : PostClosureCompressorAssignment T)
    (s : {x // x ∈ Gamma.initialSet A.fractured.outside.holes.paths \
      Gamma.initialSet (outsideReference T.intervalReference Rlimit.closedSet)})
    (S : RunCompressor.InfiniteInput Gamma.graph)
    (hchange : ∀ n, ∃ m, n < m ∧ S.colour m ≠ S.colour n)
    (hS : A.assignment.produced.bracket.assignment.assigned s =
      .infinite (S.toInfiniteRunWalk hchange).toInfiniteTrace)
    (a : Nat) (haX : S.vertex a ∈ Rlimit.closedSet)
    (hinterior : Disjoint
      (hammockInterior (S.vertex a) .infinity
        (.infinite ((S.shift a).toInfiniteRunWalk
          (S.shift_changes hchange a)).toInfiniteTrace)) Rlimit.closedSet)
    (houtside : ¬ (AltPath.infinite ((S.shift a).toInfiniteRunWalk
      (S.shift_changes hchange a)).toInfiniteTrace).vertexSet ⊆
      Rlimit.closedSet) :
    ClassifiedInfiniteContactTail
      (Y := C.ladder.limitWarp) (kappa := kappa)
      (.infinite (S.toInfiniteRunWalk hchange).toInfiniteTrace)
      Rlimit.closedSet C.persistent (S.vertex a) where
  path := .infinite ((S.shift a).toInfiniteRunWalk
    (S.shift_changes hchange a)).toInfiniteTrace
  starts_at := by
    change ((S.shift a).toInfiniteRunWalk
      (S.shift_changes hchange a)).toInfiniteTrace.initial = S.vertex a
    exact S.shift_trace_initial hchange a
  infinite := True.intro
  classification := (classifyInfinite
    Rlimit.hammock_closed Rlimit.reference_closed
    (fun _ => A.infinite_shift_hammockEligible s S hchange hS a haX)
    (fun _ => A.infinite_shift_internallySafe s S hchange hS a)
    (by
      change ((S.shift a).toInfiniteRunWalk
        (S.shift_changes hchange a)).toInfiniteTrace.initial = S.vertex a
      exact S.shift_trace_initial hchange a)
    True.intro hinterior houtside
    (fun _ => haX)).some
  forwardEdges_subset_original :=
    S.shift_directionEdges_subset hchange a .forward
  vertexSet_subset_original := S.shift_vertexSet_subset hchange a
  edgeSet_subset_original := S.shift_edgeSet_subset hchange a

@[simp] theorem infiniteContactTail_path
    (A : PostClosureCompressorAssignment T)
    (s : {x // x ∈ Gamma.initialSet A.fractured.outside.holes.paths \
      Gamma.initialSet (outsideReference T.intervalReference Rlimit.closedSet)})
    (S : RunCompressor.InfiniteInput Gamma.graph)
    (hchange : ∀ n, ∃ m, n < m ∧ S.colour m ≠ S.colour n)
    (hS : A.assignment.produced.bracket.assignment.assigned s =
      .infinite (S.toInfiniteRunWalk hchange).toInfiniteTrace)
    (a : Nat) (haX : S.vertex a ∈ Rlimit.closedSet)
    (hinterior : Disjoint
      (hammockInterior (S.vertex a) .infinity
        (.infinite ((S.shift a).toInfiniteRunWalk
          (S.shift_changes hchange a)).toInfiniteTrace)) Rlimit.closedSet)
    (houtside : ¬ (AltPath.infinite ((S.shift a).toInfiniteRunWalk
      (S.shift_changes hchange a)).toInfiniteTrace).vertexSet ⊆
      Rlimit.closedSet) :
    (A.infiniteContactTail s S hchange hS a haX hinterior houtside).path =
      .infinite ((S.shift a).toInfiniteRunWalk
        (S.shift_changes hchange a)).toInfiniteTrace := rfl

#print axioms infiniteCoordinateContactPiece
#print axioms infiniteContactTail

end Erdos599.Blueprint.LinkageBlueprint.PostClosureCompressorAssignment
