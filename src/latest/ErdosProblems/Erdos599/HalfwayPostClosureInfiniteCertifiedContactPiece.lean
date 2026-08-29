/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.HalfwayPostClosureInfiniteContactPieces

/-!
# Certified bounded pieces of an infinite compressor trace

The endpoint cases are selected deterministically.  A covered endpoint
produces a covered classification and therefore no shortcut.  Consequently
shortcut membership certifies that both endpoints were exposed off the
reference warp and that the literal coordinate interval was classified by
the genuine safe Claim-2 branch.
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

/-- Deterministic closed-or-classified construction for one bounded
coordinate interval of an actual infinite compressor trace. -/
theorem exists_infiniteCoordinateContactPiece_with_certificate
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
    ∃ P : ClassifiedOrClosedFiniteContactPiece
        (Y := C.ladder.limitWarp) (kappa := kappa)
        (.infinite (S.toInfiniteRunWalk hchange).toInfiniteTrace)
        Rlimit.closedSet (S.vertex a) (S.vertex b),
      P.path =
        .finite (S.coordinateInterval a b hab).toFiniteRunWalk.toFiniteTrace ∧
      ∀ e ∈ P.shortcutEdges,
        S.vertex a ∉ Gamma.vertexSet C.ladder.limitWarp ∧
        S.vertex b ∉ Gamma.vertexSet C.ladder.limitWarp ∧
        IsSafe C.ladder.limitWarp P.path ∧
        HammockEligible Rlimit.closedSet C.ladder.limitStrictRoof
          C.ladder.limitRoof (S.vertex a) (.vertex (S.vertex b)) ∧
        Disjoint (hammockInterior (S.vertex a) (.vertex (S.vertex b)) P.path)
          Rlimit.closedSet ∧
        ¬P.path.vertexSet ⊆ Rlimit.closedSet := by
  let Q : AltPath Gamma.graph :=
    .finite (S.coordinateInterval a b hab).toFiniteRunWalk.toFiniteTrace
  have hstart : Q.initial = S.vertex a := by
    change (S.coordinateInterval a b hab).toFiniteRunWalk.toFiniteTrace.initial =
      S.vertex a
    exact S.coordinateInterval_trace_initial a b hab
  have hend : Q.terminal? = some (S.vertex b) := by
    change some (S.coordinateInterval a b hab).toFiniteRunWalk.toFiniteTrace.terminal =
      some (S.vertex b)
    congr 1
    exact S.coordinateInterval_trace_terminal a b hab
  let mkClassified : FiniteSegmentClassification
      (Y := C.ladder.limitWarp) (X := Rlimit.closedSet) (kappa := kappa)
      Q (S.vertex a) (S.vertex b) →
      ClassifiedOrClosedFiniteContactPiece
        (Y := C.ladder.limitWarp) (kappa := kappa)
        (.infinite (S.toInfiniteRunWalk hchange).toInfiniteTrace)
        Rlimit.closedSet (S.vertex a) (S.vertex b) := fun classification ↦
    .classified {
      path := Q
      starts_at := hstart
      ends_at := hend
      classification := classification
      forwardEdges_subset_original :=
        S.coordinateInterval_directionEdges_subset hchange a b hab .forward
      vertexSet_subset_original :=
        S.coordinateInterval_vertexSet_subset hchange a b hab
      edgeSet_subset_original :=
        S.coordinateInterval_edgeSet_subset hchange a b hab
    }
  by_cases hinside : Q.vertexSet ⊆ Rlimit.closedSet
  · let P : ClassifiedOrClosedFiniteContactPiece
        (Y := C.ladder.limitWarp) (kappa := kappa)
        (.infinite (S.toInfiniteRunWalk hchange).toInfiniteTrace)
        Rlimit.closedSet (S.vertex a) (S.vertex b) := .closed {
      path := Q
      starts_at := hstart
      ends_at := hend
      contained := hinside
      forwardEdges_subset_original :=
        S.coordinateInterval_directionEdges_subset hchange a b hab .forward
      vertexSet_subset_original :=
        S.coordinateInterval_vertexSet_subset hchange a b hab
      edgeSet_subset_original :=
        S.coordinateInterval_edgeSet_subset hchange a b hab
    }
    refine ⟨P, rfl, ?_⟩
    intro e he
    change e ∈ (∅ : Set (V × V)) at he
    exact (by simpa using he : False).elim
  · by_cases haY : S.vertex a ∈ Gamma.vertexSet C.ladder.limitWarp
    · let owner : ClosedReferenceOwner C.ladder.limitWarp
          Rlimit.closedSet (S.vertex a) :=
        (ClosedReferenceOwner.exists_of_mem Rlimit.reference_closed haY haX).some
      let P := mkClassified (.initialCovered owner)
      refine ⟨P, rfl, ?_⟩
      intro e he
      change e ∈ (∅ : Set (V × V)) at he
      exact (by simpa using he : False).elim
    · by_cases hbY : S.vertex b ∈ Gamma.vertexSet C.ladder.limitWarp
      · let owner : ClosedReferenceOwner C.ladder.limitWarp
            Rlimit.closedSet (S.vertex b) :=
          (ClosedReferenceOwner.exists_of_mem Rlimit.reference_closed hbY hbX).some
        let P := mkClassified (.terminalCovered owner)
        refine ⟨P, rfl, ?_⟩
        intro e he
        change e ∈ (∅ : Set (V × V)) at he
        exact (by simpa using he : False).elim
      · have hsafe : IsSafe C.ladder.limitWarp Q := by
          apply (A.infinite_coordinateInterval_internallySafe
            s S hchange hS a b hab).isSafe_of_exposedEndpoints
          · rw [hstart]
            exact haY
          · intro w hw
            have hwb := Option.some.inj (hw.symm.trans hend)
            simpa only [hwb] using hbY
        have heligible : HammockEligible Rlimit.closedSet
            C.ladder.limitStrictRoof C.ladder.limitRoof
            (S.vertex a) (.vertex (S.vertex b)) :=
          A.infinite_coordinateInterval_hammockEligible
            s S hchange hS a b haX hbX
        have himag : IsImaginaryEdge Gamma C.ladder.limitWarp kappa
            (S.vertex a) (S.vertex b) :=
          isImaginaryEdge_of_closed Rlimit.hammock_closed heligible hsafe
            hstart hend hinterior hinside
        let P := mkClassified (.imaginary himag)
        refine ⟨P, rfl, ?_⟩
        intro _e _he
        exact ⟨haY, hbY, hsafe, heligible, hinterior, hinside⟩

#print axioms exists_infiniteCoordinateContactPiece_with_certificate

end Erdos599.Blueprint.LinkageBlueprint.PostClosureCompressorAssignment
