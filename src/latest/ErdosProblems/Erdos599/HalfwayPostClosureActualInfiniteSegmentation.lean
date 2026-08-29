/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.HalfwayPostClosureInfiniteContactPieces
import ErdosProblems.Erdos599.HalfwayPostClosureSourceAbsorption

/-!
# Actual infinite post-closure contact segmentation

The initial coordinate of every uncovered assigned path belongs to the
moving closing set.  Enumerating all later contacts therefore yields either
an omega chain of literal finite coordinate intervals, or a finite chain
followed by the genuine shifted infinite suffix.  Each finite interval is
closed or Claim-2 classified, and the suffix is classified without being
discarded.  The resulting decomposition is exact on vertices and edges.
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

private theorem initial_coordinate_mem_closedSet
    (A : PostClosureCompressorAssignment T)
    (s : {x // x ∈ Gamma.initialSet A.fractured.outside.holes.paths \
      Gamma.initialSet (outsideReference T.intervalReference Rlimit.closedSet)})
    (S : RunCompressor.InfiniteInput Gamma.graph)
    (hchange : ∀ n, ∃ m, n < m ∧ S.colour m ≠ S.colour n)
    (hS : A.assignment.produced.bracket.assignment.assigned s =
      .infinite (S.toInfiniteRunWalk hchange).toInfiniteTrace) :
    S.vertex 0 ∈ Rlimit.closedSet := by
  have hsX : s.1 ∈ Rlimit.closedSet :=
    T.uncovered_initials_subset_closedSet Rlimit A.fractured s.2
  have hstart := A.assignment.produced.bracket.assignment.starts_at s
  rw [hS] at hstart
  rw [← hstart] at hsX
  change (S.toInfiniteRunWalk hchange).toInfiniteTrace.initial ∈
    Rlimit.closedSet at hsX
  rw [(S.toInfiniteRunWalk hchange).toInfiniteTrace_initial] at hsX
  exact hsX

private theorem exists_eventuallyClosedClassifiedContactSegmentation
    (A : PostClosureCompressorAssignment T)
    (s : {x // x ∈ Gamma.initialSet A.fractured.outside.holes.paths \
      Gamma.initialSet (outsideReference T.intervalReference Rlimit.closedSet)})
    (S : RunCompressor.InfiniteInput Gamma.graph)
    (hchange : ∀ n, ∃ m, n < m ∧ S.colour m ≠ S.colour n)
    (hS : A.assignment.produced.bracket.assignment.assigned s =
      .infinite (S.toInfiniteRunWalk hchange).toInfiniteTrace)
    (E : S.EventualContactCoordinates Rlimit.closedSet) :
    ∃ D : EventuallyClosedClassifiedContactSegmentation
        (Y := C.ladder.limitWarp) (kappa := kappa)
        (.infinite (S.toInfiniteRunWalk hchange).toInfiniteTrace)
        Rlimit.closedSet C.persistent,
      D.toChain.contactSet ⊆ Rlimit.closedSet := by
  classical
  let piece : (i : Fin E.count) →
      ClassifiedOrClosedFiniteContactPiece
        (Y := C.ladder.limitWarp) (kappa := kappa)
        (.infinite (S.toInfiniteRunWalk hchange).toInfiniteTrace)
        Rlimit.closedSet
        (S.vertex (E.coord i.castSucc)) (S.vertex (E.coord i.succ)) :=
    fun i => A.infiniteCoordinateContactPiece s S hchange hS
      (E.coord i.castSucc) (E.coord i.succ)
      (E.strictMono_coord Fin.castSucc_lt_succ)
      (E.coord_mem i.castSucc) (E.coord_mem i.succ)
      (E.interval_hammockInterior_disjoint i)
  have piece_path (i : Fin E.count) :
      (piece i).path = .finite (E.interval i).toFiniteRunWalk.toFiniteTrace := by
    rw [show E.interval i = S.coordinateInterval
      (E.coord i.castSucc) (E.coord i.succ)
      (E.strictMono_coord Fin.castSucc_lt_succ) from rfl]
    exact infiniteCoordinateContactPiece_path A s S hchange hS
      (E.coord i.castSucc) (E.coord i.succ)
      (E.strictMono_coord Fin.castSucc_lt_succ)
      (E.coord_mem i.castSucc) (E.coord_mem i.succ)
      (E.interval_hammockInterior_disjoint i)
  let tail := A.infiniteContactTail s S hchange hS E.last
    (E.coord_mem ⟨E.count, Nat.lt_succ_self _⟩)
    (E.suffix_hammockInterior_disjoint hchange)
    (E.suffix_not_subset hchange)
  have tail_path : tail.path =
      .infinite ((S.shift E.last).toInfiniteRunWalk
        (S.shift_changes hchange E.last)).toInfiniteTrace := by
    exact infiniteContactTail_path A s S hchange hS E.last
      (E.coord_mem ⟨E.count, Nat.lt_succ_self _⟩)
      (E.suffix_hammockInterior_disjoint hchange)
      (E.suffix_not_subset hchange)
  let D : EventuallyClosedClassifiedContactSegmentation
      (Y := C.ladder.limitWarp) (kappa := kappa)
      (.infinite (S.toInfiniteRunWalk hchange).toInfiniteTrace)
      Rlimit.closedSet C.persistent := {
    count := E.count
    point := fun i => S.vertex (E.coord i)
    point_injective := by
      intro i j hij
      exact E.strictMono_coord.injective (S.vertex_injective hij)
    piece := piece
    tail := tail
    initial_eq := by
      change S.vertex (E.coord ⟨0, Nat.zero_lt_succ _⟩) =
        (S.toInfiniteRunWalk hchange).toInfiniteTrace.initial
      rw [E.coord_zero, (S.toInfiniteRunWalk hchange).toInfiniteTrace_initial]
      rfl
    vertexSet_exact := by
      change (S.toInfiniteRunWalk hchange).toInfiniteTrace.vertexSet =
        Set.range (fun i => S.vertex (E.coord i)) ∪
          (⋃ i, (piece i).path.vertexSet) ∪ tail.path.vertexSet
      apply Set.Subset.antisymm
      · intro x hx
        rw [E.trace_vertexSet_exact hchange] at hx
        rcases hx with hx | hx
        · left
          right
          simp only [Set.mem_iUnion] at hx ⊢
          obtain ⟨i, hxi⟩ := hx
          refine ⟨i, ?_⟩
          rw [piece_path i]
          change x ∈ (E.interval i).toFiniteRunWalk.toFiniteTrace.vertexSet
          exact hxi
        · right
          rw [tail_path]
          change x ∈ ((S.shift E.last).toInfiniteRunWalk
            (S.shift_changes hchange E.last)).toInfiniteTrace.vertexSet
          exact hx
      · rintro x ((hx | hx) | hx)
        · change x ∈ (S.toInfiniteRunWalk hchange).toInfiniteTrace.vertexSet
          rw [S.toInfiniteTrace_vertexSet hchange]
          obtain ⟨i, rfl⟩ := hx
          exact ⟨E.coord i, rfl⟩
        · simp only [Set.mem_iUnion] at hx
          obtain ⟨i, hxi⟩ := hx
          exact (piece i).vertexSet_subset_original hxi
        · exact tail.vertexSet_subset_original hx
    edgeSet_exact := by
      change (S.toInfiniteRunWalk hchange).toInfiniteTrace.edgeSet =
        (⋃ i, (piece i).path.edgeSet) ∪ tail.path.edgeSet
      rw [E.trace_edgeSet_exact hchange]
      have hpieces :
          (⋃ i : Fin E.count,
            (E.interval i).toFiniteRunWalk.toFiniteTrace.edgeSet) =
          ⋃ i, (piece i).path.edgeSet := by
        apply iUnion_congr
        intro i
        rw [piece_path i]
        rfl
      rw [hpieces, tail_path]
      rfl
  }
  refine ⟨D, ?_⟩
  rintro x hx
  change x ∈ Set.range (fun i => S.vertex (E.coord i)) at hx
  obtain ⟨i, rfl⟩ := hx
  exact E.coord_mem i

private theorem exists_omegaClosedClassifiedContactSegmentation
    (A : PostClosureCompressorAssignment T)
    (s : {x // x ∈ Gamma.initialSet A.fractured.outside.holes.paths \
      Gamma.initialSet (outsideReference T.intervalReference Rlimit.closedSet)})
    (S : RunCompressor.InfiniteInput Gamma.graph)
    (hchange : ∀ n, ∃ m, n < m ∧ S.colour m ≠ S.colour n)
    (hS : A.assignment.produced.bracket.assignment.assigned s =
      .infinite (S.toInfiniteRunWalk hchange).toInfiniteTrace)
    (E : S.OmegaContactCoordinates Rlimit.closedSet) :
    ∃ D : OmegaClosedClassifiedContactSegmentation
        (Y := C.ladder.limitWarp) (kappa := kappa)
        (.infinite (S.toInfiniteRunWalk hchange).toInfiniteTrace)
        Rlimit.closedSet,
      D.toChain.contactSet ⊆ Rlimit.closedSet := by
  classical
  let piece : (i : Nat) →
      ClassifiedOrClosedFiniteContactPiece
        (Y := C.ladder.limitWarp) (kappa := kappa)
        (.infinite (S.toInfiniteRunWalk hchange).toInfiniteTrace)
        Rlimit.closedSet (S.vertex (E.coord i))
        (S.vertex (E.coord (i + 1))) :=
    fun i => A.infiniteCoordinateContactPiece s S hchange hS
      (E.coord i) (E.coord (i + 1))
      (E.strictMono_coord (Nat.lt_succ_self i))
      (E.coord_mem i) (E.coord_mem (i + 1))
      (E.interval_hammockInterior_disjoint i)
  have piece_path (i : Nat) :
      (piece i).path = .finite (E.interval i).toFiniteRunWalk.toFiniteTrace := by
    rw [show E.interval i = S.coordinateInterval
      (E.coord i) (E.coord (i + 1))
      (E.strictMono_coord (Nat.lt_succ_self i)) from rfl]
    exact infiniteCoordinateContactPiece_path A s S hchange hS
      (E.coord i) (E.coord (i + 1))
      (E.strictMono_coord (Nat.lt_succ_self i))
      (E.coord_mem i) (E.coord_mem (i + 1))
      (E.interval_hammockInterior_disjoint i)
  let D : OmegaClosedClassifiedContactSegmentation
      (Y := C.ladder.limitWarp) (kappa := kappa)
      (.infinite (S.toInfiniteRunWalk hchange).toInfiniteTrace)
      Rlimit.closedSet := {
    point := fun i => S.vertex (E.coord i)
    point_injective := by
      intro i j hij
      exact E.strictMono_coord.injective (S.vertex_injective hij)
    piece := piece
    initial_eq := by
      change S.vertex (E.coord 0) =
        (S.toInfiniteRunWalk hchange).toInfiniteTrace.initial
      rw [E.coord_zero, (S.toInfiniteRunWalk hchange).toInfiniteTrace_initial]
      rfl
    vertexSet_exact := by
      change (S.toInfiniteRunWalk hchange).toInfiniteTrace.vertexSet =
        Set.range (fun i => S.vertex (E.coord i)) ∪
          ⋃ i, (piece i).path.vertexSet
      apply Set.Subset.antisymm
      · intro x hx
        right
        rw [E.trace_vertexSet_exact hchange] at hx
        simp only [Set.mem_iUnion] at hx ⊢
        obtain ⟨i, hxi⟩ := hx
        refine ⟨i, ?_⟩
        rw [piece_path i]
        change x ∈ (E.interval i).toFiniteRunWalk.toFiniteTrace.vertexSet
        exact hxi
      · rintro x (hx | hx)
        · change x ∈ (S.toInfiniteRunWalk hchange).toInfiniteTrace.vertexSet
          rw [S.toInfiniteTrace_vertexSet hchange]
          obtain ⟨i, rfl⟩ := hx
          exact ⟨E.coord i, rfl⟩
        · simp only [Set.mem_iUnion] at hx
          obtain ⟨i, hxi⟩ := hx
          exact (piece i).vertexSet_subset_original hxi
    edgeSet_exact := by
      change (S.toInfiniteRunWalk hchange).toInfiniteTrace.edgeSet =
        ⋃ i, (piece i).path.edgeSet
      rw [E.trace_edgeSet_exact hchange]
      apply iUnion_congr
      intro i
      rw [piece_path i]
      rfl
  }
  refine ⟨D, ?_⟩
  rintro x hx
  change x ∈ Set.range (fun i => S.vertex (E.coord i)) at hx
  obtain ⟨i, rfl⟩ := hx
  exact E.coord_mem i

/-- The actual infinite segmentation retains its raw-coordinate provenance:
every displayed contact is one of the enumerated closing-set contacts. -/
theorem exists_actualInfiniteClosedClassifiedContactSegmentation_with_contactSet_subset
    (A : PostClosureCompressorAssignment T)
    (s : {x // x ∈ Gamma.initialSet A.fractured.outside.holes.paths \
      Gamma.initialSet (outsideReference T.intervalReference Rlimit.closedSet)})
    (S : RunCompressor.InfiniteInput Gamma.graph)
    (hchange : ∀ n, ∃ m, n < m ∧ S.colour m ≠ S.colour n)
    (hS : A.assignment.produced.bracket.assignment.assigned s =
      .infinite (S.toInfiniteRunWalk hchange).toInfiniteTrace) :
    ∃ D : ClosedClassifiedContactSegmentation
        (Y := C.ladder.limitWarp) (kappa := kappa)
        (.infinite (S.toInfiniteRunWalk hchange).toInfiniteTrace)
        Rlimit.closedSet C.persistent,
      D.contactSet ⊆ Rlimit.closedSet := by
  have hzero := A.initial_coordinate_mem_closedSet s S hchange hS
  cases S.contactDichotomy Rlimit.closedSet hzero with
  | eventual E =>
      obtain ⟨D, hD⟩ := A.exists_eventuallyClosedClassifiedContactSegmentation
        s S hchange hS E
      exact ⟨.eventually D, hD⟩
  | omega E =>
      obtain ⟨D, hD⟩ := A.exists_omegaClosedClassifiedContactSegmentation
        s S hchange hS E
      exact ⟨.omega D, hD⟩

/-- The infinite branch of the actual compressor assignment has an exact
mixed contact segmentation.  In the eventual case its true infinite suffix
is retained and classified; in the omega case every raw edge belongs to a
consecutive finite contact interval. -/
theorem exists_actualInfiniteClosedClassifiedContactSegmentation
    (A : PostClosureCompressorAssignment T)
    (s : {x // x ∈ Gamma.initialSet A.fractured.outside.holes.paths \
      Gamma.initialSet (outsideReference T.intervalReference Rlimit.closedSet)})
    (S : RunCompressor.InfiniteInput Gamma.graph)
    (hchange : ∀ n, ∃ m, n < m ∧ S.colour m ≠ S.colour n)
    (hS : A.assignment.produced.bracket.assignment.assigned s =
      .infinite (S.toInfiniteRunWalk hchange).toInfiniteTrace) :
    Nonempty (ClosedClassifiedContactSegmentation
      (Y := C.ladder.limitWarp) (kappa := kappa)
      (.infinite (S.toInfiniteRunWalk hchange).toInfiniteTrace)
      Rlimit.closedSet C.persistent) := by
  obtain ⟨D, _hD⟩ :=
    A.exists_actualInfiniteClosedClassifiedContactSegmentation_with_contactSet_subset
      s S hchange hS
  exact ⟨D⟩

#print axioms exists_actualInfiniteClosedClassifiedContactSegmentation_with_contactSet_subset
#print axioms exists_actualInfiniteClosedClassifiedContactSegmentation

end Erdos599.Blueprint.LinkageBlueprint.PostClosureCompressorAssignment
