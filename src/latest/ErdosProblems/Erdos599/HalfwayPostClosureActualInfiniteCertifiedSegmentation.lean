/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.HalfwayPostClosureInfiniteCertifiedContactPiece
import ErdosProblems.Erdos599.HalfwayPostClosureActualInfiniteSegmentation

/-!
# Certified actual infinite contact segmentation

The eventual and cofinal-contact branches retain their raw coordinate
enumerations.  Every bounded displayed piece is the literal coordinate
interval, and every shortcut-bearing piece has the exposed safe-path
certificate from the deterministic endpoint classifier.  The genuine
infinite suffix in the eventual branch is retained verbatim.
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

/-- Certified data for the finite-contact branch, including the true
shifted infinite suffix. -/
structure EventuallyCertifiedInfiniteContactSegmentation
    (S : RunCompressor.InfiniteInput Gamma.graph)
    (hchange : ∀ n, ∃ m, n < m ∧ S.colour m ≠ S.colour n) where
  coordinates : S.EventualContactCoordinates Rlimit.closedSet
  segmentation : EventuallyClosedClassifiedContactSegmentation
    (Y := C.ladder.limitWarp) (kappa := kappa)
    (.infinite (S.toInfiniteRunWalk hchange).toInfiniteTrace)
    Rlimit.closedSet C.persistent
  count_eq : segmentation.count = coordinates.count
  point_eq : ∀ i, segmentation.point i = S.vertex
    (coordinates.coord (Fin.cast
      (congrArg (fun n : Nat ↦ n + 1) count_eq) i))
  piece_path : ∀ i : Fin segmentation.count,
    (segmentation.piece i).path =
      .finite (coordinates.interval (Fin.cast count_eq i)
        ).toFiniteRunWalk.toFiniteTrace
  tail_path : segmentation.tail.path =
    .infinite ((S.shift coordinates.last).toInfiniteRunWalk
      (S.shift_changes hchange coordinates.last)).toInfiniteTrace
  contactSet_subset : segmentation.toChain.contactSet ⊆ Rlimit.closedSet
  shortcut_certificate : ∀ (i : Fin segmentation.count) e,
    e ∈ (segmentation.piece i).shortcutEdges →
      segmentation.point i.castSucc ∉ Gamma.vertexSet C.ladder.limitWarp ∧
      segmentation.point i.succ ∉ Gamma.vertexSet C.ladder.limitWarp ∧
      IsSafe C.ladder.limitWarp (segmentation.piece i).path ∧
      HammockEligible Rlimit.closedSet C.ladder.limitStrictRoof
        C.ladder.limitRoof (segmentation.point i.castSucc)
          (.vertex (segmentation.point i.succ)) ∧
      Disjoint (hammockInterior (segmentation.point i.castSucc)
        (.vertex (segmentation.point i.succ)) (segmentation.piece i).path)
          Rlimit.closedSet ∧
      ¬(segmentation.piece i).path.vertexSet ⊆ Rlimit.closedSet

/-- Certified data for the cofinal-contact branch. -/
structure OmegaCertifiedInfiniteContactSegmentation
    (S : RunCompressor.InfiniteInput Gamma.graph)
    (hchange : ∀ n, ∃ m, n < m ∧ S.colour m ≠ S.colour n) where
  coordinates : S.OmegaContactCoordinates Rlimit.closedSet
  segmentation : OmegaClosedClassifiedContactSegmentation
    (Y := C.ladder.limitWarp) (kappa := kappa)
    (.infinite (S.toInfiniteRunWalk hchange).toInfiniteTrace)
    Rlimit.closedSet
  point_eq : ∀ i, segmentation.point i = S.vertex (coordinates.coord i)
  piece_path : ∀ i, (segmentation.piece i).path =
    .finite (coordinates.interval i).toFiniteRunWalk.toFiniteTrace
  contactSet_subset : segmentation.toChain.contactSet ⊆ Rlimit.closedSet
  shortcut_certificate : ∀ i e,
    e ∈ (segmentation.piece i).shortcutEdges →
      segmentation.point i ∉ Gamma.vertexSet C.ladder.limitWarp ∧
      segmentation.point (i + 1) ∉ Gamma.vertexSet C.ladder.limitWarp ∧
      IsSafe C.ladder.limitWarp (segmentation.piece i).path ∧
      HammockEligible Rlimit.closedSet C.ladder.limitStrictRoof
        C.ladder.limitRoof (segmentation.point i)
          (.vertex (segmentation.point (i + 1))) ∧
      Disjoint (hammockInterior (segmentation.point i)
        (.vertex (segmentation.point (i + 1))) (segmentation.piece i).path)
          Rlimit.closedSet ∧
      ¬(segmentation.piece i).path.vertexSet ⊆ Rlimit.closedSet

/-- The actual infinite contact dichotomy with certificates retained in
both branches. -/
inductive CertifiedInfiniteContactSegmentation
    (S : RunCompressor.InfiniteInput Gamma.graph)
    (hchange : ∀ n, ∃ m, n < m ∧ S.colour m ≠ S.colour n)
    | eventual : EventuallyCertifiedInfiniteContactSegmentation
        (C := C) (Rlimit := Rlimit) S hchange →
        CertifiedInfiniteContactSegmentation S hchange
    | omega : OmegaCertifiedInfiniteContactSegmentation
        (C := C) (Rlimit := Rlimit) S hchange →
        CertifiedInfiniteContactSegmentation S hchange

namespace CertifiedInfiniteContactSegmentation

def toClosedClassified
    {S : RunCompressor.InfiniteInput Gamma.graph}
    {hchange : ∀ n, ∃ m, n < m ∧ S.colour m ≠ S.colour n}
    (D : CertifiedInfiniteContactSegmentation
      (C := C) (Rlimit := Rlimit) S hchange) :
    ClosedClassifiedContactSegmentation
      (Y := C.ladder.limitWarp) (kappa := kappa)
      (.infinite (S.toInfiniteRunWalk hchange).toInfiniteTrace)
      Rlimit.closedSet C.persistent :=
  match D with
  | .eventual E => .eventually E.segmentation
  | .omega E => .omega E.segmentation

theorem contactSet_subset
    {S : RunCompressor.InfiniteInput Gamma.graph}
    {hchange : ∀ n, ∃ m, n < m ∧ S.colour m ≠ S.colour n}
    (D : CertifiedInfiniteContactSegmentation
      (C := C) (Rlimit := Rlimit) S hchange) :
    D.toClosedClassified.contactSet ⊆ Rlimit.closedSet := by
  cases D with
  | eventual E => exact E.contactSet_subset
  | omega E => exact E.contactSet_subset

end CertifiedInfiniteContactSegmentation

/-- Construct the certified finite-contact branch for a fixed enumeration. -/
theorem exists_eventuallyCertifiedInfiniteContactSegmentation
    (A : PostClosureCompressorAssignment T)
    (s : {x // x ∈ Gamma.initialSet A.fractured.outside.holes.paths \
      Gamma.initialSet (outsideReference T.intervalReference Rlimit.closedSet)})
    (S : RunCompressor.InfiniteInput Gamma.graph)
    (hchange : ∀ n, ∃ m, n < m ∧ S.colour m ≠ S.colour n)
    (hS : A.assignment.produced.bracket.assignment.assigned s =
      .infinite (S.toInfiniteRunWalk hchange).toInfiniteTrace)
    (E : S.EventualContactCoordinates Rlimit.closedSet) :
    Nonempty (EventuallyCertifiedInfiniteContactSegmentation
      (C := C) (Rlimit := Rlimit) S hchange) := by
  classical
  have hexists (i : Fin E.count) :=
    A.exists_infiniteCoordinateContactPiece_with_certificate s S hchange hS
      (E.coord i.castSucc) (E.coord i.succ)
      (E.strictMono_coord Fin.castSucc_lt_succ)
      (E.coord_mem i.castSucc) (E.coord_mem i.succ)
      (E.interval_hammockInterior_disjoint i)
  let piece : (i : Fin E.count) →
      ClassifiedOrClosedFiniteContactPiece
        (Y := C.ladder.limitWarp) (kappa := kappa)
        (.infinite (S.toInfiniteRunWalk hchange).toInfiniteTrace)
        Rlimit.closedSet (S.vertex (E.coord i.castSucc))
          (S.vertex (E.coord i.succ)) := fun i ↦ Classical.choose (hexists i)
  have piece_spec (i : Fin E.count) := Classical.choose_spec (hexists i)
  let tail := A.infiniteContactTail s S hchange hS E.last
    (E.coord_mem ⟨E.count, Nat.lt_succ_self _⟩)
    (E.suffix_hammockInterior_disjoint hchange)
    (E.suffix_not_subset hchange)
  have tail_path : tail.path =
      .infinite ((S.shift E.last).toInfiniteRunWalk
        (S.shift_changes hchange E.last)).toInfiniteTrace :=
    infiniteContactTail_path A s S hchange hS E.last
      (E.coord_mem ⟨E.count, Nat.lt_succ_self _⟩)
      (E.suffix_hammockInterior_disjoint hchange)
      (E.suffix_not_subset hchange)
  let D : EventuallyClosedClassifiedContactSegmentation
      (Y := C.ladder.limitWarp) (kappa := kappa)
      (.infinite (S.toInfiniteRunWalk hchange).toInfiniteTrace)
      Rlimit.closedSet C.persistent := {
    count := E.count
    point := fun i ↦ S.vertex (E.coord i)
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
        Set.range (fun i ↦ S.vertex (E.coord i)) ∪
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
          rw [(piece_spec i).1]
          exact hxi
        · right
          rw [tail_path]
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
        rw [show E.interval i = S.coordinateInterval
          (E.coord i.castSucc) (E.coord i.succ)
          (E.strictMono_coord Fin.castSucc_lt_succ) from rfl]
        rw [(piece_spec i).1]
        rfl
      rw [hpieces, tail_path]
      rfl
  }
  refine ⟨{
    coordinates := E
    segmentation := D
    count_eq := rfl
    point_eq := fun _ ↦ rfl
    piece_path := fun i ↦ (piece_spec i).1
    tail_path := tail_path
    contactSet_subset := ?_
    shortcut_certificate := ?_
  }⟩
  · rintro x hx
    change x ∈ Set.range (fun i ↦ S.vertex (E.coord i)) at hx
    obtain ⟨i, rfl⟩ := hx
    exact E.coord_mem i
  · intro i e he
    exact (piece_spec i).2 e he

/-- Construct the certified cofinal-contact branch for a fixed enumeration. -/
theorem exists_omegaCertifiedInfiniteContactSegmentation
    (A : PostClosureCompressorAssignment T)
    (s : {x // x ∈ Gamma.initialSet A.fractured.outside.holes.paths \
      Gamma.initialSet (outsideReference T.intervalReference Rlimit.closedSet)})
    (S : RunCompressor.InfiniteInput Gamma.graph)
    (hchange : ∀ n, ∃ m, n < m ∧ S.colour m ≠ S.colour n)
    (hS : A.assignment.produced.bracket.assignment.assigned s =
      .infinite (S.toInfiniteRunWalk hchange).toInfiniteTrace)
    (E : S.OmegaContactCoordinates Rlimit.closedSet) :
    Nonempty (OmegaCertifiedInfiniteContactSegmentation
      (C := C) (Rlimit := Rlimit) S hchange) := by
  classical
  have hexists (i : Nat) :=
    A.exists_infiniteCoordinateContactPiece_with_certificate s S hchange hS
      (E.coord i) (E.coord (i + 1))
      (E.strictMono_coord (Nat.lt_succ_self i))
      (E.coord_mem i) (E.coord_mem (i + 1))
      (E.interval_hammockInterior_disjoint i)
  let piece : (i : Nat) →
      ClassifiedOrClosedFiniteContactPiece
        (Y := C.ladder.limitWarp) (kappa := kappa)
        (.infinite (S.toInfiniteRunWalk hchange).toInfiniteTrace)
        Rlimit.closedSet (S.vertex (E.coord i))
          (S.vertex (E.coord (i + 1))) := fun i ↦ Classical.choose (hexists i)
  have piece_spec (i : Nat) := Classical.choose_spec (hexists i)
  let D : OmegaClosedClassifiedContactSegmentation
      (Y := C.ladder.limitWarp) (kappa := kappa)
      (.infinite (S.toInfiniteRunWalk hchange).toInfiniteTrace)
      Rlimit.closedSet := {
    point := fun i ↦ S.vertex (E.coord i)
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
        Set.range (fun i ↦ S.vertex (E.coord i)) ∪
          ⋃ i, (piece i).path.vertexSet
      apply Set.Subset.antisymm
      · intro x hx
        right
        rw [E.trace_vertexSet_exact hchange] at hx
        simp only [Set.mem_iUnion] at hx ⊢
        obtain ⟨i, hxi⟩ := hx
        refine ⟨i, ?_⟩
        rw [(piece_spec i).1]
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
      rw [show E.interval i = S.coordinateInterval
        (E.coord i) (E.coord (i + 1))
        (E.strictMono_coord (Nat.lt_succ_self i)) from rfl]
      rw [(piece_spec i).1]
      rfl
  }
  refine ⟨{
    coordinates := E
    segmentation := D
    point_eq := fun _ ↦ rfl
    piece_path := fun i ↦ (piece_spec i).1
    contactSet_subset := ?_
    shortcut_certificate := ?_
  }⟩
  · rintro x hx
    change x ∈ Set.range (fun i ↦ S.vertex (E.coord i)) at hx
    obtain ⟨i, rfl⟩ := hx
    exact E.coord_mem i
  · intro i e he
    exact (piece_spec i).2 e he

/-- Total actual infinite producer with the contact dichotomy and all
shortcut certificates retained. -/
theorem exists_actualInfiniteCertifiedContactSegmentation
    (A : PostClosureCompressorAssignment T)
    (s : {x // x ∈ Gamma.initialSet A.fractured.outside.holes.paths \
      Gamma.initialSet (outsideReference T.intervalReference Rlimit.closedSet)})
    (S : RunCompressor.InfiniteInput Gamma.graph)
    (hchange : ∀ n, ∃ m, n < m ∧ S.colour m ≠ S.colour n)
    (hS : A.assignment.produced.bracket.assignment.assigned s =
      .infinite (S.toInfiniteRunWalk hchange).toInfiniteTrace) :
    Nonempty (CertifiedInfiniteContactSegmentation
      (C := C) (Rlimit := Rlimit) S hchange) := by
  have hzero : S.vertex 0 ∈ Rlimit.closedSet := by
    have hsX : s.1 ∈ Rlimit.closedSet :=
      T.uncovered_initials_subset_closedSet Rlimit A.fractured s.2
    have hstart := A.assignment.produced.bracket.assignment.starts_at s
    rw [hS] at hstart
    rw [← hstart] at hsX
    change (S.toInfiniteRunWalk hchange).toInfiniteTrace.initial ∈
      Rlimit.closedSet at hsX
    rw [(S.toInfiniteRunWalk hchange).toInfiniteTrace_initial] at hsX
    exact hsX
  cases S.contactDichotomy Rlimit.closedSet hzero with
  | eventual E =>
      obtain ⟨D⟩ := A.exists_eventuallyCertifiedInfiniteContactSegmentation
        s S hchange hS E
      exact ⟨.eventual D⟩
  | omega E =>
      obtain ⟨D⟩ := A.exists_omegaCertifiedInfiniteContactSegmentation
        s S hchange hS E
      exact ⟨.omega D⟩

#print axioms exists_eventuallyCertifiedInfiniteContactSegmentation
#print axioms exists_omegaCertifiedInfiniteContactSegmentation
#print axioms exists_actualInfiniteCertifiedContactSegmentation

end Erdos599.Blueprint.LinkageBlueprint.PostClosureCompressorAssignment
