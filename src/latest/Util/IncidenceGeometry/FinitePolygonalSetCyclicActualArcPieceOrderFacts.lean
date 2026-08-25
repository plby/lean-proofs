import Util.IncidenceGeometry.FinitePolygonalSetCyclicActualPieceCoverage
import Util.IncidenceGeometry.FinitePolygonalSetCyclicActualNormalizedSourceCycle
import Util.IncidenceGeometry.FinitePolygonalSetCyclicActualStreamIntervalBlocks
import Mathlib.Tactic

open Classical
noncomputable section


lemma FinitePolygonalSetCyclicActualArcPieceOrderFacts
    (J : SimpleClosedPolygonalCurve) (K : FinitePolygonalSet)
    (hKJ : K.carrier = J.carrier) :
    ∃ (PieceIndex : Type) (_pieceIndex_fintype : Fintype PieceIndex)
      (successor : Equiv.Perm {p : EuclideanSpace ℝ (Fin 2) // p ∈ K.points})
      (pieceArc : PieceIndex → {γ : PolygonalArc // γ ∈ J.edgeArcs})
      (pieceSegmentIndex :
        (i : PieceIndex) → {n : ℕ // n + 1 < (pieceArc i).1.vertices.length})
      (pieceSource pieceTarget : PieceIndex → EuclideanSpace ℝ (Fin 2))
      (pieceSourceParam pieceTargetParam : PieceIndex → Set.Icc (0 : ℝ) 1)
      (pieceCarrier : PieceIndex → Set (EuclideanSpace ℝ (Fin 2)))
      (arcPieceOrder :
        {p : EuclideanSpace ℝ (Fin 2) // p ∈ K.points} → List PieceIndex),
        (∀ i, pieceSourceParam i < pieceTargetParam i) ∧
          (∀ i,
            pieceSource i =
              AffineMap.lineMap
                ((pieceArc i).1.vertices[(pieceSegmentIndex i).1]'
                  (Nat.lt_of_succ_lt (pieceSegmentIndex i).2))
                ((pieceArc i).1.vertices[(pieceSegmentIndex i).1 + 1]'
                  (pieceSegmentIndex i).2)
                (pieceSourceParam i).1) ∧
          (∀ i,
            pieceTarget i =
              AffineMap.lineMap
                ((pieceArc i).1.vertices[(pieceSegmentIndex i).1]'
                  (Nat.lt_of_succ_lt (pieceSegmentIndex i).2))
                ((pieceArc i).1.vertices[(pieceSegmentIndex i).1 + 1]'
                  (pieceSegmentIndex i).2)
                (pieceTargetParam i).1) ∧
          (∀ i, pieceCarrier i = segment ℝ (pieceSource i) (pieceTarget i)) ∧
          (∀ i (v : EuclideanSpace ℝ (Fin 2)),
            v ∈ K.points → v ∉ openSegment ℝ (pieceSource i) (pieceTarget i)) ∧
          (∀ p : {p : EuclideanSpace ℝ (Fin 2) // p ∈ K.points},
            (arcPieceOrder p).length ≠ 0) ∧
          (∀ (p : {p : EuclideanSpace ℝ (Fin 2) // p ∈ K.points}) i,
            (arcPieceOrder p).head? = some i → pieceSource i = p.1) ∧
          (∀ (p : {p : EuclideanSpace ℝ (Fin 2) // p ∈ K.points}) i,
            (arcPieceOrder p).getLast? = some i →
              pieceTarget i = (successor p).1) ∧
          (∀ (p : {p : EuclideanSpace ℝ (Fin 2) // p ∈ K.points})
            n (hn : n + 1 < (arcPieceOrder p).length),
            pieceTarget ((arcPieceOrder p)[n]) =
                pieceSource ((arcPieceOrder p)[n + 1]) ∧
              ((pieceArc ((arcPieceOrder p)[n]) =
                    pieceArc ((arcPieceOrder p)[n + 1]) ∧
                  (pieceSegmentIndex ((arcPieceOrder p)[n])).1 =
                    (pieceSegmentIndex ((arcPieceOrder p)[n + 1])).1 ∧
                  pieceTargetParam ((arcPieceOrder p)[n]) =
                    pieceSourceParam ((arcPieceOrder p)[n + 1])) ∨
                (pieceArc ((arcPieceOrder p)[n]) =
                    pieceArc ((arcPieceOrder p)[n + 1]) ∧
                  (pieceSegmentIndex ((arcPieceOrder p)[n])).1 + 1 =
                    (pieceSegmentIndex ((arcPieceOrder p)[n + 1])).1 ∧
                  (pieceTargetParam ((arcPieceOrder p)[n])).1 = 1 ∧
                  (pieceSourceParam ((arcPieceOrder p)[n + 1])).1 = 0) ∨
                (pieceArc ((arcPieceOrder p)[n + 1]) =
                    J.successor (pieceArc ((arcPieceOrder p)[n])) ∧
                  (pieceSegmentIndex ((arcPieceOrder p)[n])).1 + 2 =
                    (pieceArc ((arcPieceOrder p)[n])).1.vertices.length ∧
                  (pieceSegmentIndex ((arcPieceOrder p)[n + 1])).1 = 0 ∧
                  (pieceTargetParam ((arcPieceOrder p)[n])).1 = 1 ∧
                  (pieceSourceParam ((arcPieceOrder p)[n + 1])).1 = 0))) ∧
          (∀ (p : {p : EuclideanSpace ℝ (Fin 2) // p ∈ K.points}) i,
            i ∈ (arcPieceOrder p).tail → pieceSource i ∉ K.points) ∧
          (∀ (p : {p : EuclideanSpace ℝ (Fin 2) // p ∈ K.points}) i,
            i ∈ arcPieceOrder p → pieceSource i ∈ K.points →
              pieceSource i = p.1) ∧
          (∀ (p : {p : EuclideanSpace ℝ (Fin 2) // p ∈ K.points}) i,
            i ∈ arcPieceOrder p → pieceTarget i ∈ K.points →
              pieceTarget i = (successor p).1) ∧
          (∀ p q : {p : EuclideanSpace ℝ (Fin 2) // p ∈ K.points},
            ∃ n : ℕ, (successor^[n]) p = q) ∧
          (∀ p : {p : EuclideanSpace ℝ (Fin 2) // p ∈ K.points},
            p.1 ≠ (successor p).1) := by
  rcases FinitePolygonalSetCyclicActualPieceCoverage J K hKJ with
    ⟨PieceIndex, pieceIndexFintype, successor, pieceArc, pieceSegmentIndex,
      pieceSource, pieceTarget, pieceSourceParam, pieceTargetParam,
      pieceCarrier, arcPieceOrder, pieceSourceParam_lt, pieceSource_eq,
      pieceTarget_eq, pieceCarrier_eq, no_listed_open_piece,
      arcPieceOrder_nonempty, arcPieceOrder_head_source,
      arcPieceOrder_last_target, arcPieceOrder_consecutive,
      arcPieceOrder_tail_no_source, pieceSource_listed_eq_start,
      pieceTarget_listed_eq_target, successor_cycle, successor_nondeg,
      _pieceCarrier_covers_curve⟩
  exact
    ⟨PieceIndex, pieceIndexFintype, successor, pieceArc, pieceSegmentIndex,
      pieceSource, pieceTarget, pieceSourceParam, pieceTargetParam,
      pieceCarrier, arcPieceOrder, pieceSourceParam_lt, pieceSource_eq,
      pieceTarget_eq, pieceCarrier_eq, no_listed_open_piece,
      arcPieceOrder_nonempty, arcPieceOrder_head_source,
      arcPieceOrder_last_target, arcPieceOrder_consecutive,
      arcPieceOrder_tail_no_source, pieceSource_listed_eq_start,
      pieceTarget_listed_eq_target, successor_cycle, successor_nondeg⟩

