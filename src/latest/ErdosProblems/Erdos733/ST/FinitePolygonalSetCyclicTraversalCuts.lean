import ErdosProblems.Erdos733.ST.SimpleClosedPolygonalCurve
import ErdosProblems.Erdos733.ST.FinitePolygonalSet

open Classical
noncomputable section

-- [TABLET NODE: FinitePolygonalSetCyclicTraversalCuts]
structure FinitePolygonalSetCyclicTraversalCuts
    (J : SimpleClosedPolygonalCurve) (K : FinitePolygonalSet) where
-- BODY
  successor : Equiv.Perm {p : EuclideanSpace ℝ (Fin 2) // p ∈ K.points}
  arcCarrier :
    {p : EuclideanSpace ℝ (Fin 2) // p ∈ K.points} →
      Set (EuclideanSpace ℝ (Fin 2))
  arcInterior :
    {p : EuclideanSpace ℝ (Fin 2) // p ∈ K.points} →
      Set (EuclideanSpace ℝ (Fin 2))
  pieceIndex : Type
  pieceIndex_fintype : Fintype pieceIndex
  pieceArc : pieceIndex → {γ : PolygonalArc // γ ∈ J.edgeArcs}
  pieceSegmentIndex :
    (i : pieceIndex) → {n : ℕ // n + 1 < (pieceArc i).1.vertices.length}
  pieceSource : pieceIndex → EuclideanSpace ℝ (Fin 2)
  pieceTarget : pieceIndex → EuclideanSpace ℝ (Fin 2)
  pieceSourceParam : pieceIndex → Set.Icc (0 : ℝ) 1
  pieceTargetParam : pieceIndex → Set.Icc (0 : ℝ) 1
  pieceSourceParam_lt_targetParam :
    ∀ i, pieceSourceParam i < pieceTargetParam i
  pieceSource_eq :
    ∀ i,
      pieceSource i =
        AffineMap.lineMap
          ((pieceArc i).1.vertices[(pieceSegmentIndex i).1]'
            (Nat.lt_of_succ_lt (pieceSegmentIndex i).2))
          ((pieceArc i).1.vertices[(pieceSegmentIndex i).1 + 1]'
            (pieceSegmentIndex i).2)
          (pieceSourceParam i).1
  pieceTarget_eq :
    ∀ i,
      pieceTarget i =
        AffineMap.lineMap
          ((pieceArc i).1.vertices[(pieceSegmentIndex i).1]'
            (Nat.lt_of_succ_lt (pieceSegmentIndex i).2))
          ((pieceArc i).1.vertices[(pieceSegmentIndex i).1 + 1]'
            (pieceSegmentIndex i).2)
          (pieceTargetParam i).1
  pieceCarrier : pieceIndex → Set (EuclideanSpace ℝ (Fin 2))
  pieceCarrier_eq :
    ∀ i, pieceCarrier i = segment ℝ (pieceSource i) (pieceTarget i)
  arcPieceOrder :
    {p : EuclideanSpace ℝ (Fin 2) // p ∈ K.points} → List pieceIndex
  arcPieceOrder_nonempty :
    ∀ p : {p : EuclideanSpace ℝ (Fin 2) // p ∈ K.points},
      (arcPieceOrder p).length ≠ 0
  arcPieceOrder_head_source :
    ∀ (p : {p : EuclideanSpace ℝ (Fin 2) // p ∈ K.points}) i,
      (arcPieceOrder p).head? = some i → pieceSource i = p.1
  arcPieceOrder_last_target :
    ∀ (p : {p : EuclideanSpace ℝ (Fin 2) // p ∈ K.points}) i,
      (arcPieceOrder p).getLast? = some i → pieceTarget i = (successor p).1
  arcPieceOrder_consecutive :
    ∀ (p : {p : EuclideanSpace ℝ (Fin 2) // p ∈ K.points})
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
          ((pieceArc ((arcPieceOrder p)[n + 1]) =
              J.successor (pieceArc ((arcPieceOrder p)[n])) ∧
            (pieceSegmentIndex ((arcPieceOrder p)[n])).1 + 2 =
              (pieceArc ((arcPieceOrder p)[n])).1.vertices.length ∧
            (pieceSegmentIndex ((arcPieceOrder p)[n + 1])).1 = 0 ∧
            (pieceTargetParam ((arcPieceOrder p)[n])).1 = 1 ∧
            (pieceSourceParam ((arcPieceOrder p)[n + 1])).1 = 0)))
  arcCarrier_eq_pieceOrder :
    ∀ p : {p : EuclideanSpace ℝ (Fin 2) // p ∈ K.points},
      arcCarrier p =
        ⋃ i : {i : pieceIndex // i ∈ arcPieceOrder p}, pieceCarrier i.1
  ordered_piece_open_subset_arcInterior :
    ∀ (p : {p : EuclideanSpace ℝ (Fin 2) // p ∈ K.points})
      (i : pieceIndex), i ∈ arcPieceOrder p →
        openSegment ℝ (pieceSource i) (pieceTarget i) ⊆ arcInterior p
  ordered_consecutive_junction_mem_arcInterior :
    ∀ (p : {p : EuclideanSpace ℝ (Fin 2) // p ∈ K.points})
      n (hn : n + 1 < (arcPieceOrder p).length),
      pieceTarget ((arcPieceOrder p)[n]) ∈ arcInterior p
  successor_single_cycle :
    ∀ p q : {p : EuclideanSpace ℝ (Fin 2) // p ∈ K.points},
      ∃ n : ℕ, (successor^[n]) p = q
  successor_nondegenerate :
    ∀ p : {p : EuclideanSpace ℝ (Fin 2) // p ∈ K.points},
      p.1 ≠ (successor p).1
  arc_start_mem :
    ∀ p : {p : EuclideanSpace ℝ (Fin 2) // p ∈ K.points},
      p.1 ∈ arcCarrier p
  arc_target_mem :
    ∀ p : {p : EuclideanSpace ℝ (Fin 2) // p ∈ K.points},
      (successor p).1 ∈ arcCarrier p
  arc_in_curve :
    ∀ p : {p : EuclideanSpace ℝ (Fin 2) // p ∈ K.points},
      arcCarrier p ⊆ J.carrier
  curve_covered_by_arcs :
    J.carrier ⊆
      ⋃ p : {p : EuclideanSpace ℝ (Fin 2) // p ∈ K.points}, arcCarrier p
  arcInterior_eq :
    ∀ p : {p : EuclideanSpace ℝ (Fin 2) // p ∈ K.points},
      arcInterior p =
        arcCarrier p \ ({p.1, (successor p).1} : Set (EuclideanSpace ℝ (Fin 2)))
  no_listed_point_in_arcInterior :
    ∀ (p : {p : EuclideanSpace ℝ (Fin 2) // p ∈ K.points})
      (v : EuclideanSpace ℝ (Fin 2)),
        v ∈ K.points → v ∉ arcInterior p
  arcInteriors_disjoint :
    ∀ p q : {p : EuclideanSpace ℝ (Fin 2) // p ∈ K.points},
      p ≠ q → Disjoint (arcInterior p) (arcInterior q)
