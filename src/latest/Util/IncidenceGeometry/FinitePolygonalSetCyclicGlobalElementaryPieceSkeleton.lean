import Util.IncidenceGeometry.FinitePolygonalSetCyclicElementarySegmentOccurrenceFamily
import Util.IncidenceGeometry.SimpleClosedPolygonalCurveEdgeArcTraversalList

open Classical
noncomputable section

lemma FinitePolygonalSetCyclicGlobalElementaryPieceSkeleton
    (J : SimpleClosedPolygonalCurve) (K : FinitePolygonalSet) :
    ∃ E : List {γ : PolygonalArc // γ ∈ J.edgeArcs},
      E.Nodup ∧
        (∀ γ : {γ : PolygonalArc // γ ∈ J.edgeArcs}, γ ∈ E) ∧
          0 < E.length ∧
            (∀ n (hn : n + 1 < E.length),
              J.successor (E[n]) = E[n + 1]) ∧
              (∀ (hLast : E.length - 1 < E.length) (hFirst : 0 < E.length),
                J.successor (E[E.length - 1]'hLast) = E[0]'hFirst) ∧
                ∃ (segmentIndex_lt :
                  (e : Fin E.length) →
                    (n : Fin ((E[e.1]'e.2).1.vertices.length - 1)) →
                      n.1 + 1 < (E[e.1]'e.2).1.vertices.length)
                  (cutList :
                    (e : Fin E.length) →
                      Fin ((E[e.1]'e.2).1.vertices.length - 1) → List ℝ),
                    (∀ e n, (cutList e n).Nodup) ∧
                      (∀ e n, (cutList e n).SortedLT) ∧
                        (∀ e n (t : ℝ), t ∈ cutList e n ↔
                          t = 0 ∨ t = 1 ∨
                            (0 ≤ t ∧ t ≤ 1 ∧
                              AffineMap.lineMap
                                ((E[e.1]'e.2).1.vertices[n.1]'
                                  (Nat.lt_of_succ_lt
                                    (segmentIndex_lt e n)))
                                ((E[e.1]'e.2).1.vertices[n.1 + 1]'
                                  (segmentIndex_lt e n)) t ∈ K.points)) ∧
                          (∀ e n, (0 : ℝ) ∈ cutList e n) ∧
                            (∀ e n, (1 : ℝ) ∈ cutList e n) ∧
                              (∀ e n t, t ∈ cutList e n →
                                0 ≤ t ∧ t ≤ 1) ∧
                                (∀ e n k
                                  (hk : k + 1 < (cutList e n).length),
                                  (cutList e n)[k] <
                                    (cutList e n)[k + 1]) ∧
                                  ∃ (localPieceIndex :
                                    (e : Fin E.length) →
                                      Fin
                                        ((E[e.1]'e.2).1.vertices.length - 1) →
                                        Type)
                                    (_localPieceFintype :
                                      (e : Fin E.length) →
                                        (n : Fin
                                          ((E[e.1]'e.2).1.vertices.length - 1)) →
                                          Fintype (localPieceIndex e n)),
                                    let PieceIndex : Type :=
                                      Sigma (fun e : Fin E.length =>
                                        Sigma (fun n :
                                          Fin
                                            ((E[e.1]'e.2).1.vertices.length -
                                              1) =>
                                            localPieceIndex e n))
                                    ∃ (_pieceIndexFintype : Fintype PieceIndex)
                                      (pieceNumber : PieceIndex → ℕ)
                                      (pieceNumber_lt :
                                        ∀ i,
                                          pieceNumber i + 1 <
                                            (cutList i.1 i.2.1).length)
                                      (pieceEdgePosition :
                                        PieceIndex → Fin E.length)
                                      (pieceArc :
                                        PieceIndex →
                                          {γ : PolygonalArc // γ ∈ J.edgeArcs})
                                      (pieceSegmentIndex :
                                        (i : PieceIndex) →
                                          {n : ℕ // n + 1 <
                                            (E[i.1.1]'i.1.2).1.vertices.length})
                                      (pieceSourceParam :
                                        PieceIndex → Set.Icc (0 : ℝ) 1)
                                      (pieceTargetParam :
                                        PieceIndex → Set.Icc (0 : ℝ) 1)
                                      (pieceSource :
                                        PieceIndex → EuclideanSpace ℝ (Fin 2))
                                      (pieceTarget :
                                        PieceIndex → EuclideanSpace ℝ (Fin 2))
                                      (pieceCarrier :
                                        PieceIndex →
                                          Set (EuclideanSpace ℝ (Fin 2))),
                                        (∀ i, pieceEdgePosition i = i.1) ∧
                                          (∀ i,
                                            pieceArc i =
                                              E[(pieceEdgePosition i).1]'
                                                (pieceEdgePosition i).2) ∧
                                            (∀ i,
                                              (pieceSegmentIndex i).1 =
                                                i.2.1.1) ∧
                                              (∀ e n k
                                                  (_hk : k + 1 <
                                                    (cutList e n).length),
                                                  ∃ a : localPieceIndex e n,
                                                    pieceNumber
                                                      ⟨e, ⟨n, a⟩⟩ = k) ∧
                                                  (∀ e n
                                                    (a b : localPieceIndex e n),
                                                    pieceNumber
                                                        ⟨e, ⟨n, a⟩⟩ =
                                                      pieceNumber
                                                        ⟨e, ⟨n, b⟩⟩ →
                                                      a = b) ∧
                                                    (∀ i,
                                                      pieceSourceParam i <
                                                        pieceTargetParam i) ∧
                                                      (∀ i,
                                                          (pieceSourceParam i).1 =
                                                          (cutList i.1 i.2.1)[pieceNumber i]'
                                                            (Nat.lt_of_succ_lt
                                                              (pieceNumber_lt i))) ∧
                                                        (∀ i,
                                                          (pieceTargetParam i).1 =
                                                            (cutList i.1 i.2.1)[pieceNumber i + 1]'
                                                              (pieceNumber_lt i)) ∧
                                                          (∀ i,
                                                            pieceSource i =
                                                              AffineMap.lineMap
                                                                ((E[i.1.1]'i.1.2).1.vertices[i.2.1.1]'
                                                                  (Nat.lt_of_succ_lt
                                                                    (segmentIndex_lt
                                                                      i.1 i.2.1)))
                                                                ((E[i.1.1]'i.1.2).1.vertices[i.2.1.1 + 1]'
                                                                  (segmentIndex_lt
                                                                    i.1 i.2.1))
                                                                (pieceSourceParam i).1) ∧
                                                            (∀ i,
                                                              pieceTarget i =
                                                                AffineMap.lineMap
                                                                  ((E[i.1.1]'i.1.2).1.vertices[i.2.1.1]'
                                                                    (Nat.lt_of_succ_lt
                                                                      (segmentIndex_lt
                                                                        i.1 i.2.1)))
                                                                  ((E[i.1.1]'i.1.2).1.vertices[i.2.1.1 + 1]'
                                                                    (segmentIndex_lt
                                                                      i.1 i.2.1))
                                                                  (pieceTargetParam i).1) ∧
                                                              (∀ i,
                                                                pieceCarrier i =
                                                                  segment ℝ
                                                                    (pieceSource i)
                                                                    (pieceTarget i)) ∧
                                                                (∀ i
                                                                  (p :
                                                                    EuclideanSpace
                                                                      ℝ (Fin 2)),
                                                                  p ∈ K.points →
                                                                    p ∉ openSegment ℝ
                                                                      (pieceSource i)
                                                                      (pieceTarget i)) := by
  classical
  rcases SimpleClosedPolygonalCurveEdgeArcTraversalList J with
    ⟨E, hEnodup, hEall, hEpos, hEsucc, hEwrap⟩
  let SegmentIndex : Fin E.length → Type := fun e =>
    Fin ((E[e.1]'e.2).1.vertices.length - 1)
  have segmentIndex_lt :
      ∀ (e : Fin E.length) (n : SegmentIndex e),
        n.1 + 1 < (E[e.1]'e.2).1.vertices.length := by
    intro e n
    have hn : n.1 < (E[e.1]'e.2).1.vertices.length - 1 := n.2
    have hlen : 2 ≤ (E[e.1]'e.2).1.vertices.length :=
      (E[e.1]'e.2).1.length_ge_two
    omega
  have local_exists :
      ∀ (e : Fin E.length) (n : SegmentIndex e),
        ∃ L : List ℝ,
          L.Nodup ∧
            L.SortedLT ∧
              (∀ t : ℝ, t ∈ L ↔
                t = 0 ∨ t = 1 ∨
                  (0 ≤ t ∧ t ≤ 1 ∧
                    AffineMap.lineMap
                      ((E[e.1]'e.2).1.vertices[n.1]'(Nat.lt_of_succ_lt
                        (segmentIndex_lt e n)))
                      ((E[e.1]'e.2).1.vertices[n.1 + 1]'
                        (segmentIndex_lt e n)) t ∈ K.points)) ∧
                (0 : ℝ) ∈ L ∧
                  (1 : ℝ) ∈ L ∧
                    (∀ t : ℝ, t ∈ L → 0 ≤ t ∧ t ≤ 1) ∧
                      (∀ k (hk : k + 1 < L.length), L[k] < L[k + 1]) ∧
                        ∃ (pieceIndex : Type) (_ : Fintype pieceIndex)
                          (pieceNumber : pieceIndex → ℕ)
                          (pieceNumber_lt :
                            ∀ i, pieceNumber i + 1 < L.length)
                          (_pieceNumber_surjective :
                            ∀ k (_hk : k + 1 < L.length),
                              ∃ i, pieceNumber i = k)
                          (_pieceNumber_injective :
                            ∀ i j, pieceNumber i = pieceNumber j → i = j)
                          (pieceSourceParam :
                            pieceIndex → Set.Icc (0 : ℝ) 1)
                          (pieceTargetParam :
                            pieceIndex → Set.Icc (0 : ℝ) 1)
                          (pieceSource :
                            pieceIndex → EuclideanSpace ℝ (Fin 2))
                          (pieceTarget :
                            pieceIndex → EuclideanSpace ℝ (Fin 2))
                          (pieceCarrier :
                            pieceIndex → Set (EuclideanSpace ℝ (Fin 2))),
                            (∀ i, pieceSourceParam i < pieceTargetParam i) ∧
                              (∀ i,
                                (pieceSourceParam i).1 =
                                  L[pieceNumber i]'(Nat.lt_of_succ_lt
                                    (pieceNumber_lt i))) ∧
                                (∀ i,
                                  (pieceTargetParam i).1 =
                                    L[pieceNumber i + 1]'(pieceNumber_lt i)) ∧
                                  (∀ i,
                                    pieceSource i =
                                      AffineMap.lineMap
                                        ((E[e.1]'e.2).1.vertices[n.1]'
                                          (Nat.lt_of_succ_lt
                                            (segmentIndex_lt e n)))
                                        ((E[e.1]'e.2).1.vertices[n.1 + 1]'
                                          (segmentIndex_lt e n))
                                        (pieceSourceParam i).1) ∧
                                    (∀ i,
                                      pieceTarget i =
                                        AffineMap.lineMap
                                          ((E[e.1]'e.2).1.vertices[n.1]'
                                            (Nat.lt_of_succ_lt
                                              (segmentIndex_lt e n)))
                                          ((E[e.1]'e.2).1.vertices[n.1 + 1]'
                                            (segmentIndex_lt e n))
                                          (pieceTargetParam i).1) ∧
                                      (∀ i,
                                        pieceCarrier i =
                                          segment ℝ (pieceSource i)
                                            (pieceTarget i)) ∧
                                        (∀ i
                                          (p : EuclideanSpace ℝ (Fin 2)),
                                          p ∈ K.points →
                                            p ∉ openSegment ℝ
                                              (pieceSource i) (pieceTarget i)) := by
    intro e n
    exact FinitePolygonalSetCyclicElementarySegmentOccurrenceFamily
      J K (E[e.1]'e.2) n.1 (segmentIndex_lt e n)
  choose L hLnodup hLsorted hLmem hLzero hLone hLbounds hLlt
    localPieceExists using local_exists
  choose LocalPieceIndex localPieceFintype localPieceNumber
    localPieceNumber_lt localPieceNumber_surjective localPieceNumber_injective
    localPieceSourceParam localPieceTargetParam localPieceSource
    localPieceTarget localPieceCarrier localPieceFields using localPieceExists
  choose localSourceParam_lt localSourceParam_eq localTargetParam_eq
    localSource_eq localTarget_eq localCarrier_eq localNoListed using
      localPieceFields
  let PieceIndex : Type :=
    Sigma (fun e : Fin E.length =>
      Sigma (fun n : SegmentIndex e => LocalPieceIndex e n))
  have pieceIndexFintype : Fintype PieceIndex := by
    classical
    dsimp [PieceIndex]
    letI : (e : Fin E.length) → Fintype (SegmentIndex e) := fun _ =>
      inferInstance
    letI : (e : Fin E.length) → (n : SegmentIndex e) →
        Fintype (LocalPieceIndex e n) := localPieceFintype
    infer_instance
  let pieceNumber : PieceIndex → ℕ := fun i =>
    localPieceNumber i.1 i.2.1 i.2.2
  have pieceNumber_lt :
      ∀ i : PieceIndex, pieceNumber i + 1 < (L i.1 i.2.1).length := by
    intro i
    exact localPieceNumber_lt i.1 i.2.1 i.2.2
  let pieceEdgePosition : PieceIndex → Fin E.length := fun i => i.1
  let pieceArc : PieceIndex → {γ : PolygonalArc // γ ∈ J.edgeArcs} := fun i =>
    E[i.1.1]'i.1.2
  let pieceSegmentIndex :
      (i : PieceIndex) →
        {n : ℕ // n + 1 < (E[i.1.1]'i.1.2).1.vertices.length} :=
    fun i => ⟨i.2.1.1, segmentIndex_lt i.1 i.2.1⟩
  let pieceSourceParam : PieceIndex → Set.Icc (0 : ℝ) 1 := fun i =>
    localPieceSourceParam i.1 i.2.1 i.2.2
  let pieceTargetParam : PieceIndex → Set.Icc (0 : ℝ) 1 := fun i =>
    localPieceTargetParam i.1 i.2.1 i.2.2
  let pieceSource : PieceIndex → EuclideanSpace ℝ (Fin 2) := fun i =>
    localPieceSource i.1 i.2.1 i.2.2
  let pieceTarget : PieceIndex → EuclideanSpace ℝ (Fin 2) := fun i =>
    localPieceTarget i.1 i.2.1 i.2.2
  let pieceCarrier : PieceIndex → Set (EuclideanSpace ℝ (Fin 2)) := fun i =>
    localPieceCarrier i.1 i.2.1 i.2.2
  refine ⟨E, hEnodup, hEall, hEpos, hEsucc, hEwrap, ?_⟩
  refine ⟨segmentIndex_lt, L, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro e n
    exact hLnodup e n
  · intro e n
    exact hLsorted e n
  · intro e n t
    exact hLmem e n t
  · intro e n
    exact hLzero e n
  · intro e n
    exact hLone e n
  · intro e n t ht
    exact hLbounds e n t ht
  · intro e n k hk
    exact hLlt e n k hk
  · refine ⟨LocalPieceIndex, localPieceFintype, ?_⟩
    change
      ∃ (_pieceIndexFintype : Fintype PieceIndex)
        (pieceNumber : PieceIndex → ℕ)
        (pieceNumber_lt :
          ∀ i, pieceNumber i + 1 < (L i.1 i.2.1).length)
        (pieceEdgePosition : PieceIndex → Fin E.length)
        (pieceArc : PieceIndex → {γ : PolygonalArc // γ ∈ J.edgeArcs})
        (pieceSegmentIndex :
          (i : PieceIndex) →
            {n : ℕ // n + 1 < (E[i.1.1]'i.1.2).1.vertices.length})
        (pieceSourceParam : PieceIndex → Set.Icc (0 : ℝ) 1)
        (pieceTargetParam : PieceIndex → Set.Icc (0 : ℝ) 1)
        (pieceSource : PieceIndex → EuclideanSpace ℝ (Fin 2))
        (pieceTarget : PieceIndex → EuclideanSpace ℝ (Fin 2))
        (pieceCarrier : PieceIndex → Set (EuclideanSpace ℝ (Fin 2))),
          (∀ i, pieceEdgePosition i = i.1) ∧
            (∀ i,
              pieceArc i =
                E[(pieceEdgePosition i).1]'(pieceEdgePosition i).2) ∧
              (∀ i, (pieceSegmentIndex i).1 = i.2.1.1) ∧
                (∀ e n k (_hk : k + 1 < (L e n).length),
                  ∃ a : LocalPieceIndex e n, pieceNumber ⟨e, ⟨n, a⟩⟩ = k) ∧
                  (∀ e n (a b : LocalPieceIndex e n),
                    pieceNumber ⟨e, ⟨n, a⟩⟩ =
                        pieceNumber ⟨e, ⟨n, b⟩⟩ →
                      a = b) ∧
                    (∀ i, pieceSourceParam i < pieceTargetParam i) ∧
                      (∀ i,
                        (pieceSourceParam i).1 =
                          (L i.1 i.2.1)[pieceNumber i]'
                            (Nat.lt_of_succ_lt (pieceNumber_lt i))) ∧
                        (∀ i,
                          (pieceTargetParam i).1 =
                            (L i.1 i.2.1)[pieceNumber i + 1]'
                              (pieceNumber_lt i)) ∧
                          (∀ i,
                            pieceSource i =
                              AffineMap.lineMap
                                ((E[i.1.1]'i.1.2).1.vertices[i.2.1.1]'
                                  (Nat.lt_of_succ_lt
                                    (segmentIndex_lt i.1 i.2.1)))
                                ((E[i.1.1]'i.1.2).1.vertices[i.2.1.1 + 1]'
                                  (segmentIndex_lt i.1 i.2.1))
                                (pieceSourceParam i).1) ∧
                            (∀ i,
                              pieceTarget i =
                                AffineMap.lineMap
                                  ((E[i.1.1]'i.1.2).1.vertices[i.2.1.1]'
                                    (Nat.lt_of_succ_lt
                                      (segmentIndex_lt i.1 i.2.1)))
                                  ((E[i.1.1]'i.1.2).1.vertices[i.2.1.1 + 1]'
                                    (segmentIndex_lt i.1 i.2.1))
                                  (pieceTargetParam i).1) ∧
                              (∀ i,
                                pieceCarrier i =
                                  segment ℝ (pieceSource i) (pieceTarget i)) ∧
                                (∀ i (p : EuclideanSpace ℝ (Fin 2)),
                                  p ∈ K.points →
                                    p ∉ openSegment ℝ
                                      (pieceSource i) (pieceTarget i))
    refine ⟨pieceIndexFintype, pieceNumber, pieceNumber_lt,
      pieceEdgePosition, pieceArc, pieceSegmentIndex, pieceSourceParam,
      pieceTargetParam, pieceSource, pieceTarget, pieceCarrier, ?_, ?_, ?_,
      ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro i
      rfl
    · intro i
      rfl
    · intro i
      rfl
    · intro e n k hk
      exact localPieceNumber_surjective e n k hk
    · intro e n a b hab
      exact localPieceNumber_injective e n a b hab
    · intro i
      exact localSourceParam_lt i.1 i.2.1 i.2.2
    · intro i
      exact localSourceParam_eq i.1 i.2.1 i.2.2
    · intro i
      exact localTargetParam_eq i.1 i.2.1 i.2.2
    · intro i
      exact localSource_eq i.1 i.2.1 i.2.2
    · intro i
      exact localTarget_eq i.1 i.2.1 i.2.2
    · intro i
      exact localCarrier_eq i.1 i.2.1 i.2.2
    · intro i p hp
      exact localNoListed i.1 i.2.1 i.2.2 p hp
