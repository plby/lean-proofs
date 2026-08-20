import ErdosProblems.Erdos733.ST.FinitePolygonalSetCyclicElementarySegmentCutList

open Classical
noncomputable section

-- [TABLET NODE: FinitePolygonalSetCyclicElementarySegmentOccurrenceFamily]
lemma FinitePolygonalSetCyclicElementarySegmentOccurrenceFamily
    (J : SimpleClosedPolygonalCurve) (K : FinitePolygonalSet)
    (γ : {γ : PolygonalArc // γ ∈ J.edgeArcs}) (n : ℕ)
    (hn : n + 1 < γ.1.vertices.length) :
    ∃ L : List ℝ,
      L.Nodup ∧
        L.SortedLT ∧
          (∀ t : ℝ, t ∈ L ↔
            t = 0 ∨ t = 1 ∨
              (0 ≤ t ∧ t ≤ 1 ∧
                AffineMap.lineMap
                  (γ.1.vertices[n]'(Nat.lt_of_succ_lt hn))
                  (γ.1.vertices[n + 1]'hn) t ∈ K.points)) ∧
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
                                    (γ.1.vertices[n]'(Nat.lt_of_succ_lt hn))
                                    (γ.1.vertices[n + 1]'hn)
                                    (pieceSourceParam i).1) ∧
                                (∀ i,
                                  pieceTarget i =
                                    AffineMap.lineMap
                                      (γ.1.vertices[n]'(Nat.lt_of_succ_lt hn))
                                      (γ.1.vertices[n + 1]'hn)
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
-- BODY
  let A : EuclideanSpace ℝ (Fin 2) :=
    γ.1.vertices[n]'(Nat.lt_of_succ_lt hn)
  let B : EuclideanSpace ℝ (Fin 2) := γ.1.vertices[n + 1]'hn
  rcases FinitePolygonalSetCyclicElementarySegmentCutList J K γ n hn with
    ⟨L, hnodup, hsorted, hmem, hzero, hone, hbounds, hlt, _hparamGap,
      hopenGap⟩
  let PieceIndex : Type := Fin (L.length - 1)
  let pieceNumber : PieceIndex → ℕ := fun i => i.1
  have pieceNumber_lt : ∀ i : PieceIndex, pieceNumber i + 1 < L.length := by
    intro i
    dsimp [pieceNumber, PieceIndex]
    omega
  have pieceNumber_surjective :
      ∀ k (hk : k + 1 < L.length), ∃ i : PieceIndex, pieceNumber i = k := by
    intro k hk
    refine ⟨⟨k, ?_⟩, rfl⟩
    omega
  have pieceNumber_injective :
      ∀ i j : PieceIndex, pieceNumber i = pieceNumber j → i = j := by
    intro i j hij
    exact Fin.ext hij
  let pieceSourceParam : PieceIndex → Set.Icc (0 : ℝ) 1 := fun i =>
    ⟨L[pieceNumber i]'(Nat.lt_of_succ_lt (pieceNumber_lt i)),
      hbounds _ (List.getElem_mem (l := L) (n := pieceNumber i)
        (Nat.lt_of_succ_lt (pieceNumber_lt i)))⟩
  let pieceTargetParam : PieceIndex → Set.Icc (0 : ℝ) 1 := fun i =>
    ⟨L[pieceNumber i + 1]'(pieceNumber_lt i),
      hbounds _ (List.getElem_mem (l := L) (n := pieceNumber i + 1)
        (pieceNumber_lt i))⟩
  let pieceSource : PieceIndex → EuclideanSpace ℝ (Fin 2) := fun i =>
    AffineMap.lineMap A B (pieceSourceParam i).1
  let pieceTarget : PieceIndex → EuclideanSpace ℝ (Fin 2) := fun i =>
    AffineMap.lineMap A B (pieceTargetParam i).1
  let pieceCarrier : PieceIndex → Set (EuclideanSpace ℝ (Fin 2)) := fun i =>
    segment ℝ (pieceSource i) (pieceTarget i)
  refine ⟨L, hnodup, hsorted, hmem, hzero, hone, hbounds, hlt, ?_⟩
  refine ⟨PieceIndex, inferInstance, pieceNumber, pieceNumber_lt,
    pieceNumber_surjective, pieceNumber_injective, pieceSourceParam,
    pieceTargetParam, pieceSource, pieceTarget, pieceCarrier, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_⟩
  · intro i
    change (pieceSourceParam i).1 < (pieceTargetParam i).1
    simpa [pieceSourceParam, pieceTargetParam] using
      hlt (pieceNumber i) (pieceNumber_lt i)
  · intro i
    rfl
  · intro i
    rfl
  · intro i
    simp [pieceSource, A, B]
  · intro i
    simp [pieceTarget, A, B]
  · intro i
    rfl
  · intro i p hp
    simpa [pieceSource, pieceTarget, pieceSourceParam, pieceTargetParam,
      A, B] using hopenGap (pieceNumber i) (pieceNumber_lt i) p hp
