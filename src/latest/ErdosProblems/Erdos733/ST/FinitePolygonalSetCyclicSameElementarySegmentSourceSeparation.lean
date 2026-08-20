import ErdosProblems.Erdos733.ST.SimpleClosedPolygonalCurve

open Classical
noncomputable section

-- [TABLET NODE: FinitePolygonalSetCyclicSameElementarySegmentSourceSeparation]
lemma FinitePolygonalSetCyclicSameElementarySegmentSourceSeparation
    (J : SimpleClosedPolygonalCurve)
    (E : List {γ : PolygonalArc // γ ∈ J.edgeArcs})
    (segmentIndex_lt :
      (e : Fin E.length) →
        (n : Fin ((E[e.1]'e.2).1.vertices.length - 1)) →
          n.1 + 1 < (E[e.1]'e.2).1.vertices.length)
    (cutList :
      (e : Fin E.length) →
        Fin ((E[e.1]'e.2).1.vertices.length - 1) → List ℝ)
    (cutList_nodup : ∀ e n, (cutList e n).Nodup)
    (localPieceIndex :
      (e : Fin E.length) →
        Fin ((E[e.1]'e.2).1.vertices.length - 1) → Type)
    (pieceNumber :
      (Sigma (fun e : Fin E.length =>
        Sigma (fun n : Fin ((E[e.1]'e.2).1.vertices.length - 1) =>
          localPieceIndex e n))) → ℕ)
    (pieceNumber_lt :
      ∀ i : Sigma (fun e : Fin E.length =>
        Sigma (fun n : Fin ((E[e.1]'e.2).1.vertices.length - 1) =>
          localPieceIndex e n)),
        pieceNumber i + 1 < (cutList i.1 i.2.1).length)
    (pieceNumber_injective :
      ∀ e n (a b : localPieceIndex e n),
        pieceNumber ⟨e, ⟨n, a⟩⟩ =
          pieceNumber ⟨e, ⟨n, b⟩⟩ →
        a = b)
    (pieceSourceParam :
      (Sigma (fun e : Fin E.length =>
        Sigma (fun n : Fin ((E[e.1]'e.2).1.vertices.length - 1) =>
          localPieceIndex e n))) → Set.Icc (0 : ℝ) 1)
    (pieceSourceParam_eq :
      ∀ i : Sigma (fun e : Fin E.length =>
        Sigma (fun n : Fin ((E[e.1]'e.2).1.vertices.length - 1) =>
          localPieceIndex e n)),
        (pieceSourceParam i).1 =
          (cutList i.1 i.2.1)[pieceNumber i]'
            (Nat.lt_of_succ_lt (pieceNumber_lt i)))
    (pieceSource :
      (Sigma (fun e : Fin E.length =>
        Sigma (fun n : Fin ((E[e.1]'e.2).1.vertices.length - 1) =>
          localPieceIndex e n))) → EuclideanSpace ℝ (Fin 2))
    (pieceSource_eq :
      ∀ i : Sigma (fun e : Fin E.length =>
        Sigma (fun n : Fin ((E[e.1]'e.2).1.vertices.length - 1) =>
          localPieceIndex e n)),
        pieceSource i =
          AffineMap.lineMap
            ((E[i.1.1]'i.1.2).1.vertices[i.2.1.1]'
              (Nat.lt_of_succ_lt (segmentIndex_lt i.1 i.2.1)))
            ((E[i.1.1]'i.1.2).1.vertices[i.2.1.1 + 1]'
              (segmentIndex_lt i.1 i.2.1))
            (pieceSourceParam i).1) :
    let PieceIndex : Type :=
      Sigma (fun e : Fin E.length =>
        Sigma (fun n : Fin ((E[e.1]'e.2).1.vertices.length - 1) =>
          localPieceIndex e n))
    ∀ (e : Fin E.length)
      (n : Fin ((E[e.1]'e.2).1.vertices.length - 1))
      (a b : localPieceIndex e n),
      pieceSource (⟨e, ⟨n, a⟩⟩ : PieceIndex) =
        pieceSource (⟨e, ⟨n, b⟩⟩ : PieceIndex) →
        a = b := by
-- BODY
  intro PieceIndex e n a b hsource
  apply pieceNumber_injective e n a b
  have hv_ne :
      (E[e.1]'e.2).1.vertices[n.1]'(Nat.lt_of_succ_lt
          (segmentIndex_lt e n)) ≠
        (E[e.1]'e.2).1.vertices[n.1 + 1]'(segmentIndex_lt e n) := by
    intro hv
    have hidx : n.1 = n.1 + 1 := by
      exact ((E[e.1]'e.2).1.simple_vertices.getElem_inj_iff).mp hv
    omega
  have hparam :
      (pieceSourceParam (⟨e, ⟨n, a⟩⟩ : PieceIndex)).1 =
        (pieceSourceParam (⟨e, ⟨n, b⟩⟩ : PieceIndex)).1 := by
    exact (AffineMap.lineMap_injective ℝ hv_ne) (by
      rw [← pieceSource_eq (⟨e, ⟨n, a⟩⟩ : PieceIndex),
        ← pieceSource_eq (⟨e, ⟨n, b⟩⟩ : PieceIndex)]
      exact hsource)
  have hget :
      (cutList e n)[pieceNumber (⟨e, ⟨n, a⟩⟩ : PieceIndex)]'
          (Nat.lt_of_succ_lt (pieceNumber_lt (⟨e, ⟨n, a⟩⟩ : PieceIndex))) =
        (cutList e n)[pieceNumber (⟨e, ⟨n, b⟩⟩ : PieceIndex)]'
          (Nat.lt_of_succ_lt (pieceNumber_lt (⟨e, ⟨n, b⟩⟩ : PieceIndex))) := by
    rw [← pieceSourceParam_eq (⟨e, ⟨n, a⟩⟩ : PieceIndex),
      ← pieceSourceParam_eq (⟨e, ⟨n, b⟩⟩ : PieceIndex)]
    exact hparam
  exact (cutList_nodup e n).getElem_inj_iff.mp hget
