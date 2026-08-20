import ErdosProblems.Erdos733.ST.SimpleClosedPolygonalCurve

open Classical
noncomputable section

-- [TABLET NODE: FinitePolygonalSetCyclicPieceSourceNotSegmentTarget]
lemma FinitePolygonalSetCyclicPieceSourceNotSegmentTarget
    (J : SimpleClosedPolygonalCurve)
    (E : List {γ : PolygonalArc // γ ∈ J.edgeArcs})
    (segmentIndex_lt :
      (e : Fin E.length) →
        (n : Fin ((E[e.1]'e.2).1.vertices.length - 1)) →
          n.1 + 1 < (E[e.1]'e.2).1.vertices.length)
    (cutList :
      (e : Fin E.length) →
        Fin ((E[e.1]'e.2).1.vertices.length - 1) → List ℝ)
    (cutList_bounds : ∀ e n t, t ∈ cutList e n → 0 ≤ t ∧ t ≤ 1)
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
    (pieceSourceParam :
      (Sigma (fun e : Fin E.length =>
        Sigma (fun n : Fin ((E[e.1]'e.2).1.vertices.length - 1) =>
          localPieceIndex e n))) → Set.Icc (0 : ℝ) 1)
    (pieceTargetParam :
      (Sigma (fun e : Fin E.length =>
        Sigma (fun n : Fin ((E[e.1]'e.2).1.vertices.length - 1) =>
          localPieceIndex e n))) → Set.Icc (0 : ℝ) 1)
    (pieceSourceParam_lt :
      ∀ i : Sigma (fun e : Fin E.length =>
        Sigma (fun n : Fin ((E[e.1]'e.2).1.vertices.length - 1) =>
          localPieceIndex e n)),
        pieceSourceParam i < pieceTargetParam i)
    (pieceTargetParam_eq :
      ∀ i : Sigma (fun e : Fin E.length =>
        Sigma (fun n : Fin ((E[e.1]'e.2).1.vertices.length - 1) =>
          localPieceIndex e n)),
        (pieceTargetParam i).1 =
          (cutList i.1 i.2.1)[pieceNumber i + 1]'(pieceNumber_lt i))
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
    ∀ i : PieceIndex,
      pieceSource i ≠
        (E[i.1.1]'i.1.2).1.vertices[i.2.1.1 + 1]'
          (segmentIndex_lt i.1 i.2.1) := by
-- BODY
  intro PieceIndex i hsource_terminal
  have hv_ne :
      (E[i.1.1]'i.1.2).1.vertices[i.2.1.1]'(Nat.lt_of_succ_lt
          (segmentIndex_lt i.1 i.2.1)) ≠
        (E[i.1.1]'i.1.2).1.vertices[i.2.1.1 + 1]'
          (segmentIndex_lt i.1 i.2.1) := by
    intro hv
    have hidx : i.2.1.1 = i.2.1.1 + 1 := by
      exact ((E[i.1.1]'i.1.2).1.simple_vertices.getElem_inj_iff).mp hv
    omega
  have hsource_one : (pieceSourceParam i).1 = 1 := by
    have hline :
        AffineMap.lineMap
            ((E[i.1.1]'i.1.2).1.vertices[i.2.1.1]'
              (Nat.lt_of_succ_lt (segmentIndex_lt i.1 i.2.1)))
            ((E[i.1.1]'i.1.2).1.vertices[i.2.1.1 + 1]'
              (segmentIndex_lt i.1 i.2.1))
            (pieceSourceParam i).1 =
          (E[i.1.1]'i.1.2).1.vertices[i.2.1.1 + 1]'
            (segmentIndex_lt i.1 i.2.1) := by
      simpa [pieceSource_eq i] using hsource_terminal
    exact ((AffineMap.lineMap_eq_right_iff).mp hline).resolve_left hv_ne
  have htarget_le : (pieceTargetParam i).1 ≤ 1 := by
    have hmem :
        (cutList i.1 i.2.1)[pieceNumber i + 1]'(pieceNumber_lt i) ∈
          cutList i.1 i.2.1 :=
      List.getElem_mem (l := cutList i.1 i.2.1)
        (n := pieceNumber i + 1) (h := pieceNumber_lt i)
    have hbounds :=
      cutList_bounds i.1 i.2.1
        ((cutList i.1 i.2.1)[pieceNumber i + 1]'(pieceNumber_lt i))
        hmem
    simpa [pieceTargetParam_eq i] using hbounds.2
  have hlt_one : (1 : ℝ) < (pieceTargetParam i).1 := by
    have hraw : (pieceSourceParam i).1 < (pieceTargetParam i).1 :=
      pieceSourceParam_lt i
    simpa [hsource_one] using hraw
  exact (not_lt_of_ge htarget_le hlt_one)
