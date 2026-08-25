import Util.IncidenceGeometry.FinitePolygonalSetCyclicSameElementarySegmentSourceSeparation
import Util.IncidenceGeometry.FinitePolygonalSetCyclicPieceSourceNotSegmentTarget

open Classical
noncomputable section

lemma FinitePolygonalSetCyclicSameEdgeArcSourceSeparation
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
    (pieceNumber_injective :
      ∀ e n (a b : localPieceIndex e n),
        pieceNumber ⟨e, ⟨n, a⟩⟩ =
          pieceNumber ⟨e, ⟨n, b⟩⟩ →
        a = b)
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
    (pieceSourceParam_eq :
      ∀ i : Sigma (fun e : Fin E.length =>
        Sigma (fun n : Fin ((E[e.1]'e.2).1.vertices.length - 1) =>
          localPieceIndex e n)),
        (pieceSourceParam i).1 =
          (cutList i.1 i.2.1)[pieceNumber i]'
            (Nat.lt_of_succ_lt (pieceNumber_lt i)))
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
    ∀ (e : Fin E.length)
      (n m : Fin ((E[e.1]'e.2).1.vertices.length - 1))
      (a : localPieceIndex e n) (b : localPieceIndex e m),
      pieceSource (⟨e, ⟨n, a⟩⟩ : PieceIndex) =
        pieceSource (⟨e, ⟨m, b⟩⟩ : PieceIndex) →
      (⟨e, ⟨n, a⟩⟩ : PieceIndex) = ⟨e, ⟨m, b⟩⟩ := by
  intro PieceIndex e n m a b hsource
  by_cases hnm_val : n.1 = m.1
  · have hnm : n = m := Fin.ext hnm_val
    subst m
    have hab : a = b := by
      exact
        FinitePolygonalSetCyclicSameElementarySegmentSourceSeparation
          J E segmentIndex_lt cutList cutList_nodup localPieceIndex
          pieceNumber pieceNumber_lt pieceNumber_injective pieceSourceParam
          pieceSourceParam_eq pieceSource pieceSource_eq e n a b hsource
    subst b
    rfl
  · have source_mem_segment :
      ∀ (q : PieceIndex),
        pieceSource q ∈
          segment ℝ
            ((E[q.1.1]'q.1.2).1.vertices[q.2.1.1]'
              (Nat.lt_of_succ_lt (segmentIndex_lt q.1 q.2.1)))
            ((E[q.1.1]'q.1.2).1.vertices[q.2.1.1 + 1]'
              (segmentIndex_lt q.1 q.2.1)) := by
      intro q
      rw [pieceSource_eq q, segment_eq_image_lineMap]
      exact ⟨(pieceSourceParam q).1, (pieceSourceParam q).2, rfl⟩
    have source_not_segment_target :
      ∀ q : PieceIndex,
        pieceSource q ≠
          (E[q.1.1]'q.1.2).1.vertices[q.2.1.1 + 1]'
            (segmentIndex_lt q.1 q.2.1) := by
      intro q
      exact
        FinitePolygonalSetCyclicPieceSourceNotSegmentTarget
          J E segmentIndex_lt cutList cutList_bounds localPieceIndex
          pieceNumber pieceNumber_lt pieceSourceParam pieceTargetParam
          pieceSourceParam_lt pieceTargetParam_eq pieceSource pieceSource_eq q
    have separated_contra :
        ∀ (n₁ n₂ : Fin ((E[e.1]'e.2).1.vertices.length - 1))
          (a₁ : localPieceIndex e n₁) (a₂ : localPieceIndex e n₂),
          n₁.1 < n₂.1 →
          pieceSource (⟨e, ⟨n₁, a₁⟩⟩ : PieceIndex) =
            pieceSource (⟨e, ⟨n₂, a₂⟩⟩ : PieceIndex) →
          False := by
      intro n₁ n₂ a₁ a₂ hlt hsrc
      let γ : PolygonalArc := (E[e.1]'e.2).1
      have hmem_left :
          pieceSource (⟨e, ⟨n₁, a₁⟩⟩ : PieceIndex) ∈
            segment ℝ
              (γ.vertices[n₁.1]'(Nat.lt_of_succ_lt (by
                simpa [γ] using segmentIndex_lt e n₁)))
              (γ.vertices[n₁.1 + 1]'(by
                simpa [γ] using segmentIndex_lt e n₁)) := by
        simpa [γ] using source_mem_segment (⟨e, ⟨n₁, a₁⟩⟩ : PieceIndex)
      have hmem_right_raw :
          pieceSource (⟨e, ⟨n₂, a₂⟩⟩ : PieceIndex) ∈
            segment ℝ
              (γ.vertices[n₂.1]'(Nat.lt_of_succ_lt (by
                simpa [γ] using segmentIndex_lt e n₂)))
              (γ.vertices[n₂.1 + 1]'(by
                simpa [γ] using segmentIndex_lt e n₂)) := by
        simpa [γ] using source_mem_segment (⟨e, ⟨n₂, a₂⟩⟩ : PieceIndex)
      have hmem_inter :
          pieceSource (⟨e, ⟨n₁, a₁⟩⟩ : PieceIndex) ∈
            segment ℝ
                (γ.vertices[n₁.1]'(Nat.lt_of_succ_lt (by
                  simpa [γ] using segmentIndex_lt e n₁)))
                (γ.vertices[n₁.1 + 1]'(by
                  simpa [γ] using segmentIndex_lt e n₁)) ∩
              segment ℝ
                (γ.vertices[n₂.1]'(Nat.lt_of_succ_lt (by
                  simpa [γ] using segmentIndex_lt e n₂)))
                (γ.vertices[n₂.1 + 1]'(by
                  simpa [γ] using segmentIndex_lt e n₂)) :=
        ⟨hmem_left, by simpa [hsrc] using hmem_right_raw⟩
      have hinter := γ.segment_intersections
        (by simpa [γ] using segmentIndex_lt e n₁)
        (by simpa [γ] using segmentIndex_lt e n₂) hlt
      by_cases hadj : n₂.1 = n₁.1 + 1
      · have hsource_eq_terminal :
            pieceSource (⟨e, ⟨n₁, a₁⟩⟩ : PieceIndex) =
              (E[e.1]'e.2).1.vertices[n₁.1 + 1]'
                (segmentIndex_lt e n₁) := by
          rw [hinter] at hmem_inter
          simpa [γ, hadj] using hmem_inter
        exact source_not_segment_target
          (⟨e, ⟨n₁, a₁⟩⟩ : PieceIndex) hsource_eq_terminal
      · have : pieceSource (⟨e, ⟨n₁, a₁⟩⟩ : PieceIndex) ∈
            (∅ : Set (EuclideanSpace ℝ (Fin 2))) := by
          rw [hinter] at hmem_inter
          simp [hadj] at hmem_inter
        exact this
    have hlt_or : n.1 < m.1 ∨ m.1 < n.1 := by omega
    rcases hlt_or with hlt | hlt
    · exact (separated_contra n m a b hlt hsource).elim
    · exact (separated_contra m n b a hlt hsource.symm).elim
