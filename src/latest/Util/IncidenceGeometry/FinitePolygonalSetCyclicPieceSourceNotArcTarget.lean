import Util.IncidenceGeometry.FinitePolygonalSetCyclicPieceSourceNotSegmentTarget

open Classical
noncomputable section

lemma FinitePolygonalSetCyclicPieceSourceNotArcTarget
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
      pieceSource i ≠ (E[i.1.1]'i.1.2).1.target := by
  intro PieceIndex i hsource_target
  let γ : PolygonalArc := (E[i.1.1]'i.1.2).1
  let n : Fin (γ.vertices.length - 1) := i.2.1
  have hnot_segment_target :
      pieceSource i ≠
        γ.vertices[n.1 + 1]'(by
          simpa [γ, n] using segmentIndex_lt i.1 i.2.1) := by
    simpa [PieceIndex, γ, n] using
      FinitePolygonalSetCyclicPieceSourceNotSegmentTarget
        J E segmentIndex_lt cutList cutList_bounds localPieceIndex
        pieceNumber pieceNumber_lt pieceSourceParam pieceTargetParam
        pieceSourceParam_lt pieceTargetParam_eq pieceSource pieceSource_eq i
  by_cases hlast : n.1 + 2 = γ.vertices.length
  · have hvertex_target :
        γ.vertices[n.1 + 1]'(by
          simpa [γ, n] using segmentIndex_lt i.1 i.2.1) = γ.target := by
      have hlast_some :
          γ.vertices.getLast? =
            some (γ.vertices[n.1 + 1]'(by
              simpa [γ, n] using segmentIndex_lt i.1 i.2.1)) := by
        rw [List.getLast?_eq_getElem?]
        have hidx : γ.vertices.length - 1 = n.1 + 1 := by omega
        simp [hidx]
      exact Option.some.inj (by rw [← hlast_some, γ.target_eq_last])
    exact hnot_segment_target (hsource_target.trans hvertex_target.symm)
  · let m : Fin (γ.vertices.length - 1) :=
      ⟨γ.vertices.length - 2, by
        have hlen : 2 ≤ γ.vertices.length := γ.length_ge_two
        omega⟩
    have hm_succ : m.1 + 1 < γ.vertices.length := by
      have hlen : 2 ≤ γ.vertices.length := γ.length_ge_two
      dsimp [m]
      omega
    have hm_last : m.1 + 1 = γ.vertices.length - 1 := by
      have hlen : 2 ≤ γ.vertices.length := γ.length_ge_two
      dsimp [m]
      omega
    have hn_lt_m : n.1 < m.1 := by
      dsimp [m] at *
      omega
    have hsource_mem :
        pieceSource i ∈
          segment ℝ
            (γ.vertices[n.1]'(Nat.lt_of_succ_lt (by
              simpa [γ, n] using segmentIndex_lt i.1 i.2.1)))
            (γ.vertices[n.1 + 1]'(by
              simpa [γ, n] using segmentIndex_lt i.1 i.2.1)) := by
      rw [pieceSource_eq i, segment_eq_image_lineMap]
      exact ⟨(pieceSourceParam i).1, (pieceSourceParam i).2, rfl⟩
    have htarget_mem_n :
        γ.target ∈
          segment ℝ
            (γ.vertices[n.1]'(Nat.lt_of_succ_lt (by
              simpa [γ, n] using segmentIndex_lt i.1 i.2.1)))
            (γ.vertices[n.1 + 1]'(by
              simpa [γ, n] using segmentIndex_lt i.1 i.2.1)) := by
      simpa [hsource_target] using hsource_mem
    have htarget_vertex_last :
        γ.target = γ.vertices[m.1 + 1]'hm_succ := by
      have hlast_some :
          γ.vertices.getLast? = some (γ.vertices[m.1 + 1]'hm_succ) := by
        rw [List.getLast?_eq_getElem?]
        simp [hm_last]
      exact (Option.some.inj (by rw [← hlast_some, γ.target_eq_last])).symm
    have htarget_mem_last :
        γ.target ∈
          segment ℝ
            (γ.vertices[m.1]'(Nat.lt_of_succ_lt hm_succ))
            (γ.vertices[m.1 + 1]'hm_succ) := by
      rw [htarget_vertex_last]
      exact right_mem_segment ℝ _ _
    have htarget_inter :
        γ.target ∈
          segment ℝ
              (γ.vertices[n.1]'(Nat.lt_of_succ_lt (by
                simpa [γ, n] using segmentIndex_lt i.1 i.2.1)))
              (γ.vertices[n.1 + 1]'(by
                simpa [γ, n] using segmentIndex_lt i.1 i.2.1)) ∩
            segment ℝ
              (γ.vertices[m.1]'(Nat.lt_of_succ_lt hm_succ))
              (γ.vertices[m.1 + 1]'hm_succ) :=
      ⟨htarget_mem_n, htarget_mem_last⟩
    have hinter := γ.segment_intersections
      (by simpa [γ, n] using segmentIndex_lt i.1 i.2.1) hm_succ hn_lt_m
    by_cases hadj : m.1 = n.1 + 1
    · have htarget_eq_vertex :
          γ.target =
            γ.vertices[m.1]'(Nat.lt_of_succ_lt hm_succ) := by
        rw [hinter] at htarget_inter
        simpa [hadj] using htarget_inter
      have hidx : m.1 = m.1 + 1 := by
        exact γ.simple_vertices.getElem_inj_iff.mp
          (htarget_eq_vertex.symm.trans htarget_vertex_last)
      omega
    · have : γ.target ∈ (∅ : Set (EuclideanSpace ℝ (Fin 2))) := by
        rw [hinter] at htarget_inter
        simp [hadj] at htarget_inter
      exact this
