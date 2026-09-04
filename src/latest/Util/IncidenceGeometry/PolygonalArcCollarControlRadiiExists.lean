import Util.IncidenceGeometry.PolygonalArcCollarControlRadii
import Util.IncidenceGeometry.PolygonalArcVertexNonincidentSegmentSeparation

open Classical
noncomputable section

lemma PolygonalArcCollarControlRadiiExists (γ : PolygonalArc) {η : ℝ}
    (hη : 0 < η) :
    Nonempty (PolygonalArcCollarControlRadii γ η) := by
  let n := γ.vertices.length
  have hlen_pos : 0 < n := by
    have hlen : 2 ≤ γ.vertices.length := γ.length_ge_two
    dsimp [n]
    omega
  let : Nonempty (Fin n) := ⟨⟨0, hlen_pos⟩⟩
  let center : Fin n → EuclideanSpace ℝ (Fin 2) := fun i => γ.vertices[i.1]
  have hcenter : Function.Injective center := by
    intro i j hij
    apply Fin.ext
    have hidx : i.1 = j.1 := by
      apply (List.Nodup.getElem_inj_iff γ.simple_vertices).mp
      simpa [center, n] using hij
    exact hidx
  let vertexTerm : Fin n × Fin n → ℝ := fun p =>
    if p.1 = p.2 then (1 : ℝ) else dist (center p.1) (center p.2) / 3
  let vertexBound : ℝ :=
    Finset.univ.inf' (show (Finset.univ : Finset (Fin n × Fin n)).Nonempty from
      Finset.univ_nonempty) vertexTerm
  have vertexTerm_pos : ∀ p, 0 < vertexTerm p := by
    intro p
    dsimp [vertexTerm]
    by_cases hp : p.1 = p.2
    · simp [hp]
    · have hdist : 0 < dist (center p.1) (center p.2) := by
        exact dist_pos.mpr (by
          intro h
          exact hp (hcenter h))
      positivity
  have vertexBound_pos : 0 < vertexBound := by
    dsimp [vertexBound]
    exact (Finset.lt_inf'_iff _).2 (by
      intro p _hp
      exact vertexTerm_pos p)
  let segmentTerm : Fin n × Fin n → ℝ := fun p =>
    if h : p.2.1 + 1 < γ.vertices.length ∧ p.1.1 ≠ p.2.1 ∧
        p.1.1 ≠ p.2.1 + 1 then
      (Classical.choose
        (PolygonalArcVertexNonincidentSegmentSeparation γ
          (by simpa [n] using p.1.2) h.1 h.2.1 h.2.2)) / 2
    else (1 : ℝ)
  let segmentBound : ℝ :=
    Finset.univ.inf' (show (Finset.univ : Finset (Fin n × Fin n)).Nonempty from
      Finset.univ_nonempty) segmentTerm
  have segmentTerm_pos : ∀ p, 0 < segmentTerm p := by
    intro p
    dsimp [segmentTerm]
    by_cases h : p.2.1 + 1 < γ.vertices.length ∧ p.1.1 ≠ p.2.1 ∧
        p.1.1 ≠ p.2.1 + 1
    · have hsep :=
        Classical.choose_spec
          (PolygonalArcVertexNonincidentSegmentSeparation γ
            (by simpa [n] using p.1.2) h.1 h.2.1 h.2.2)
      simpa [h] using half_pos hsep.1
    · simp [h]
  have segmentBound_pos : 0 < segmentBound := by
    dsimp [segmentBound]
    exact (Finset.lt_inf'_iff _).2 (by
      intro p _hp
      exact segmentTerm_pos p)
  let ρ : ℝ := min (η / 2) (min (vertexBound / 2) (segmentBound / 2))
  have hρpos : 0 < ρ := by
    dsimp [ρ]
    exact lt_min (half_pos hη)
      (lt_min (half_pos vertexBound_pos) (half_pos segmentBound_pos))
  have hρ_lt_eta : ρ < η := by
    have hle : ρ ≤ η / 2 := by
      dsimp [ρ]
      exact min_le_left _ _
    nlinarith
  have hρ_lt_vertexBound : ρ < vertexBound := by
    have hle : ρ ≤ vertexBound / 2 := by
      dsimp [ρ]
      exact le_trans (min_le_right _ _) (min_le_left _ _)
    have hhalf : vertexBound / 2 < vertexBound := half_lt_self vertexBound_pos
    exact lt_of_le_of_lt hle hhalf
  have hρ_lt_segmentBound : ρ < segmentBound := by
    have hle : ρ ≤ segmentBound / 2 := by
      dsimp [ρ]
      exact le_trans (min_le_right _ _) (min_le_right _ _)
    have hhalf : segmentBound / 2 < segmentBound := half_lt_self segmentBound_pos
    exact lt_of_le_of_lt hle hhalf
  have hρ_lt_vertex_dist :
      ∀ ⦃i j : Fin n⦄, i ≠ j → ρ < dist (center i) (center j) / 3 := by
    intro i j hij
    have hle :
        vertexBound ≤ dist (center i) (center j) / 3 := by
      have hentry : vertexBound ≤ vertexTerm (i, j) := by
        dsimp [vertexBound]
        exact Finset.inf'_le vertexTerm (Finset.mem_univ (i, j))
      simpa [vertexTerm, hij] using hentry
    exact hρ_lt_vertexBound.trans_le hle
  have hρ_lt_segmentBound_entry :
      ∀ ⦃i : Fin n⦄ ⦃j : ℕ⦄ (hj : j + 1 < γ.vertices.length),
        (hij : i.1 ≠ j) → (hijs : i.1 ≠ j + 1) →
          ρ <
            Classical.choose
              (PolygonalArcVertexNonincidentSegmentSeparation γ
                (by simpa [n] using i.2) hj hij hijs) := by
    intro i j hj hij hijs
    let jf : Fin n := ⟨j, by
      dsimp [n]
      exact Nat.lt_of_succ_lt hj⟩
    have hcond : jf.1 + 1 < γ.vertices.length ∧ i.1 ≠ jf.1 ∧
        i.1 ≠ jf.1 + 1 := by
      exact ⟨hj, by simpa [jf] using hij, by simpa [jf] using hijs⟩
    have hle :
        segmentBound ≤
          (Classical.choose
            (PolygonalArcVertexNonincidentSegmentSeparation γ
              (by simpa [n] using i.2) hj hij hijs)) / 2 := by
      have hentry : segmentBound ≤ segmentTerm (i, jf) := by
        dsimp [segmentBound]
        exact Finset.inf'_le segmentTerm (Finset.mem_univ (i, jf))
      simpa [segmentTerm, hcond, jf] using hentry
    have hsep_pos :
        0 <
          Classical.choose
            (PolygonalArcVertexNonincidentSegmentSeparation γ
              (by simpa [n] using i.2) hj hij hijs) := by
      exact (Classical.choose_spec
        (PolygonalArcVertexNonincidentSegmentSeparation γ
          (by simpa [n] using i.2) hj hij hijs)).1
    nlinarith [hρ_lt_segmentBound, hle]
  refine ⟨
    { radius := fun _ => ρ
      radius_pos := fun _ => hρpos
      radius_lt_eta := fun _ => hρ_lt_eta
      control_disks_disjoint := ?_
      adjacent_radii_sum_lt := ?_
      nonincident_segment_disjoint := ?_ }⟩
  · intro i j hij
    apply Metric.closedBall_disjoint_closedBall
    have hdist_pos : 0 < dist (center ⟨i.1, by simpa [n] using i.2⟩)
        (center ⟨j.1, by simpa [n] using j.2⟩) := by
      exact dist_pos.mpr (by
        intro h
        exact hij (Fin.ext (by
          have hc :
              center ⟨i.1, by simpa [n] using i.2⟩ =
                center ⟨j.1, by simpa [n] using j.2⟩ := h
          exact congrArg Fin.val (hcenter hc))))
    have hlt :
        ρ <
          dist (center ⟨i.1, by simpa [n] using i.2⟩)
            (center ⟨j.1, by simpa [n] using j.2⟩) / 3 := by
      exact hρ_lt_vertex_dist (by
        intro h
        exact hij (Fin.ext (by simpa using congrArg Fin.val h)))
    simpa [center, n] using (by
      nlinarith : ρ + ρ <
        dist (center ⟨i.1, by simpa [n] using i.2⟩)
          (center ⟨j.1, by simpa [n] using j.2⟩))
  · intro j hj
    let jf : Fin n := ⟨j, by
      dsimp [n]
      exact Nat.lt_of_succ_lt hj⟩
    let j1f : Fin n := ⟨j + 1, by
      dsimp [n]
      exact hj⟩
    have hjne : jf ≠ j1f := by
      intro h
      have : j = j + 1 := by
        simpa [jf, j1f] using congrArg Fin.val h
      omega
    have hlt : ρ < dist (center jf) (center j1f) / 3 :=
      hρ_lt_vertex_dist hjne
    simpa [center, n, jf, j1f] using (by
      nlinarith : ρ + ρ < dist (center jf) (center j1f))
  · intro i j hj hij hijs
    rw [Set.disjoint_left]
    intro x hxball hxseg
    have hρδ :=
      hρ_lt_segmentBound_entry (i := ⟨i.1, by simpa [n] using i.2⟩)
        (j := j) hj hij hijs
    have hsep :=
      Classical.choose_spec
        (PolygonalArcVertexNonincidentSegmentSeparation γ
          (by simpa [n] using i.2) hj hij hijs)
    have hxle : dist γ.vertices[i.1] x ≤ ρ := by
      simpa [Metric.mem_closedBall, dist_comm] using hxball
    have hδle :
        Classical.choose
            (PolygonalArcVertexNonincidentSegmentSeparation γ
              (by simpa [n] using i.2) hj hij hijs) ≤
          dist γ.vertices[i.1] x := hsep.2 x hxseg
    nlinarith
