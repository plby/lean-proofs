import Mathlib.Tactic
import Util.IncidenceGeometry.PolygonalArcCollarControlRadiiExists
import Util.IncidenceGeometry.PolygonalArcEndpointIsolation
import Util.IncidenceGeometry.PolygonalArcVertexMemCarrier

open Classical
noncomputable section

lemma PolygonalArcCollarControlRadiiExistsBelow (γ : PolygonalArc)
    (η r₀ r₁ : ℝ) :
    0 < η →
      0 < r₀ →
        0 < r₁ →
          PolygonalArcEndpointIsolation γ r₀ r₁ →
            let hsource : 0 < γ.vertices.length := by
              have hlen := γ.length_ge_two
              omega
            let htarget : γ.vertices.length - 1 < γ.vertices.length := by
              have hlen := γ.length_ge_two
              omega
            ∃ controlRadii : PolygonalArcCollarControlRadii γ η,
              controlRadii.radius ⟨0, hsource⟩ < r₀ ∧
                controlRadii.radius ⟨γ.vertices.length - 1, htarget⟩ < r₁ ∧
                  (∀ i : Fin γ.vertices.length, i.1 ≠ 0 →
                    Disjoint
                      (Metric.ball γ.vertices[i.1] (controlRadii.radius i))
                      (Metric.ball γ.source r₀)) ∧
                    (∀ i : Fin γ.vertices.length,
                      i.1 + 1 ≠ γ.vertices.length →
                        Disjoint
                          (Metric.ball γ.vertices[i.1] (controlRadii.radius i))
                          (Metric.ball γ.target r₁)) := by
  intro hη hr₀ hr₁ hIso
  have hsourceIdx : 0 < γ.vertices.length := by
    have hlen := γ.length_ge_two
    omega
  have hfirst : 1 < γ.vertices.length := by
    have hlen := γ.length_ge_two
    omega
  have htargetIdx : γ.vertices.length - 1 < γ.vertices.length := by
    have hlen := γ.length_ge_two
    omega
  let jlast : ℕ := γ.vertices.length - 2
  have hlast : jlast + 1 < γ.vertices.length := by
    have hlen := γ.length_ge_two
    dsimp [jlast]
    omega
  have hlast_succ : jlast + 1 = γ.vertices.length - 1 := by
    have hlen := γ.length_ge_two
    dsimp [jlast]
    omega
  have hsource_vertex : γ.vertices[0] = γ.source := by
    have hget : γ.vertices[0]? = some γ.vertices[0] :=
      List.getElem?_eq_getElem hsourceIdx
    rw [← List.head?_eq_getElem?, γ.source_eq_head] at hget
    exact Option.some.inj hget.symm
  have htarget_vertex : γ.vertices[γ.vertices.length - 1] = γ.target := by
    have hget :
        γ.vertices[γ.vertices.length - 1]? =
          some γ.vertices[γ.vertices.length - 1] :=
      List.getElem?_eq_getElem htargetIdx
    rw [← List.getLast?_eq_getElem?, γ.target_eq_last] at hget
    exact Option.some.inj hget.symm
  have hlast_vertex : γ.vertices[jlast + 1] = γ.target := by
    simpa [hlast_succ] using htarget_vertex
  have source_gap_pos :
      ∀ i : Fin γ.vertices.length, i.1 ≠ 0 →
        0 < dist γ.vertices[i.1] γ.source - r₀ := by
    intro i hi0
    have hdist_gt : r₀ < dist γ.vertices[i.1] γ.source := by
      by_cases hi1 : i.1 = 1
      · have hdist :
            r₀ < dist γ.source γ.vertices[1] := by
          simpa [PolygonalArcInitialEndpointSegmentLength] using
            hIso.source_lt_initial_length
        simpa [hi1, dist_comm] using hdist
      · have hnot_closed :
            γ.vertices[i.1] ∉ Metric.closedBall γ.source r₀ := by
          intro hball
          have hcarrier : γ.vertices[i.1] ∈ γ.carrier :=
            PolygonalArcVertexMemCarrier γ
              (List.getElem_mem (l := γ.vertices) i.2)
          have hseg_source :
              γ.vertices[i.1] ∈ segment ℝ γ.source γ.vertices[1] := by
            exact hIso.source_closedBall_carrier_subset_initial_segment
              ⟨hball, hcarrier⟩
          have hseg :
              γ.vertices[i.1] ∈ segment ℝ γ.vertices[0] γ.vertices[1] := by
            simpa [hsource_vertex] using hseg_source
          have hne_left : γ.vertices[0] ≠ γ.vertices[i.1] := by
            intro hEq
            have hidx : (0 : ℕ) = i.1 := by
              apply (List.Nodup.getElem_inj_iff γ.simple_vertices).mp
              simpa using hEq
            exact hi0 hidx.symm
          have hne_right : γ.vertices[1] ≠ γ.vertices[i.1] := by
            intro hEq
            have hidx : (1 : ℕ) = i.1 := by
              apply (List.Nodup.getElem_inj_iff γ.simple_vertices).mp
              simpa using hEq
            exact hi1 hidx.symm
          have hopen :
              γ.vertices[i.1] ∈ openSegment ℝ γ.vertices[0] γ.vertices[1] :=
            mem_openSegment_of_ne_left_right (𝕜 := ℝ) hne_left hne_right hseg
          exact γ.vertices_avoid_nonincident_interiors (i := 0) (k := i.1)
            hfirst i.2 hi0 (by simpa using hi1) hopen
        have hdist_source : r₀ < dist γ.source γ.vertices[i.1] := by
          apply lt_of_not_ge
          intro hle
          exact hnot_closed (by
            simpa [Metric.mem_closedBall, dist_comm] using hle)
        simpa [dist_comm] using hdist_source
    nlinarith
  have target_gap_pos :
      ∀ i : Fin γ.vertices.length, i.1 + 1 ≠ γ.vertices.length →
        0 < dist γ.vertices[i.1] γ.target - r₁ := by
    intro i hitarget
    have hdist_gt : r₁ < dist γ.vertices[i.1] γ.target := by
      by_cases hilast : i.1 = jlast
      · have hdist :
            r₁ < dist γ.target γ.vertices[jlast] := by
          simpa [PolygonalArcTerminalEndpointSegmentLength, jlast] using
            hIso.target_lt_terminal_length
        simpa [hilast, dist_comm] using hdist
      · have hnot_closed :
            γ.vertices[i.1] ∉ Metric.closedBall γ.target r₁ := by
          intro hball
          have hcarrier : γ.vertices[i.1] ∈ γ.carrier :=
            PolygonalArcVertexMemCarrier γ
              (List.getElem_mem (l := γ.vertices) i.2)
          have hseg_target :
              γ.vertices[i.1] ∈ segment ℝ γ.target γ.vertices[jlast] := by
            exact hIso.target_closedBall_carrier_subset_terminal_segment
              ⟨hball, hcarrier⟩
          have hseg_target' :
              γ.vertices[i.1] ∈ segment ℝ γ.vertices[jlast] γ.target := by
            simpa [segment_symm] using hseg_target
          have hseg :
              γ.vertices[i.1] ∈
                segment ℝ γ.vertices[jlast] γ.vertices[jlast + 1] := by
            simpa [hlast_vertex] using hseg_target'
          have hne_left : γ.vertices[jlast] ≠ γ.vertices[i.1] := by
            intro hEq
            have hidx : jlast = i.1 := by
              apply (List.Nodup.getElem_inj_iff γ.simple_vertices).mp
              simpa using hEq
            exact hilast hidx.symm
          have hine_succ : i.1 ≠ jlast + 1 := by
            intro hEq
            have : i.1 + 1 = γ.vertices.length := by
              omega
            exact hitarget this
          have hne_right : γ.vertices[jlast + 1] ≠ γ.vertices[i.1] := by
            intro hEq
            have hidx : jlast + 1 = i.1 := by
              apply (List.Nodup.getElem_inj_iff γ.simple_vertices).mp
              simpa using hEq
            exact hine_succ hidx.symm
          have hopen :
              γ.vertices[i.1] ∈
                openSegment ℝ γ.vertices[jlast] γ.vertices[jlast + 1] :=
            mem_openSegment_of_ne_left_right (𝕜 := ℝ) hne_left hne_right hseg
          exact γ.vertices_avoid_nonincident_interiors (i := jlast) (k := i.1)
            hlast i.2 hilast hine_succ hopen
        have hdist_target : r₁ < dist γ.target γ.vertices[i.1] := by
          apply lt_of_not_ge
          intro hle
          exact hnot_closed (by
            simpa [Metric.mem_closedBall, dist_comm] using hle)
        simpa [dist_comm] using hdist_target
    nlinarith
  let sourceTerm : Fin γ.vertices.length → ℝ := fun i =>
    if i.1 = 0 then 1 else (dist γ.vertices[i.1] γ.source - r₀) / 2
  let targetTerm : Fin γ.vertices.length → ℝ := fun i =>
    if i.1 + 1 = γ.vertices.length then 1
    else (dist γ.vertices[i.1] γ.target - r₁) / 2
  let : Nonempty (Fin γ.vertices.length) := ⟨⟨0, hsourceIdx⟩⟩
  let sourceBound : ℝ :=
    Finset.univ.inf' (show (Finset.univ : Finset (Fin γ.vertices.length)).Nonempty
      from Finset.univ_nonempty) sourceTerm
  let targetBound : ℝ :=
    Finset.univ.inf' (show (Finset.univ : Finset (Fin γ.vertices.length)).Nonempty
      from Finset.univ_nonempty) targetTerm
  have sourceTerm_pos : ∀ i, 0 < sourceTerm i := by
    intro i
    dsimp [sourceTerm]
    by_cases hi0 : i.1 = 0
    · simp [hi0]
    · have hgap := source_gap_pos i hi0
      simp [hi0]
      nlinarith
  have targetTerm_pos : ∀ i, 0 < targetTerm i := by
    intro i
    dsimp [targetTerm]
    by_cases hitarget : i.1 + 1 = γ.vertices.length
    · simp [hitarget]
    · have hgap := target_gap_pos i hitarget
      simp [hitarget]
      nlinarith
  have sourceBound_pos : 0 < sourceBound := by
    dsimp [sourceBound]
    exact (Finset.lt_inf'_iff _).2 (by
      intro i _hi
      exact sourceTerm_pos i)
  have targetBound_pos : 0 < targetBound := by
    dsimp [targetBound]
    exact (Finset.lt_inf'_iff _).2 (by
      intro i _hi
      exact targetTerm_pos i)
  let ε : ℝ :=
    min (η / 2)
      (min (r₀ / 2)
        (min (r₁ / 2) (min (sourceBound / 2) (targetBound / 2))))
  have hεpos : 0 < ε := by
    dsimp [ε]
    exact lt_min (half_pos hη)
      (lt_min (half_pos hr₀)
        (lt_min (half_pos hr₁)
          (lt_min (half_pos sourceBound_pos) (half_pos targetBound_pos))))
  have hε_lt_η : ε < η := by
    have hle : ε ≤ η / 2 := by
      dsimp [ε]
      exact min_le_left _ _
    nlinarith
  have hε_lt_r₀ : ε < r₀ := by
    have hle : ε ≤ r₀ / 2 := by
      dsimp [ε]
      exact le_trans (min_le_right _ _) (min_le_left _ _)
    nlinarith
  have hε_lt_r₁ : ε < r₁ := by
    have hle : ε ≤ r₁ / 2 := by
      dsimp [ε]
      exact le_trans (min_le_right _ _)
        (le_trans (min_le_right _ _) (min_le_left _ _))
    nlinarith
  have hε_lt_sourceBound : ε < sourceBound := by
    have hle : ε ≤ sourceBound / 2 := by
      dsimp [ε]
      exact le_trans (min_le_right _ _)
        (le_trans (min_le_right _ _)
          (le_trans (min_le_right _ _) (min_le_left _ _)))
    exact lt_of_le_of_lt hle (half_lt_self sourceBound_pos)
  have hε_lt_targetBound : ε < targetBound := by
    have hle : ε ≤ targetBound / 2 := by
      dsimp [ε]
      exact le_trans (min_le_right _ _)
        (le_trans (min_le_right _ _)
          (le_trans (min_le_right _ _) (min_le_right _ _)))
    exact lt_of_le_of_lt hle (half_lt_self targetBound_pos)
  obtain ⟨smallRadii⟩ :=
    PolygonalArcCollarControlRadiiExists γ (η := ε) hεpos
  let controlRadii : PolygonalArcCollarControlRadii γ η :=
    { radius := smallRadii.radius
      radius_pos := smallRadii.radius_pos
      radius_lt_eta := fun i => (smallRadii.radius_lt_eta i).trans hε_lt_η
      control_disks_disjoint := smallRadii.control_disks_disjoint
      adjacent_radii_sum_lt := smallRadii.adjacent_radii_sum_lt
      nonincident_segment_disjoint := smallRadii.nonincident_segment_disjoint }
  dsimp
  refine ⟨controlRadii, ?_, ?_, ?_, ?_⟩
  · dsimp [controlRadii]
    exact (smallRadii.radius_lt_eta ⟨0, hsourceIdx⟩).trans hε_lt_r₀
  · dsimp [controlRadii]
    exact (smallRadii.radius_lt_eta ⟨γ.vertices.length - 1, htargetIdx⟩).trans hε_lt_r₁
  · intro i hi0
    dsimp [controlRadii]
    have hle :
        sourceBound ≤ sourceTerm i := by
      dsimp [sourceBound]
      exact Finset.inf'_le sourceTerm (Finset.mem_univ i)
    have hrad_lt :
        smallRadii.radius i <
          (dist γ.vertices[i.1] γ.source - r₀) / 2 := by
      have hterm : sourceTerm i =
          (dist γ.vertices[i.1] γ.source - r₀) / 2 := by
        simp [sourceTerm, hi0]
      exact (smallRadii.radius_lt_eta i).trans
        (by simpa [hterm] using hε_lt_sourceBound.trans_le hle)
    have hgap := source_gap_pos i hi0
    have hsum :
        smallRadii.radius i + r₀ ≤ dist γ.vertices[i.1] γ.source := by
      nlinarith
    exact Metric.ball_disjoint_ball hsum
  · intro i hitarget
    dsimp [controlRadii]
    have hle :
        targetBound ≤ targetTerm i := by
      dsimp [targetBound]
      exact Finset.inf'_le targetTerm (Finset.mem_univ i)
    have hrad_lt :
        smallRadii.radius i <
          (dist γ.vertices[i.1] γ.target - r₁) / 2 := by
      have hterm : targetTerm i =
          (dist γ.vertices[i.1] γ.target - r₁) / 2 := by
        simp [targetTerm, hitarget]
      exact (smallRadii.radius_lt_eta i).trans
        (by simpa [hterm] using hε_lt_targetBound.trans_le hle)
    have hgap := target_gap_pos i hitarget
    have hsum :
        smallRadii.radius i + r₁ ≤ dist γ.vertices[i.1] γ.target := by
      nlinarith
    exact Metric.ball_disjoint_ball hsum
