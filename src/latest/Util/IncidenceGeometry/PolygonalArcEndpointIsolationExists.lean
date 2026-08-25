import Util.IncidenceGeometry.PolygonalArcEndpointIsolation
import Util.IncidenceGeometry.PolygonalArcCarrierCompact
import Util.IncidenceGeometry.PolygonalArcCollarControlRadiiExists
import Util.IncidenceGeometry.PositiveSeparation

open Classical
noncomputable section

lemma PolygonalArcEndpointIsolationExists (γ : PolygonalArc) :
    ∃ r₀ r₁ : ℝ, PolygonalArcEndpointIsolation γ r₀ r₁ := by
  have hsourceIdx : 0 < γ.vertices.length := by
    have hlen := γ.length_ge_two
    omega
  have hfirst : 0 + 1 < γ.vertices.length := by
    have hlen := γ.length_ge_two
    omega
  let sourceIdx : Fin γ.vertices.length := ⟨0, hsourceIdx⟩
  have htargetIdx : γ.vertices.length - 1 < γ.vertices.length := by
    have hlen := γ.length_ge_two
    omega
  let targetIdx : Fin γ.vertices.length := ⟨γ.vertices.length - 1, htargetIdx⟩
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
  obtain ⟨controlRadii⟩ :=
    PolygonalArcCollarControlRadiiExists γ (η := (1 : ℝ)) (by norm_num)
  refine ⟨controlRadii.radius sourceIdx, controlRadii.radius targetIdx, ?_⟩
  refine
    { source_pos := controlRadii.radius_pos sourceIdx
      target_pos := controlRadii.radius_pos targetIdx
      source_lt_initial_length := ?_
      target_lt_terminal_length := ?_
      endpoint_closedBalls_disjoint := ?_
      source_closedBall_carrier_subset_initial_segment := ?_
      target_closedBall_carrier_subset_terminal_segment := ?_ }
  · have hsum := controlRadii.adjacent_radii_sum_lt (j := 0) hfirst
    have hnext_pos := controlRadii.radius_pos ⟨1, hfirst⟩
    have hlt :
        controlRadii.radius sourceIdx < dist γ.vertices[0] γ.vertices[1] := by
      nlinarith
    simpa [PolygonalArcInitialEndpointSegmentLength, sourceIdx, hsource_vertex]
      using hlt
  · have hsum := controlRadii.adjacent_radii_sum_lt (j := jlast) hlast
    have hprev_pos :=
      controlRadii.radius_pos ⟨jlast, Nat.lt_of_succ_lt hlast⟩
    have hlt :
        controlRadii.radius targetIdx <
          dist γ.vertices[jlast] γ.vertices[jlast + 1] := by
      have htarget_eq_idx :
          (⟨jlast + 1, hlast⟩ : Fin γ.vertices.length) = targetIdx := by
        apply Fin.ext
        simpa [targetIdx] using hlast_succ
      simpa [htarget_eq_idx] using (by nlinarith : controlRadii.radius
        (⟨jlast + 1, hlast⟩ : Fin γ.vertices.length) <
          dist γ.vertices[jlast] γ.vertices[jlast + 1])
    have hdist :
        dist γ.vertices[jlast] γ.vertices[jlast + 1] =
          dist γ.target γ.vertices[jlast] := by
      simpa [hlast_vertex] using
        (dist_comm γ.vertices[jlast] γ.vertices[jlast + 1])
    have hlt' :
        controlRadii.radius targetIdx < dist γ.target γ.vertices[jlast] := by
      simpa [hdist] using hlt
    simpa [PolygonalArcTerminalEndpointSegmentLength, jlast] using hlt'
  · have hne : sourceIdx ≠ targetIdx := by
      intro h
      have : (0 : ℕ) = γ.vertices.length - 1 := by
        simpa [sourceIdx, targetIdx] using congrArg Fin.val h
      have hlen := γ.length_ge_two
      omega
    have hdisj := controlRadii.control_disks_disjoint (i := sourceIdx)
      (j := targetIdx) hne
    simpa [sourceIdx, targetIdx, hsource_vertex, htarget_vertex] using hdisj
  · dsimp
    intro z hz
    rcases hz with ⟨hzball, hzcarrier⟩
    rw [γ.carrier_eq] at hzcarrier
    rcases hzcarrier with ⟨j, hj, hzseg⟩
    by_cases hj0 : j = 0
    · subst j
      simpa [hsource_vertex] using hzseg
    · exfalso
      have hdisj := controlRadii.nonincident_segment_disjoint
        (i := sourceIdx) (j := j) hj
        (by
          intro h
          exact hj0 h.symm)
        (by
          intro h
          have h0 : (0 : ℕ) = j + 1 := by
            simpa [sourceIdx] using h
          omega)
      have hzball' : z ∈ Metric.closedBall γ.vertices[sourceIdx.1]
          (controlRadii.radius sourceIdx) := by
        simpa [sourceIdx, hsource_vertex] using hzball
      exact (Set.disjoint_left.mp hdisj hzball') hzseg
  · dsimp
    intro z hz
    rcases hz with ⟨hzball, hzcarrier⟩
    rw [γ.carrier_eq] at hzcarrier
    rcases hzcarrier with ⟨j, hj, hzseg⟩
    by_cases hjlast : j = jlast
    · subst j
      have hzseg' :
          z ∈ segment ℝ γ.vertices[jlast + 1] γ.vertices[jlast] := by
        simpa [segment_symm] using hzseg
      simpa [hlast_vertex] using hzseg'
    · exfalso
      have hij : targetIdx.1 ≠ j := by
        intro h
        have : j = jlast := by
          have hlen := γ.length_ge_two
          dsimp [targetIdx, jlast] at h
          omega
        exact hjlast this
      have hijs : targetIdx.1 ≠ j + 1 := by
        intro h
        have : j = jlast := by
          have hlen := γ.length_ge_two
          dsimp [targetIdx, jlast] at h
          omega
        exact hjlast this
      have hdisj := controlRadii.nonincident_segment_disjoint
        (i := targetIdx) (j := j) hj hij hijs
      have hzball' : z ∈ Metric.closedBall γ.vertices[targetIdx.1]
          (controlRadii.radius targetIdx) := by
        simpa [targetIdx, htarget_vertex] using hzball
      exact (Set.disjoint_left.mp hdisj hzball') hzseg
