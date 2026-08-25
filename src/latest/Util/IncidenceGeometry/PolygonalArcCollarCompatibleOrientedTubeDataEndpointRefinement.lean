import Mathlib.Tactic
import Util.IncidenceGeometry.PolygonalArcCollarCompatibleOrientedTubeData
import Util.IncidenceGeometry.PolygonalArcEndpointIsolation
import Util.IncidenceGeometry.PositiveSeparation

open Classical
noncomputable section

private lemma endpointRefinement_successive_positive_negative_cones_disjoint
    (γ : PolygonalArc) {η : ℝ}
    (controlRadii : PolygonalArcCollarControlRadii γ η)
    (middleSegments : PolygonalArcCollarMiddleSegmentData γ controlRadii)
    (forbiddenMargins :
      PolygonalArcCollarMiddleForbiddenMargins γ controlRadii middleSegments)
    (base :
      PolygonalArcCollarCompatibleOrientedTubeData γ controlRadii middleSegments
        forbiddenMargins)
    (initialConeBound terminalConeBound :
      (j : ℕ) → j + 1 < γ.vertices.length → ℝ)
    (initialConeBound_le_base :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length),
        initialConeBound j hj ≤ base.initialConeBound j hj)
    (terminalConeBound_le_base :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length),
        terminalConeBound j hj ≤ base.terminalConeBound j hj)
    (j : ℕ) (hj : j + 1 < γ.vertices.length)
    (hnext : (j + 1) + 1 < γ.vertices.length) :
    Disjoint
      {z | ∃ t : ℝ, t ∈ Set.Ioo (0 : ℝ) (1 : ℝ) ∧
        ∃ s : ℝ, 0 < s ∧ s < terminalConeBound j hj * (1 - t) ∧
          z = AffineMap.lineMap γ.vertices[j] γ.vertices[j + 1] t +
            s • base.orientedTubes.toPolygonalArcCollarSeparatedTubeData.normal j hj}
      {z | ∃ t : ℝ, t ∈ Set.Ioo (0 : ℝ) (1 : ℝ) ∧
        ∃ s : ℝ, s < 0 ∧ |s| < initialConeBound (j + 1) hnext * t ∧
          z = AffineMap.lineMap γ.vertices[j + 1] γ.vertices[j + 2] t +
            s • base.orientedTubes.toPolygonalArcCollarSeparatedTubeData.normal
              (j + 1) hnext} := by
  rw [Set.disjoint_left]
  intro z hzL hzR
  rcases hzL with ⟨t, ht, s, hs_pos, hs_lt, hzL⟩
  rcases hzR with ⟨u, hu, r, hr_neg, hr_lt, hzR⟩
  exact Set.disjoint_left.mp
    (base.successive_positive_negative_cones_disjoint j hj hnext)
    (by
      refine ⟨t, ht, s, hs_pos, ?_, hzL⟩
      exact lt_of_lt_of_le hs_lt
        (mul_le_mul_of_nonneg_right (terminalConeBound_le_base j hj)
          (by nlinarith [ht.2])))
    (by
      refine ⟨u, hu, r, hr_neg, ?_, hzR⟩
      exact lt_of_lt_of_le hr_lt
        (mul_le_mul_of_nonneg_right (initialConeBound_le_base (j + 1) hnext)
          (le_of_lt hu.1)))

private lemma endpointRefinement_successive_negative_positive_cones_disjoint
    (γ : PolygonalArc) {η : ℝ}
    (controlRadii : PolygonalArcCollarControlRadii γ η)
    (middleSegments : PolygonalArcCollarMiddleSegmentData γ controlRadii)
    (forbiddenMargins :
      PolygonalArcCollarMiddleForbiddenMargins γ controlRadii middleSegments)
    (base :
      PolygonalArcCollarCompatibleOrientedTubeData γ controlRadii middleSegments
        forbiddenMargins)
    (initialConeBound terminalConeBound :
      (j : ℕ) → j + 1 < γ.vertices.length → ℝ)
    (initialConeBound_le_base :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length),
        initialConeBound j hj ≤ base.initialConeBound j hj)
    (terminalConeBound_le_base :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length),
        terminalConeBound j hj ≤ base.terminalConeBound j hj)
    (j : ℕ) (hj : j + 1 < γ.vertices.length)
    (hnext : (j + 1) + 1 < γ.vertices.length) :
    Disjoint
      {z | ∃ t : ℝ, t ∈ Set.Ioo (0 : ℝ) (1 : ℝ) ∧
        ∃ s : ℝ, s < 0 ∧ |s| < terminalConeBound j hj * (1 - t) ∧
          z = AffineMap.lineMap γ.vertices[j] γ.vertices[j + 1] t +
            s • base.orientedTubes.toPolygonalArcCollarSeparatedTubeData.normal j hj}
      {z | ∃ t : ℝ, t ∈ Set.Ioo (0 : ℝ) (1 : ℝ) ∧
        ∃ s : ℝ, 0 < s ∧ s < initialConeBound (j + 1) hnext * t ∧
          z = AffineMap.lineMap γ.vertices[j + 1] γ.vertices[j + 2] t +
            s • base.orientedTubes.toPolygonalArcCollarSeparatedTubeData.normal
              (j + 1) hnext} := by
  rw [Set.disjoint_left]
  intro z hzL hzR
  rcases hzL with ⟨t, ht, s, hs_neg, hs_lt, hzL⟩
  rcases hzR with ⟨u, hu, r, hr_pos, hr_lt, hzR⟩
  exact Set.disjoint_left.mp
    (base.successive_negative_positive_cones_disjoint j hj hnext)
    (by
      refine ⟨t, ht, s, hs_neg, ?_, hzL⟩
      exact lt_of_lt_of_le hs_lt
        (mul_le_mul_of_nonneg_right (terminalConeBound_le_base j hj)
          (by nlinarith [ht.2])))
    (by
      refine ⟨u, hu, r, hr_pos, ?_, hzR⟩
      exact lt_of_lt_of_le hr_lt
        (mul_le_mul_of_nonneg_right (initialConeBound_le_base (j + 1) hnext)
          (le_of_lt hu.1)))

private lemma endpointRefinement_initial_signed_cone_disjoint_previous_segment
    (γ : PolygonalArc) {η : ℝ}
    (controlRadii : PolygonalArcCollarControlRadii γ η)
    (middleSegments : PolygonalArcCollarMiddleSegmentData γ controlRadii)
    (forbiddenMargins :
      PolygonalArcCollarMiddleForbiddenMargins γ controlRadii middleSegments)
    (base :
      PolygonalArcCollarCompatibleOrientedTubeData γ controlRadii middleSegments
        forbiddenMargins)
    (initialConeBound : (j : ℕ) → j + 1 < γ.vertices.length → ℝ)
    (initialConeBound_le_base :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length),
        initialConeBound j hj ≤ base.initialConeBound j hj)
    (j : ℕ) (hj : j + 1 < γ.vertices.length) (hprev : 0 < j) :
    Disjoint
      {z | ∃ t : ℝ, t ∈ Set.Ioo (0 : ℝ) (1 : ℝ) ∧
        ∃ s : ℝ, s ≠ 0 ∧ |s| < initialConeBound j hj * t ∧
          z = AffineMap.lineMap γ.vertices[j] γ.vertices[j + 1] t +
            s • base.orientedTubes.toPolygonalArcCollarSeparatedTubeData.normal j hj}
      (segment ℝ γ.vertices[j - 1] γ.vertices[j]) := by
  rw [Set.disjoint_left]
  intro z hzCone hzSeg
  rcases hzCone with ⟨t, ht, s, hs_ne, hs_lt, hz⟩
  exact Set.disjoint_left.mp
    (base.initial_signed_cone_disjoint_previous_segment j hj hprev)
    (by
      refine ⟨t, ht, s, hs_ne, ?_, hz⟩
      exact lt_of_lt_of_le hs_lt
        (mul_le_mul_of_nonneg_right (initialConeBound_le_base j hj)
          (le_of_lt ht.1)))
    hzSeg

private lemma endpointRefinement_terminal_signed_cone_disjoint_next_segment
    (γ : PolygonalArc) {η : ℝ}
    (controlRadii : PolygonalArcCollarControlRadii γ η)
    (middleSegments : PolygonalArcCollarMiddleSegmentData γ controlRadii)
    (forbiddenMargins :
      PolygonalArcCollarMiddleForbiddenMargins γ controlRadii middleSegments)
    (base :
      PolygonalArcCollarCompatibleOrientedTubeData γ controlRadii middleSegments
        forbiddenMargins)
    (terminalConeBound : (j : ℕ) → j + 1 < γ.vertices.length → ℝ)
    (terminalConeBound_le_base :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length),
        terminalConeBound j hj ≤ base.terminalConeBound j hj)
    (j : ℕ) (hj : j + 1 < γ.vertices.length)
    (hnext : (j + 1) + 1 < γ.vertices.length) :
    Disjoint
      {z | ∃ t : ℝ, t ∈ Set.Ioo (0 : ℝ) (1 : ℝ) ∧
        ∃ s : ℝ, s ≠ 0 ∧ |s| < terminalConeBound j hj * (1 - t) ∧
          z = AffineMap.lineMap γ.vertices[j] γ.vertices[j + 1] t +
            s • base.orientedTubes.toPolygonalArcCollarSeparatedTubeData.normal j hj}
      (segment ℝ γ.vertices[j + 1] γ.vertices[j + 2]) := by
  rw [Set.disjoint_left]
  intro z hzCone hzSeg
  rcases hzCone with ⟨t, ht, s, hs_ne, hs_lt, hz⟩
  exact Set.disjoint_left.mp
    (base.terminal_signed_cone_disjoint_next_segment j hj hnext)
    (by
      refine ⟨t, ht, s, hs_ne, ?_, hz⟩
      exact lt_of_lt_of_le hs_lt
        (mul_le_mul_of_nonneg_right (terminalConeBound_le_base j hj)
          (by nlinarith [ht.2])))
    hzSeg

private lemma endpointRefinement_tube_disjoint_ball
    (a b p normal : EuclideanSpace ℝ (Fin 2))
    (lowerParam upperParam halfWidth separation radius : ℝ)
    (separation_pos : 0 < separation)
    (centerline_separated :
      ∀ c,
        c ∈ (AffineMap.lineMap a b) '' Set.Icc lowerParam upperParam →
          ∀ z, z ∈ Metric.closedBall p radius → separation ≤ dist c z)
    (halfWidth_mul_normal_norm_lt_half :
      halfWidth * ‖normal‖ < separation / 2) :
    Disjoint
      {z | ∃ t : ℝ, t ∈ Set.Ioo lowerParam upperParam ∧
        ∃ s : ℝ, s ∈ Set.Ioo (-halfWidth) halfWidth ∧
          z = AffineMap.lineMap a b t + s • normal}
      (Metric.ball p radius) := by
  rw [Set.disjoint_left]
  intro z hzTube hzBall
  rcases hzTube with ⟨t, ht, s, hs, hz⟩
  let c : EuclideanSpace ℝ (Fin 2) := AffineMap.lineMap a b t
  have hcCenter : c ∈ (AffineMap.lineMap a b) '' Set.Icc lowerParam upperParam :=
    ⟨t, ⟨le_of_lt ht.1, le_of_lt ht.2⟩, rfl⟩
  have hzClosed : z ∈ Metric.closedBall p radius := by
    rw [Metric.mem_closedBall]
    exact le_of_lt (by simpa [Metric.mem_ball] using hzBall)
  have hsep := centerline_separated c hcCenter z hzClosed
  have hs_abs : |s| < halfWidth := abs_lt.mpr hs
  have hdist : dist z c = |s| * ‖normal‖ := by
    rw [hz]
    have hsub : AffineMap.lineMap a b t + s • normal - c = s • normal := by
      simp [c]
    rw [dist_eq_norm, hsub, norm_smul, Real.norm_eq_abs]
  have hclose : dist c z < separation / 2 := by
    calc
      dist c z = dist z c := dist_comm c z
      _ = |s| * ‖normal‖ := hdist
      _ ≤ halfWidth * ‖normal‖ :=
        mul_le_mul_of_nonneg_right (le_of_lt hs_abs) (norm_nonneg _)
      _ < separation / 2 := halfWidth_mul_normal_norm_lt_half
  nlinarith

private lemma endpointRefinement_width_mul_norm_lt_half
    {width separation normalNorm : ℝ}
    (normalNorm_nonneg : 0 ≤ normalNorm) (separation_pos : 0 < separation)
    (width_le : width ≤ separation / (4 * (normalNorm + 1))) :
    width * normalNorm < separation / 2 := by
  have hden : 0 < 4 * (normalNorm + 1) := by positivity
  have hden_ne : 4 * (normalNorm + 1) ≠ 0 := ne_of_gt hden
  have hscaled :
      separation / (4 * (normalNorm + 1)) * normalNorm < separation / 2 := by
    field_simp [hden_ne]
    nlinarith
  exact (mul_le_mul_of_nonneg_right width_le normalNorm_nonneg).trans_lt hscaled

private lemma endpointRefinement_source_centerline_disjoint_closedBall
    (γ : PolygonalArc) {η : ℝ}
    (controlRadii : PolygonalArcCollarControlRadii γ η)
    (middleSegments : PolygonalArcCollarMiddleSegmentData γ controlRadii)
    (forbiddenMargins :
      PolygonalArcCollarMiddleForbiddenMargins γ controlRadii middleSegments)
    (old :
      PolygonalArcCollarSeparatedTubeData γ controlRadii middleSegments forbiddenMargins)
    (r₀ r₁ : ℝ) (hIso : PolygonalArcEndpointIsolation γ r₀ r₁)
    (j : ℕ) (hj : j + 1 < γ.vertices.length) (hj0 : j ≠ 0) :
    Disjoint
      ((AffineMap.lineMap γ.vertices[j] γ.vertices[j + 1]) ''
        Set.Icc (old.lowerParam j hj) (old.upperParam j hj))
      (Metric.closedBall γ.source r₀) := by
  have hfirst : 0 + 1 < γ.vertices.length := by
    have hlen := γ.length_ge_two
    omega
  have segmentEndpoints_ne : γ.vertices[j] ≠ γ.vertices[j + 1] := by
    have hdist_pos : 0 < dist γ.vertices[j] γ.vertices[j + 1] := by
      have hsum := controlRadii.adjacent_radii_sum_lt (j := j) hj
      have hleft := controlRadii.radius_pos ⟨j, Nat.lt_of_succ_lt hj⟩
      have hright := controlRadii.radius_pos ⟨j + 1, hj⟩
      nlinarith
    exact dist_pos.mp hdist_pos
  have hsource_vertex : γ.vertices[0] = γ.source := by
    have hsourceIdx : 0 < γ.vertices.length := by
      have hlen := γ.length_ge_two
      omega
    have hget : γ.vertices[0]? = some γ.vertices[0] :=
      List.getElem?_eq_getElem hsourceIdx
    rw [← List.head?_eq_getElem?, γ.source_eq_head] at hget
    exact Option.some.inj hget.symm
  rw [Set.disjoint_left]
  intro x hxCenter hxBall
  rcases hxCenter with ⟨t, ht, htx⟩
  have hxSegJ : x ∈ segment ℝ γ.vertices[j] γ.vertices[j + 1] := by
    rw [segment_eq_image_lineMap]
    refine ⟨t, ?_, htx⟩
    exact ⟨le_trans (le_of_lt (old.lowerParam_pos j hj)) ht.1,
      le_trans ht.2 (le_of_lt (old.upperParam_lt_one j hj))⟩
  have hxCarrier : x ∈ γ.carrier := by
    rw [γ.carrier_eq]
    exact ⟨j, hj, hxSegJ⟩
  have hxFirstSource :
      x ∈ segment ℝ γ.source (γ.vertices[1]'(by
        have hlen := γ.length_ge_two
        omega)) :=
    hIso.source_closedBall_carrier_subset_initial_segment ⟨hxBall, hxCarrier⟩
  have hxFirst : x ∈ segment ℝ γ.vertices[0] γ.vertices[1] := by
    simpa [hsource_vertex] using hxFirstSource
  by_cases hj1 : j = 1
  · subst j
    have hinter :
        segment ℝ γ.vertices[0] γ.vertices[0 + 1] ∩
            segment ℝ γ.vertices[1] γ.vertices[1 + 1] =
          ({γ.vertices[1]} : Set (EuclideanSpace ℝ (Fin 2))) := by
      have hraw := γ.segment_intersections (i := 0) (j := 1) hfirst hj (by omega)
      simpa using hraw
    have hxInter :
        x ∈ segment ℝ γ.vertices[0] γ.vertices[0 + 1] ∩
            segment ℝ γ.vertices[1] γ.vertices[1 + 1] :=
      ⟨by simpa using hxFirst, hxSegJ⟩
    rw [hinter] at hxInter
    have hxVertex : x = γ.vertices[1] := by simpa using hxInter
    let f : ℝ →ᵃ[ℝ] EuclideanSpace ℝ (Fin 2) :=
      AffineMap.lineMap γ.vertices[1] γ.vertices[1 + 1]
    have hf : Function.Injective f :=
      AffineMap.lineMap_injective (k := ℝ) segmentEndpoints_ne
    have ht0 : t = 0 := by
      apply hf
      calc
        f t = x := by simpa [f] using htx
        _ = γ.vertices[1] := hxVertex
        _ = f 0 := by simp [f]
    linarith [old.lowerParam_pos 1 hj, ht.1]
  · have hjgt : 1 < j := by omega
    have hnot_adj : j ≠ 0 + 1 := by omega
    have hinter :
        segment ℝ γ.vertices[0] γ.vertices[0 + 1] ∩
            segment ℝ γ.vertices[j] γ.vertices[j + 1] =
          (∅ : Set (EuclideanSpace ℝ (Fin 2))) := by
      have hraw := γ.segment_intersections (i := 0) (j := j) hfirst hj (by omega)
      simpa [hnot_adj] using hraw
    have hxInter :
        x ∈ segment ℝ γ.vertices[0] γ.vertices[0 + 1] ∩
            segment ℝ γ.vertices[j] γ.vertices[j + 1] :=
      ⟨by simpa using hxFirst, hxSegJ⟩
    rw [hinter] at hxInter
    exact hxInter

private lemma endpointRefinement_target_centerline_disjoint_closedBall
    (γ : PolygonalArc) {η : ℝ}
    (controlRadii : PolygonalArcCollarControlRadii γ η)
    (middleSegments : PolygonalArcCollarMiddleSegmentData γ controlRadii)
    (forbiddenMargins :
      PolygonalArcCollarMiddleForbiddenMargins γ controlRadii middleSegments)
    (old :
      PolygonalArcCollarSeparatedTubeData γ controlRadii middleSegments forbiddenMargins)
    (r₀ r₁ : ℝ) (hIso : PolygonalArcEndpointIsolation γ r₀ r₁)
    (j : ℕ) (hj : j + 1 < γ.vertices.length)
    (hjlast : j ≠ γ.vertices.length - 2) :
    Disjoint
      ((AffineMap.lineMap γ.vertices[j] γ.vertices[j + 1]) ''
        Set.Icc (old.lowerParam j hj) (old.upperParam j hj))
      (Metric.closedBall γ.target r₁) := by
  let jlast : ℕ := γ.vertices.length - 2
  have hlast : jlast + 1 < γ.vertices.length := by
    have hlen := γ.length_ge_two
    dsimp [jlast]
    omega
  have hlast_succ : jlast + 1 = γ.vertices.length - 1 := by
    have hlen := γ.length_ge_two
    dsimp [jlast]
    omega
  have segmentEndpoints_ne : γ.vertices[j] ≠ γ.vertices[j + 1] := by
    have hdist_pos : 0 < dist γ.vertices[j] γ.vertices[j + 1] := by
      have hsum := controlRadii.adjacent_radii_sum_lt (j := j) hj
      have hleft := controlRadii.radius_pos ⟨j, Nat.lt_of_succ_lt hj⟩
      have hright := controlRadii.radius_pos ⟨j + 1, hj⟩
      nlinarith
    exact dist_pos.mp hdist_pos
  have htarget_vertex : γ.vertices[γ.vertices.length - 1] = γ.target := by
    have htargetIdx : γ.vertices.length - 1 < γ.vertices.length := by
      have hlen := γ.length_ge_two
      omega
    have hget :
        γ.vertices[γ.vertices.length - 1]? =
          some γ.vertices[γ.vertices.length - 1] :=
      List.getElem?_eq_getElem htargetIdx
    rw [← List.getLast?_eq_getElem?, γ.target_eq_last] at hget
    exact Option.some.inj hget.symm
  have htarget_jlast : γ.vertices[jlast + 1] = γ.target := by
    simpa [hlast_succ] using htarget_vertex
  rw [Set.disjoint_left]
  intro x hxCenter hxBall
  rcases hxCenter with ⟨t, ht, htx⟩
  have hxSegJ : x ∈ segment ℝ γ.vertices[j] γ.vertices[j + 1] := by
    rw [segment_eq_image_lineMap]
    refine ⟨t, ?_, htx⟩
    exact ⟨le_trans (le_of_lt (old.lowerParam_pos j hj)) ht.1,
      le_trans ht.2 (le_of_lt (old.upperParam_lt_one j hj))⟩
  have hxCarrier : x ∈ γ.carrier := by
    rw [γ.carrier_eq]
    exact ⟨j, hj, hxSegJ⟩
  have hxTerminalSource :
      x ∈ segment ℝ γ.target (γ.vertices[γ.vertices.length - 2]'(by
        have hlen := γ.length_ge_two
        omega)) :=
    hIso.target_closedBall_carrier_subset_terminal_segment ⟨hxBall, hxCarrier⟩
  have hxLast : x ∈ segment ℝ γ.vertices[jlast] γ.vertices[jlast + 1] := by
    simpa [jlast, htarget_jlast, segment_symm] using hxTerminalSource
  have hj_lt_last : j < jlast := by
    have hlen := γ.length_ge_two
    dsimp [jlast] at hjlast ⊢
    omega
  by_cases hadj : jlast = j + 1
  · have hinter :
        segment ℝ γ.vertices[j] γ.vertices[j + 1] ∩
            segment ℝ γ.vertices[jlast] γ.vertices[jlast + 1] =
          ({γ.vertices[jlast]} : Set (EuclideanSpace ℝ (Fin 2))) := by
      have hraw :=
        γ.segment_intersections (i := j) (j := jlast) hj hlast hj_lt_last
      simpa [hadj] using hraw
    have hxInter :
        x ∈ segment ℝ γ.vertices[j] γ.vertices[j + 1] ∩
            segment ℝ γ.vertices[jlast] γ.vertices[jlast + 1] :=
      ⟨hxSegJ, hxLast⟩
    rw [hinter] at hxInter
    have hxVertex : x = γ.vertices[j + 1] := by
      simpa [hadj] using hxInter
    let f : ℝ →ᵃ[ℝ] EuclideanSpace ℝ (Fin 2) :=
      AffineMap.lineMap γ.vertices[j] γ.vertices[j + 1]
    have hf : Function.Injective f :=
      AffineMap.lineMap_injective (k := ℝ) segmentEndpoints_ne
    have ht1 : t = 1 := by
      apply hf
      calc
        f t = x := by simpa [f] using htx
        _ = γ.vertices[j + 1] := hxVertex
        _ = f 1 := by simp [f]
    linarith [old.upperParam_lt_one j hj, ht.2]
  · have hinter :
        segment ℝ γ.vertices[j] γ.vertices[j + 1] ∩
            segment ℝ γ.vertices[jlast] γ.vertices[jlast + 1] =
          (∅ : Set (EuclideanSpace ℝ (Fin 2))) := by
      have hraw :=
        γ.segment_intersections (i := j) (j := jlast) hj hlast hj_lt_last
      simpa [hadj] using hraw
    have hxInter :
        x ∈ segment ℝ γ.vertices[j] γ.vertices[j + 1] ∩
            segment ℝ γ.vertices[jlast] γ.vertices[jlast + 1] :=
      ⟨hxSegJ, hxLast⟩
    rw [hinter] at hxInter
    exact hxInter


lemma PolygonalArcCollarCompatibleOrientedTubeDataEndpointRefinement (γ : PolygonalArc)
    {η : ℝ} (controlRadii : PolygonalArcCollarControlRadii γ η)
    (middleSegments : PolygonalArcCollarMiddleSegmentData γ controlRadii)
    (forbiddenMargins :
      PolygonalArcCollarMiddleForbiddenMargins γ controlRadii middleSegments)
    (base :
      PolygonalArcCollarCompatibleOrientedTubeData γ controlRadii middleSegments
        forbiddenMargins)
    (r₀ r₁ K₀ K₁ : ℝ) :
    PolygonalArcEndpointIsolation γ r₀ r₁ →
      0 < K₀ →
      0 < K₁ →
        let hfirst : 0 + 1 < γ.vertices.length := by
          have hlen := γ.length_ge_two
          omega
        let jlast : ℕ := γ.vertices.length - 2
        let hlast : jlast + 1 < γ.vertices.length := by
          have _hlen := γ.length_ge_two
          dsimp [jlast]
          omega
        ∃ compatibleTubes :
          PolygonalArcCollarCompatibleOrientedTubeData γ controlRadii
            middleSegments forbiddenMargins,
          compatibleTubes.initialConeBound 0 hfirst < K₀ ∧
            compatibleTubes.terminalConeBound jlast hlast < K₁ ∧
              (∀ (j : ℕ) (hj : j + 1 < γ.vertices.length), j ≠ 0 →
                Disjoint
                  (compatibleTubes.orientedTubes.toPolygonalArcCollarSeparatedTubeData.tube
                    j hj)
                  (Metric.ball γ.source r₀)) ∧
                (∀ (j : ℕ) (hj : j + 1 < γ.vertices.length), j ≠ jlast →
                  Disjoint
                    (compatibleTubes.orientedTubes.toPolygonalArcCollarSeparatedTubeData.tube
                      j hj)
                    (Metric.ball γ.target r₁)) := by
  intro hIso hK₀ hK₁
  let old := base.orientedTubes.toPolygonalArcCollarSeparatedTubeData
  let hfirst : 0 + 1 < γ.vertices.length := by
    have hlen := γ.length_ge_two
    omega
  let jlast : ℕ := γ.vertices.length - 2
  let hlast : jlast + 1 < γ.vertices.length := by
    have hlen := γ.length_ge_two
    dsimp [jlast]
    omega
  have old_lower_lt_upper :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length),
        old.lowerParam j hj < old.upperParam j hj := by
    intro j hj
    calc
      old.lowerParam j hj <
          controlRadii.radius ⟨j, Nat.lt_of_succ_lt hj⟩ /
            dist γ.vertices[j] γ.vertices[j + 1] :=
        old.lowerParam_lt_left_parameter j hj
      _ < 1 - controlRadii.radius ⟨j + 1, hj⟩ /
            dist γ.vertices[j] γ.vertices[j + 1] :=
        middleSegments.left_parameter_lt_right_parameter j hj
      _ < old.upperParam j hj :=
        old.right_parameter_lt_upperParam j hj
  let centerline : (j : ℕ) → j + 1 < γ.vertices.length →
      Set (EuclideanSpace ℝ (Fin 2)) := fun j hj =>
    (AffineMap.lineMap γ.vertices[j] γ.vertices[j + 1]) ''
      Set.Icc (old.lowerParam j hj) (old.upperParam j hj)
  have centerline_nonempty :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length),
        (centerline j hj).Nonempty := by
    intro j hj
    refine ⟨AffineMap.lineMap γ.vertices[j] γ.vertices[j + 1]
      (old.lowerParam j hj), ?_⟩
    exact ⟨old.lowerParam j hj,
      ⟨le_rfl, le_of_lt (old_lower_lt_upper j hj)⟩, rfl⟩
  have centerline_compact :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length),
        IsCompact (centerline j hj) := by
    intro j hj
    dsimp [centerline]
    exact isCompact_Icc.image AffineMap.lineMap_continuous
  have sourceCenterline_disjoint_closedBall :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length), j ≠ 0 →
        Disjoint (centerline j hj) (Metric.closedBall γ.source r₀) := by
    intro j hj hj0
    exact endpointRefinement_source_centerline_disjoint_closedBall
      γ controlRadii middleSegments forbiddenMargins old r₀ r₁ hIso j hj hj0
  have targetCenterline_disjoint_closedBall :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length), j ≠ jlast →
        Disjoint (centerline j hj) (Metric.closedBall γ.target r₁) := by
    intro j hj hjlast
    exact endpointRefinement_target_centerline_disjoint_closedBall
      γ controlRadii middleSegments forbiddenMargins old r₀ r₁ hIso j hj
        (by simpa [jlast] using hjlast)
  have sourceSeparationExists :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length), j ≠ 0 →
        ∃ ε : ℝ, 0 < ε ∧
          ∀ c, c ∈ centerline j hj →
            ∀ z, z ∈ Metric.closedBall γ.source r₀ → ε ≤ dist c z := by
    intro j hj hj0
    have hball_nonempty : (Metric.closedBall γ.source r₀).Nonempty := by
      refine ⟨γ.source, ?_⟩
      simp [Metric.mem_closedBall, le_of_lt hIso.source_pos]
    exact PositiveSeparation (centerline_nonempty j hj) hball_nonempty
      (centerline_compact j hj) (isCompact_closedBall γ.source r₀)
      (sourceCenterline_disjoint_closedBall j hj hj0)
  have targetSeparationExists :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length), j ≠ jlast →
        ∃ ε : ℝ, 0 < ε ∧
          ∀ c, c ∈ centerline j hj →
            ∀ z, z ∈ Metric.closedBall γ.target r₁ → ε ≤ dist c z := by
    intro j hj hjlast
    have hball_nonempty : (Metric.closedBall γ.target r₁).Nonempty := by
      refine ⟨γ.target, ?_⟩
      simp [Metric.mem_closedBall, le_of_lt hIso.target_pos]
    exact PositiveSeparation (centerline_nonempty j hj) hball_nonempty
      (centerline_compact j hj) (isCompact_closedBall γ.target r₁)
      (targetCenterline_disjoint_closedBall j hj hjlast)
  let sourceSeparation :
      (j : ℕ) → (hj : j + 1 < γ.vertices.length) → j ≠ 0 → ℝ :=
    fun j hj hj0 => Classical.choose (sourceSeparationExists j hj hj0)
  let targetSeparation :
      (j : ℕ) → (hj : j + 1 < γ.vertices.length) → j ≠ jlast → ℝ :=
    fun j hj hjlast => Classical.choose (targetSeparationExists j hj hjlast)
  have sourceSeparation_pos :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length) (hj0 : j ≠ 0),
        0 < sourceSeparation j hj hj0 := by
    intro j hj hj0
    simpa [sourceSeparation] using
      (Classical.choose_spec (sourceSeparationExists j hj hj0)).1
  have targetSeparation_pos :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length) (hjlast : j ≠ jlast),
        0 < targetSeparation j hj hjlast := by
    intro j hj hjlast
    simpa [targetSeparation] using
      (Classical.choose_spec (targetSeparationExists j hj hjlast)).1
  let initialConeBound : (j : ℕ) → j + 1 < γ.vertices.length → ℝ := fun j hj =>
    if j = 0 then min (base.initialConeBound j hj) (K₀ / 2)
    else base.initialConeBound j hj
  let terminalConeBound : (j : ℕ) → j + 1 < γ.vertices.length → ℝ := fun j hj =>
    if j = jlast then min (base.terminalConeBound j hj) (K₁ / 2)
    else base.terminalConeBound j hj
  have initialConeBound_pos :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length), 0 < initialConeBound j hj := by
    intro j hj
    dsimp [initialConeBound]
    by_cases hj0 : j = 0
    · simpa [hj0] using
        lt_min (base.initialConeBound_pos j hj) (half_pos hK₀)
    · simpa [hj0] using base.initialConeBound_pos j hj
  have terminalConeBound_pos :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length), 0 < terminalConeBound j hj := by
    intro j hj
    dsimp [terminalConeBound]
    by_cases hjlast : j = jlast
    · simpa [hjlast] using
        lt_min (base.terminalConeBound_pos j hj) (half_pos hK₁)
    · simpa [hjlast] using base.terminalConeBound_pos j hj
  have initialConeBound_le_base :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length),
        initialConeBound j hj ≤ base.initialConeBound j hj := by
    intro j hj
    dsimp [initialConeBound]
    by_cases hj0 : j = 0
    · simp [hj0]
    · simp [hj0]
  have terminalConeBound_le_base :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length),
        terminalConeBound j hj ≤ base.terminalConeBound j hj := by
    intro j hj
    dsimp [terminalConeBound]
    by_cases hjlast : j = jlast
    · simp [hjlast]
    · simp [hjlast]
  let sourceEndpointWidthTerm : (j : ℕ) → j + 1 < γ.vertices.length → ℝ :=
    fun j hj =>
      if hj0 : j = 0 then 1
      else sourceSeparation j hj hj0 / (4 * (‖old.normal j hj‖ + 1))
  let targetEndpointWidthTerm : (j : ℕ) → j + 1 < γ.vertices.length → ℝ :=
    fun j hj =>
      if hjlast : j = jlast then 1
      else targetSeparation j hj hjlast / (4 * (‖old.normal j hj‖ + 1))
  let halfWidth : (j : ℕ) → j + 1 < γ.vertices.length → ℝ := fun j hj =>
    min (min (old.halfWidth j hj / 2)
      (initialConeBound j hj * old.lowerParam j hj / 2))
      (min (terminalConeBound j hj * (1 - old.upperParam j hj) / 2)
        (min (sourceEndpointWidthTerm j hj) (targetEndpointWidthTerm j hj)))
  have one_sub_old_upper_pos :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length),
        0 < 1 - old.upperParam j hj := by
    intro j hj
    linarith [old.upperParam_lt_one j hj]
  have sourceEndpointWidthTerm_pos :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length),
        0 < sourceEndpointWidthTerm j hj := by
    intro j hj
    dsimp [sourceEndpointWidthTerm]
    by_cases hj0 : j = 0
    · simp [hj0]
    · have hden : 0 < 4 * (‖old.normal j hj‖ + 1) := by positivity
      simpa [hj0] using div_pos (sourceSeparation_pos j hj hj0) hden
  have targetEndpointWidthTerm_pos :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length),
        0 < targetEndpointWidthTerm j hj := by
    intro j hj
    dsimp [targetEndpointWidthTerm]
    by_cases hjlast : j = jlast
    · simp [hjlast]
    · have hden : 0 < 4 * (‖old.normal j hj‖ + 1) := by positivity
      simpa [hjlast] using div_pos (targetSeparation_pos j hj hjlast) hden
  have halfWidth_pos :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length), 0 < halfWidth j hj := by
    intro j hj
    dsimp [halfWidth]
    exact lt_min
      (lt_min (half_pos (old.halfWidth_pos j hj))
        (half_pos (mul_pos (initialConeBound_pos j hj) (old.lowerParam_pos j hj))))
      (lt_min
        (half_pos (mul_pos (terminalConeBound_pos j hj)
          (one_sub_old_upper_pos j hj)))
        (lt_min (sourceEndpointWidthTerm_pos j hj)
          (targetEndpointWidthTerm_pos j hj)))
  have halfWidth_le_old_half :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length),
        halfWidth j hj ≤ old.halfWidth j hj / 2 := by
    intro j hj
    dsimp [halfWidth]
    exact le_trans (min_le_left _ _) (min_le_left _ _)
  have halfWidth_lt_old :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length),
        halfWidth j hj < old.halfWidth j hj := by
    intro j hj
    have hhalf : old.halfWidth j hj / 2 < old.halfWidth j hj := by
      nlinarith [old.halfWidth_pos j hj]
    exact lt_of_le_of_lt (halfWidth_le_old_half j hj) hhalf
  have halfWidth_le_initialConeWidth :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length),
        halfWidth j hj ≤ initialConeBound j hj * old.lowerParam j hj / 2 := by
    intro j hj
    dsimp [halfWidth]
    exact le_trans (min_le_left _ _) (min_le_right _ _)
  have halfWidth_le_terminalConeWidth :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length),
        halfWidth j hj ≤ terminalConeBound j hj * (1 - old.upperParam j hj) / 2 := by
    intro j hj
    dsimp [halfWidth]
    exact le_trans (min_le_right _ _) (min_le_left _ _)
  have halfWidth_le_sourceEndpointWidthTerm :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length),
        halfWidth j hj ≤ sourceEndpointWidthTerm j hj := by
    intro j hj
    dsimp [halfWidth]
    exact le_trans (min_le_right _ _)
      (le_trans (min_le_right _ _) (min_le_left _ _))
  have halfWidth_le_targetEndpointWidthTerm :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length),
        halfWidth j hj ≤ targetEndpointWidthTerm j hj := by
    intro j hj
    dsimp [halfWidth]
    exact le_trans (min_le_right _ _)
      (le_trans (min_le_right _ _) (min_le_right _ _))
  have halfWidth_lt_initialCone_mul_lowerParam :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length),
        halfWidth j hj < initialConeBound j hj * old.lowerParam j hj := by
    intro j hj
    have hprod : 0 < initialConeBound j hj * old.lowerParam j hj :=
      mul_pos (initialConeBound_pos j hj) (old.lowerParam_pos j hj)
    have hhalf :
        initialConeBound j hj * old.lowerParam j hj / 2 <
          initialConeBound j hj * old.lowerParam j hj := by
      nlinarith
    exact lt_of_le_of_lt (halfWidth_le_initialConeWidth j hj) hhalf
  have halfWidth_lt_terminalCone_mul_one_sub_upperParam :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length),
        halfWidth j hj < terminalConeBound j hj * (1 - old.upperParam j hj) := by
    intro j hj
    have hprod : 0 < terminalConeBound j hj * (1 - old.upperParam j hj) :=
      mul_pos (terminalConeBound_pos j hj) (one_sub_old_upper_pos j hj)
    have hhalf :
        terminalConeBound j hj * (1 - old.upperParam j hj) / 2 <
          terminalConeBound j hj * (1 - old.upperParam j hj) := by
      nlinarith
    exact lt_of_le_of_lt (halfWidth_le_terminalConeWidth j hj) hhalf
  have halfWidth_mul_normal_norm_lt_source_half :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length) (hj0 : j ≠ 0),
        halfWidth j hj * ‖old.normal j hj‖ <
          sourceSeparation j hj hj0 / 2 := by
    intro j hj hj0
    have hle :
        halfWidth j hj ≤
          sourceSeparation j hj hj0 / (4 * (‖old.normal j hj‖ + 1)) := by
      dsimp [sourceEndpointWidthTerm] at halfWidth_le_sourceEndpointWidthTerm
      simpa [hj0] using halfWidth_le_sourceEndpointWidthTerm j hj
    exact endpointRefinement_width_mul_norm_lt_half (norm_nonneg _)
      (sourceSeparation_pos j hj hj0) hle
  have halfWidth_mul_normal_norm_lt_target_half :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length) (hjlast : j ≠ jlast),
        halfWidth j hj * ‖old.normal j hj‖ <
          targetSeparation j hj hjlast / 2 := by
    intro j hj hjlast
    have hle :
        halfWidth j hj ≤
          targetSeparation j hj hjlast / (4 * (‖old.normal j hj‖ + 1)) := by
      dsimp [targetEndpointWidthTerm] at halfWidth_le_targetEndpointWidthTerm
      simpa [hjlast] using halfWidth_le_targetEndpointWidthTerm j hj
    exact endpointRefinement_width_mul_norm_lt_half (norm_nonneg _)
      (targetSeparation_pos j hj hjlast) hle
  let tube : (j : ℕ) → j + 1 < γ.vertices.length →
      Set (EuclideanSpace ℝ (Fin 2)) := fun j hj =>
    {z | ∃ t : ℝ, t ∈ Set.Ioo (old.lowerParam j hj) (old.upperParam j hj) ∧
      ∃ s : ℝ, s ∈ Set.Ioo (-(halfWidth j hj)) (halfWidth j hj) ∧
        z =
          AffineMap.lineMap γ.vertices[j] γ.vertices[j + 1] t +
            s • old.normal j hj}
  let leftHalf : (j : ℕ) → j + 1 < γ.vertices.length →
      Set (EuclideanSpace ℝ (Fin 2)) := fun j hj =>
    {z | ∃ t : ℝ, t ∈ Set.Ioo (old.lowerParam j hj) (old.upperParam j hj) ∧
      ∃ s : ℝ, s ∈ Set.Ioo (0 : ℝ) (halfWidth j hj) ∧
        z =
          AffineMap.lineMap γ.vertices[j] γ.vertices[j + 1] t +
            s • old.normal j hj}
  let rightHalf : (j : ℕ) → j + 1 < γ.vertices.length →
      Set (EuclideanSpace ℝ (Fin 2)) := fun j hj =>
    {z | ∃ t : ℝ, t ∈ Set.Ioo (old.lowerParam j hj) (old.upperParam j hj) ∧
      ∃ s : ℝ, s ∈ Set.Ioo (-(halfWidth j hj)) (0 : ℝ) ∧
        z =
          AffineMap.lineMap γ.vertices[j] γ.vertices[j + 1] t +
            s • old.normal j hj}
  have tube_subset_old :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length),
        tube j hj ⊆ old.tube j hj := by
    intro j hj z hz
    dsimp [tube] at hz
    rcases hz with ⟨t, ht, s, hs, rfl⟩
    rw [old.tube_eq j hj]
    refine ⟨t, ht, s, ?_, rfl⟩
    have hW := halfWidth_lt_old j hj
    exact ⟨lt_trans (neg_lt_neg hW) hs.1, lt_trans hs.2 hW⟩
  have middle_subset_tube :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length),
        middleSegments.middle j hj ⊆ tube j hj := by
    intro j hj z hz
    rw [middleSegments.middle_eq j hj] at hz
    rcases hz with ⟨t, ht, rfl⟩
    dsimp [tube]
    refine ⟨t, ?_, 0, ?_, by simp⟩
    · exact ⟨(old.lowerParam_lt_left_parameter j hj).trans_le ht.1,
        lt_of_le_of_lt ht.2 (old.right_parameter_lt_upperParam j hj)⟩
    · exact ⟨by simpa using halfWidth_pos j hj, halfWidth_pos j hj⟩
  have leftHalf_subset_tube :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length),
        leftHalf j hj ⊆ tube j hj := by
    intro j hj z hz
    dsimp [leftHalf] at hz
    rcases hz with ⟨t, ht, s, hs, rfl⟩
    dsimp [tube]
    refine ⟨t, ht, s, ?_, rfl⟩
    exact ⟨lt_trans (neg_neg_of_pos (halfWidth_pos j hj)) hs.1, hs.2⟩
  have rightHalf_subset_tube :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length),
        rightHalf j hj ⊆ tube j hj := by
    intro j hj z hz
    dsimp [rightHalf] at hz
    rcases hz with ⟨t, ht, s, hs, rfl⟩
    dsimp [tube]
    refine ⟨t, ht, s, ?_, rfl⟩
    exact ⟨hs.1, hs.2.trans (halfWidth_pos j hj)⟩
  have tube_subset_eta_neighborhood :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length),
        ∀ z ∈ tube j hj, ∃ p ∈ γ.carrier, dist z p < η := by
    intro j hj z hz
    exact old.tube_subset_eta_neighborhood j hj z (tube_subset_old j hj hz)
  have tube_point_close_to_middle :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length),
        ∀ z ∈ tube j hj, ∃ p ∈ middleSegments.middle j hj,
          dist z p < forbiddenMargins.margin j hj / 2 := by
    intro j hj z hz
    exact old.tube_point_close_to_middle j hj z (tube_subset_old j hj hz)
  have tube_disjoint_nonadjacent_segments :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length)
        (k : ℕ) (hk : k + 1 < γ.vertices.length),
          (j + 1 < k ∨ k + 1 < j) →
            Disjoint (tube j hj) (segment ℝ γ.vertices[k] γ.vertices[k + 1]) := by
    intro j hj k hk hgap
    rw [Set.disjoint_left]
    intro z hzTube hzSeg
    exact Set.disjoint_left.mp
      (old.tube_disjoint_nonadjacent_segments j hj k hk hgap)
      (tube_subset_old j hj hzTube) hzSeg
  have tube_disjoint_nonincident_control_disks :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length)
        (i : Fin γ.vertices.length),
          i.1 ≠ j → i.1 ≠ j + 1 →
            Disjoint (tube j hj)
              (Metric.closedBall γ.vertices[i.1] (controlRadii.radius i)) := by
    intro j hj i hij hijs
    rw [Set.disjoint_left]
    intro z hzTube hzDisk
    exact Set.disjoint_left.mp
      (old.tube_disjoint_nonincident_control_disks j hj i hij hijs)
      (tube_subset_old j hj hzTube) hzDisk
  have tube_disjoint_nonadjacent_middle_cores :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length)
        (k : ℕ) (hk : k + 1 < γ.vertices.length),
          (j + 1 < k ∨ k + 1 < j) →
            Disjoint (tube j hj) (middleSegments.middle k hk) := by
    intro j hj k hk hgap
    rw [Set.disjoint_left]
    intro z hzTube hzMiddle
    exact Set.disjoint_left.mp
      (old.tube_disjoint_nonadjacent_middle_cores j hj k hk hgap)
      (tube_subset_old j hj hzTube) hzMiddle
  have tube_disjoint_nonadjacent_tubes :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length)
        (k : ℕ) (hk : k + 1 < γ.vertices.length),
          (j + 1 < k ∨ k + 1 < j) →
            Disjoint (tube j hj) (tube k hk) := by
    intro j hj k hk hgap
    rw [Set.disjoint_left]
    intro z hzj hzk
    exact Set.disjoint_left.mp
      (old.tube_disjoint_nonadjacent_tubes j hj k hk hgap)
      (tube_subset_old j hj hzj) (tube_subset_old k hk hzk)
  have halfWidth_mul_normal_norm_lt_eta :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length),
        halfWidth j hj * ‖old.normal j hj‖ < η := by
    intro j hj
    calc
      halfWidth j hj * ‖old.normal j hj‖
          ≤ old.halfWidth j hj * ‖old.normal j hj‖ :=
        mul_le_mul_of_nonneg_right (le_of_lt (halfWidth_lt_old j hj)) (norm_nonneg _)
      _ < η := old.halfWidth_mul_normal_norm_lt_eta j hj
  have halfWidth_mul_normal_norm_lt_margin_quarter :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length),
        halfWidth j hj * ‖old.normal j hj‖ <
          forbiddenMargins.margin j hj / 4 := by
    intro j hj
    calc
      halfWidth j hj * ‖old.normal j hj‖
          ≤ old.halfWidth j hj * ‖old.normal j hj‖ :=
        mul_le_mul_of_nonneg_right (le_of_lt (halfWidth_lt_old j hj)) (norm_nonneg _)
      _ < forbiddenMargins.margin j hj / 4 :=
        old.halfWidth_mul_normal_norm_lt_margin_quarter j hj
  have initial_signed_cone_disjoint_previous_segment :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length) (_hprev : 0 < j),
        Disjoint
          {z | ∃ t : ℝ, t ∈ Set.Ioo (0 : ℝ) (1 : ℝ) ∧
            ∃ s : ℝ, s ≠ 0 ∧ |s| < initialConeBound j hj * t ∧
              z =
                AffineMap.lineMap γ.vertices[j] γ.vertices[j + 1] t +
                  s • old.normal j hj}
          (segment ℝ γ.vertices[j - 1] γ.vertices[j]) := by
    intro j hj hprev
    exact endpointRefinement_initial_signed_cone_disjoint_previous_segment
      γ controlRadii middleSegments forbiddenMargins base initialConeBound
        initialConeBound_le_base j hj hprev
  have terminal_signed_cone_disjoint_next_segment :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length)
        (_hnext : (j + 1) + 1 < γ.vertices.length),
          Disjoint
            {z | ∃ t : ℝ, t ∈ Set.Ioo (0 : ℝ) (1 : ℝ) ∧
              ∃ s : ℝ, s ≠ 0 ∧ |s| < terminalConeBound j hj * (1 - t) ∧
                z =
                  AffineMap.lineMap γ.vertices[j] γ.vertices[j + 1] t +
                    s • old.normal j hj}
            (segment ℝ γ.vertices[j + 1] γ.vertices[j + 2]) := by
    intro j hj hnext
    exact endpointRefinement_terminal_signed_cone_disjoint_next_segment
      γ controlRadii middleSegments forbiddenMargins base terminalConeBound
        terminalConeBound_le_base j hj hnext
  have initial_halfWidth_mul_normal_norm_lt_away_quarter :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length) (hprev : 0 < j),
        halfWidth j hj * ‖old.normal j hj‖ <
          base.initialAwaySeparation j hj hprev / 4 := by
    intro j hj hprev
    calc
      halfWidth j hj * ‖old.normal j hj‖
          ≤ old.halfWidth j hj * ‖old.normal j hj‖ :=
        mul_le_mul_of_nonneg_right (le_of_lt (halfWidth_lt_old j hj)) (norm_nonneg _)
      _ < base.initialAwaySeparation j hj hprev / 4 :=
        base.initial_halfWidth_mul_normal_norm_lt_away_quarter j hj hprev
  have terminal_halfWidth_mul_normal_norm_lt_away_quarter :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length)
        (hnext : (j + 1) + 1 < γ.vertices.length),
          halfWidth j hj * ‖old.normal j hj‖ <
            base.terminalAwaySeparation j hj hnext / 4 := by
    intro j hj hnext
    calc
      halfWidth j hj * ‖old.normal j hj‖
          ≤ old.halfWidth j hj * ‖old.normal j hj‖ :=
        mul_le_mul_of_nonneg_right (le_of_lt (halfWidth_lt_old j hj)) (norm_nonneg _)
      _ < base.terminalAwaySeparation j hj hnext / 4 :=
        base.terminal_halfWidth_mul_normal_norm_lt_away_quarter j hj hnext
  have successive_halfWidth_normal_sum_lt_away_quarter :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length)
        (hnext : (j + 1) + 1 < γ.vertices.length),
          halfWidth j hj * ‖old.normal j hj‖ +
            halfWidth (j + 1) hnext * ‖old.normal (j + 1) hnext‖ <
          base.successiveAwaySeparation j hj hnext / 4 := by
    intro j hj hnext
    have hleft :
        halfWidth j hj * ‖old.normal j hj‖ ≤
          old.halfWidth j hj * ‖old.normal j hj‖ :=
      mul_le_mul_of_nonneg_right (le_of_lt (halfWidth_lt_old j hj)) (norm_nonneg _)
    have hright :
        halfWidth (j + 1) hnext * ‖old.normal (j + 1) hnext‖ ≤
          old.halfWidth (j + 1) hnext * ‖old.normal (j + 1) hnext‖ :=
      mul_le_mul_of_nonneg_right (le_of_lt (halfWidth_lt_old (j + 1) hnext))
        (norm_nonneg _)
    calc
      halfWidth j hj * ‖old.normal j hj‖ +
          halfWidth (j + 1) hnext * ‖old.normal (j + 1) hnext‖
          ≤
        old.halfWidth j hj * ‖old.normal j hj‖ +
          old.halfWidth (j + 1) hnext * ‖old.normal (j + 1) hnext‖ :=
        add_le_add hleft hright
      _ < base.successiveAwaySeparation j hj hnext / 4 :=
        base.successive_halfWidth_normal_sum_lt_away_quarter j hj hnext
  have source_tube_disjoint_endpoint :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length), j ≠ 0 →
        Disjoint (tube j hj) (Metric.ball γ.source r₀) := by
    intro j hj hj0
    apply endpointRefinement_tube_disjoint_ball
    · exact sourceSeparation_pos j hj hj0
    · intro c hc z hz
      exact (Classical.choose_spec (sourceSeparationExists j hj hj0)).2 c hc z hz
    · exact halfWidth_mul_normal_norm_lt_source_half j hj hj0
  have target_tube_disjoint_endpoint :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length), j ≠ jlast →
        Disjoint (tube j hj) (Metric.ball γ.target r₁) := by
    intro j hj hjlast
    apply endpointRefinement_tube_disjoint_ball
    · exact targetSeparation_pos j hj hjlast
    · intro c hc z hz
      exact (Classical.choose_spec (targetSeparationExists j hj hjlast)).2 c hc z hz
    · exact halfWidth_mul_normal_norm_lt_target_half j hj hjlast
  let orientedTubes :
      PolygonalArcCollarOrientedSeparatedTubeData γ controlRadii middleSegments
        forbiddenMargins :=
    { lowerParam := old.lowerParam
      upperParam := old.upperParam
      halfWidth := halfWidth
      normal := old.normal
      tube := tube
      leftHalf := leftHalf
      rightHalf := rightHalf
      lowerParam_pos := old.lowerParam_pos
      lowerParam_lt_left_parameter := old.lowerParam_lt_left_parameter
      right_parameter_lt_upperParam := old.right_parameter_lt_upperParam
      upperParam_lt_one := old.upperParam_lt_one
      halfWidth_pos := halfWidth_pos
      normal_orthogonal := old.normal_orthogonal
      normal_norm_eq_segment_length := old.normal_norm_eq_segment_length
      halfWidth_mul_normal_norm_lt_eta := halfWidth_mul_normal_norm_lt_eta
      halfWidth_mul_normal_norm_lt_margin_quarter :=
        halfWidth_mul_normal_norm_lt_margin_quarter
      lower_parameter_slack_mul_segment_length_lt_margin_quarter :=
        old.lower_parameter_slack_mul_segment_length_lt_margin_quarter
      upper_parameter_slack_mul_segment_length_lt_margin_quarter :=
        old.upper_parameter_slack_mul_segment_length_lt_margin_quarter
      tube_eq := by
        intro j hj
        rfl
      leftHalf_eq := by
        intro j hj
        rfl
      rightHalf_eq := by
        intro j hj
        rfl
      middle_subset_tube := middle_subset_tube
      leftHalf_subset_tube := leftHalf_subset_tube
      rightHalf_subset_tube := rightHalf_subset_tube
      tube_subset_eta_neighborhood := tube_subset_eta_neighborhood
      tube_point_close_to_middle := tube_point_close_to_middle
      tube_disjoint_nonadjacent_segments := tube_disjoint_nonadjacent_segments
      tube_disjoint_nonincident_control_disks := tube_disjoint_nonincident_control_disks
      tube_disjoint_nonadjacent_middle_cores := tube_disjoint_nonadjacent_middle_cores
      tube_disjoint_nonadjacent_tubes := tube_disjoint_nonadjacent_tubes
      normal_eq_positive_quarter_turn :=
        base.orientedTubes.normal_eq_positive_quarter_turn }
  let compatibleTubes :
      PolygonalArcCollarCompatibleOrientedTubeData γ controlRadii middleSegments
        forbiddenMargins :=
    { orientedTubes := orientedTubes
      initialConeBound := initialConeBound
      terminalConeBound := terminalConeBound
      initialConeBound_pos := initialConeBound_pos
      terminalConeBound_pos := terminalConeBound_pos
      initial_halfWidth_lt_cone_mul_lowerParam := by
        intro j hj
        simpa [orientedTubes] using halfWidth_lt_initialCone_mul_lowerParam j hj
      terminal_halfWidth_lt_cone_mul_one_sub_upperParam := by
        intro j hj
        simpa [orientedTubes] using
          halfWidth_lt_terminalCone_mul_one_sub_upperParam j hj
      initial_signed_cone_disjoint_previous_segment := by
        intro j hj hprev
        simpa [orientedTubes] using
          initial_signed_cone_disjoint_previous_segment j hj hprev
      terminal_signed_cone_disjoint_next_segment := by
        intro j hj hnext
        simpa [orientedTubes] using
          terminal_signed_cone_disjoint_next_segment j hj hnext
      successive_positive_negative_cones_disjoint := by
        intro j hj hnext
        exact endpointRefinement_successive_positive_negative_cones_disjoint
          γ controlRadii middleSegments forbiddenMargins base initialConeBound
            terminalConeBound initialConeBound_le_base terminalConeBound_le_base j hj hnext
      successive_negative_positive_cones_disjoint := by
        intro j hj hnext
        exact endpointRefinement_successive_negative_positive_cones_disjoint
          γ controlRadii middleSegments forbiddenMargins base initialConeBound
            terminalConeBound initialConeBound_le_base terminalConeBound_le_base j hj hnext
      initialAwaySeparation := base.initialAwaySeparation
      terminalAwaySeparation := base.terminalAwaySeparation
      successiveAwaySeparation := base.successiveAwaySeparation
      initialAwaySeparation_pos := base.initialAwaySeparation_pos
      terminalAwaySeparation_pos := base.terminalAwaySeparation_pos
      successiveAwaySeparation_pos := base.successiveAwaySeparation_pos
      initial_centerline_previous_segment_away :=
        base.initial_centerline_previous_segment_away
      terminal_centerline_next_segment_away :=
        base.terminal_centerline_next_segment_away
      successive_centerlines_away := base.successive_centerlines_away
      initial_halfWidth_mul_normal_norm_lt_away_quarter := by
        intro j hj hprev
        simpa [orientedTubes] using
          initial_halfWidth_mul_normal_norm_lt_away_quarter j hj hprev
      terminal_halfWidth_mul_normal_norm_lt_away_quarter := by
        intro j hj hnext
        simpa [orientedTubes] using
          terminal_halfWidth_mul_normal_norm_lt_away_quarter j hj hnext
      successive_halfWidth_normal_sum_lt_away_quarter := by
        intro j hj hnext
        simpa [orientedTubes] using
          successive_halfWidth_normal_sum_lt_away_quarter j hj hnext }
  refine ⟨compatibleTubes, ?_, ?_, ?_, ?_⟩
  · have hle :
        initialConeBound 0 hfirst ≤ K₀ / 2 := by
      dsimp [initialConeBound]
      simp
    have hhalf : K₀ / 2 < K₀ := by nlinarith
    exact lt_of_le_of_lt hle hhalf
  · have hle :
        terminalConeBound jlast hlast ≤ K₁ / 2 := by
      dsimp [terminalConeBound]
      simp
    have hhalf : K₁ / 2 < K₁ := by nlinarith
    exact lt_of_le_of_lt hle hhalf
  · intro j hj hj0
    simpa [compatibleTubes, orientedTubes] using
      source_tube_disjoint_endpoint j hj hj0
  · intro j hj hjlast
    simpa [compatibleTubes, orientedTubes] using
      target_tube_disjoint_endpoint j hj hjlast
