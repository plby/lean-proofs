import Util.IncidenceGeometry.PolygonalArcCollarCompatibleOrientedTubeData
import Util.IncidenceGeometry.PolygonalArcAdjacentOutwardDirectionsNotSameRay
import Util.IncidenceGeometry.PlanarRot90ConeAvoidsRay
import Util.IncidenceGeometry.PlanarRot90SameSideConesDisjoint
import Util.IncidenceGeometry.PositiveSeparation

open Classical
noncomputable section

private lemma collar_segmentEndpoints_ne (γ : PolygonalArc) {η : ℝ}
    (controlRadii : PolygonalArcCollarControlRadii γ η) (j : ℕ)
    (hj : j + 1 < γ.vertices.length) : γ.vertices[j] ≠ γ.vertices[j + 1] := by
  have hsum := controlRadii.adjacent_radii_sum_lt (j := j) hj
  have hleft := controlRadii.radius_pos ⟨j, Nat.lt_of_succ_lt hj⟩
  have hright := controlRadii.radius_pos ⟨j + 1, hj⟩
  apply dist_pos.mp
  nlinarith

private lemma collar_initialConeAvoidsPreviousRay (γ : PolygonalArc) {η : ℝ}
    (controlRadii : PolygonalArcCollarControlRadii γ η) (j : ℕ)
    (hj : j + 1 < γ.vertices.length) (hprev : 0 < j) :
    ∃ κ : ℝ, 0 < κ ∧
      ∀ c t s : ℝ, 0 ≤ c → 0 < t → s ≠ 0 → |s| < κ * t →
        c • (γ.vertices[j - 1] - γ.vertices[j]) ≠
          t • (γ.vertices[j + 1] - γ.vertices[j]) +
            s • PlanarRot90 (γ.vertices[j + 1] - γ.vertices[j]) := by
  apply PlanarRot90ConeAvoidsRay
  · exact sub_ne_zero.mpr (collar_segmentEndpoints_ne γ controlRadii j hj).symm
  · exact (PolygonalArcAdjacentOutwardDirectionsNotSameRay γ hprev hj).1

private lemma collar_terminalConeAvoidsNextRay (γ : PolygonalArc) {η : ℝ}
    (controlRadii : PolygonalArcCollarControlRadii γ η) (j : ℕ)
    (hj : j + 1 < γ.vertices.length)
    (hnext : (j + 1) + 1 < γ.vertices.length) :
    ∃ κ : ℝ, 0 < κ ∧
      ∀ c t s : ℝ, 0 ≤ c → 0 < t → s ≠ 0 → |s| < κ * t →
        c • (γ.vertices[j + 2] - γ.vertices[j + 1]) ≠
          t • (γ.vertices[j] - γ.vertices[j + 1]) +
            s • PlanarRot90 (γ.vertices[j] - γ.vertices[j + 1]) := by
  have hnot :
      ¬ ∃ a : ℝ, 0 < a ∧
        γ.vertices[j + 2] - γ.vertices[j + 1] =
          a • (γ.vertices[j] - γ.vertices[j + 1]) := by
    simpa [Nat.add_assoc] using
      (PolygonalArcAdjacentOutwardDirectionsNotSameRay γ
        (i := j + 1) (Nat.succ_pos j) hnext).2
  apply PlanarRot90ConeAvoidsRay
  · exact sub_ne_zero.mpr (collar_segmentEndpoints_ne γ controlRadii j hj)
  · exact hnot

private lemma collar_successiveOutwardConesDisjoint (γ : PolygonalArc) {η : ℝ}
    (controlRadii : PolygonalArcCollarControlRadii γ η) (j : ℕ)
    (hj : j + 1 < γ.vertices.length)
    (hnext : (j + 1) + 1 < γ.vertices.length) :
    ∃ κ : ℝ, 0 < κ ∧
      ∀ a c b r : ℝ, 0 < a → 0 < c → 0 < b * r →
        |b| < κ * a → |r| < κ * c →
          a • (γ.vertices[j] - γ.vertices[j + 1]) +
              b • PlanarRot90 (γ.vertices[j] - γ.vertices[j + 1]) ≠
            c • (γ.vertices[j + 2] - γ.vertices[j + 1]) +
              r • PlanarRot90 (γ.vertices[j + 2] - γ.vertices[j + 1]) := by
  have hnot :
      ¬ ∃ A : ℝ, 0 < A ∧
        γ.vertices[j + 2] - γ.vertices[j + 1] =
          A • (γ.vertices[j] - γ.vertices[j + 1]) := by
    simpa [Nat.add_assoc] using
      (PolygonalArcAdjacentOutwardDirectionsNotSameRay γ
        (i := j + 1) (Nat.succ_pos j) hnext).2
  apply PlanarRot90SameSideConesDisjoint
  · exact sub_ne_zero.mpr (collar_segmentEndpoints_ne γ controlRadii j hj)
  · exact sub_ne_zero.mpr
      (collar_segmentEndpoints_ne γ controlRadii (j + 1) hnext).symm
  · exact hnot

private lemma collar_initialCenterline_disjoint_previous (γ : PolygonalArc) {η : ℝ}
    (controlRadii : PolygonalArcCollarControlRadii γ η) (j : ℕ)
    (hj : j + 1 < γ.vertices.length) (hprev : 0 < j) (L : ℝ) (hL : 0 < L) :
    Disjoint
      ((AffineMap.lineMap γ.vertices[j] γ.vertices[j + 1]) '' Set.Icc L (1 : ℝ))
      (segment ℝ γ.vertices[j - 1] γ.vertices[j]) := by
  rw [Set.disjoint_left]
  intro x hxA hxPrev
  rcases hxA with ⟨t, ht, rfl⟩
  have hCurrent :
      AffineMap.lineMap γ.vertices[j] γ.vertices[j + 1] t ∈
        segment ℝ γ.vertices[j] γ.vertices[j + 1] := by
    rw [segment_eq_image_lineMap]
    exact ⟨t, ⟨le_trans (le_of_lt hL) ht.1, ht.2⟩, rfl⟩
  have hprevSeg : (j - 1) + 1 < γ.vertices.length := by
    have hj' : j < γ.vertices.length := Nat.lt_of_succ_lt hj
    simpa [Nat.sub_add_cancel (Nat.succ_le_of_lt hprev)] using hj'
  have hlt : j - 1 < j := Nat.sub_lt hprev Nat.zero_lt_one
  have hinter :
      segment ℝ γ.vertices[j - 1] γ.vertices[j] ∩
          segment ℝ γ.vertices[j] γ.vertices[j + 1] =
        ({γ.vertices[j]} : Set (EuclideanSpace ℝ (Fin 2))) := by
    have hraw := γ.segment_intersections (i := j - 1) (j := j) hprevSeg hj hlt
    simpa [Nat.sub_add_cancel (Nat.succ_le_of_lt hprev)] using hraw
  have hxVertex :
      AffineMap.lineMap γ.vertices[j] γ.vertices[j + 1] t = γ.vertices[j] := by
    have hxInter := Set.mem_inter hxPrev hCurrent
    rw [hinter] at hxInter
    exact Set.mem_singleton_iff.mp hxInter
  have ht0 : t = 0 := by
    apply AffineMap.lineMap_injective (k := ℝ)
      (collar_segmentEndpoints_ne γ controlRadii j hj)
    rw [AffineMap.lineMap_apply_zero]
    exact hxVertex
  linarith [ht.1]

private lemma collar_terminalCenterline_disjoint_next (γ : PolygonalArc) {η : ℝ}
    (controlRadii : PolygonalArcCollarControlRadii γ η) (j : ℕ)
    (hj : j + 1 < γ.vertices.length)
    (hnext : (j + 1) + 1 < γ.vertices.length) (R : ℝ) (hR : R < 1) :
    Disjoint
      ((AffineMap.lineMap γ.vertices[j] γ.vertices[j + 1]) '' Set.Icc (0 : ℝ) R)
      (segment ℝ γ.vertices[j + 1] γ.vertices[j + 2]) := by
  rw [Set.disjoint_left]
  intro x hxA hxNext
  rcases hxA with ⟨t, ht, rfl⟩
  have hCurrent :
      AffineMap.lineMap γ.vertices[j] γ.vertices[j + 1] t ∈
        segment ℝ γ.vertices[j] γ.vertices[j + 1] := by
    rw [segment_eq_image_lineMap]
    exact ⟨t, ⟨ht.1, le_trans ht.2 (le_of_lt hR)⟩, rfl⟩
  have hinter :
      segment ℝ γ.vertices[j] γ.vertices[j + 1] ∩
          segment ℝ γ.vertices[j + 1] γ.vertices[j + 2] =
        ({γ.vertices[j + 1]} : Set (EuclideanSpace ℝ (Fin 2))) := by
    have hraw :=
      γ.segment_intersections (i := j) (j := j + 1) hj hnext (Nat.lt_succ_self j)
    simpa using hraw
  have hxVertex :
      AffineMap.lineMap γ.vertices[j] γ.vertices[j + 1] t = γ.vertices[j + 1] := by
    have hxInter := Set.mem_inter hCurrent hxNext
    rw [hinter] at hxInter
    exact Set.mem_singleton_iff.mp hxInter
  have ht1 : t = 1 := by
    apply AffineMap.lineMap_injective (k := ℝ)
      (collar_segmentEndpoints_ne γ controlRadii j hj)
    rw [AffineMap.lineMap_apply_one]
    exact hxVertex
  linarith [ht.2]

private lemma collar_successiveCenterlines_disjoint (γ : PolygonalArc) {η : ℝ}
    (controlRadii : PolygonalArcCollarControlRadii γ η) (j : ℕ)
    (hj : j + 1 < γ.vertices.length)
    (hnext : (j + 1) + 1 < γ.vertices.length) (R L : ℝ)
    (hR : R < 1) (hL : 0 < L) :
    Disjoint
      ((AffineMap.lineMap γ.vertices[j] γ.vertices[j + 1]) '' Set.Icc (0 : ℝ) R)
      ((AffineMap.lineMap γ.vertices[j + 1] γ.vertices[j + 2]) '' Set.Icc L (1 : ℝ)) := by
  rw [Set.disjoint_left]
  intro x hxA hxB
  rcases hxA with ⟨t, ht, rfl⟩
  rcases hxB with ⟨u, hu, hxu⟩
  have hCurrent :
      AffineMap.lineMap γ.vertices[j] γ.vertices[j + 1] t ∈
        segment ℝ γ.vertices[j] γ.vertices[j + 1] := by
    rw [segment_eq_image_lineMap]
    exact ⟨t, ⟨ht.1, le_trans ht.2 (le_of_lt hR)⟩, rfl⟩
  have hNext :
      AffineMap.lineMap γ.vertices[j] γ.vertices[j + 1] t ∈
        segment ℝ γ.vertices[j + 1] γ.vertices[j + 2] := by
    rw [← hxu, segment_eq_image_lineMap]
    exact ⟨u, ⟨le_trans (le_of_lt hL) hu.1, hu.2⟩, rfl⟩
  have hinter :
      segment ℝ γ.vertices[j] γ.vertices[j + 1] ∩
          segment ℝ γ.vertices[j + 1] γ.vertices[j + 2] =
        ({γ.vertices[j + 1]} : Set (EuclideanSpace ℝ (Fin 2))) := by
    have hraw :=
      γ.segment_intersections (i := j) (j := j + 1) hj hnext (Nat.lt_succ_self j)
    simpa using hraw
  have hxVertex :
      AffineMap.lineMap γ.vertices[j] γ.vertices[j + 1] t = γ.vertices[j + 1] := by
    have hxInter := Set.mem_inter hCurrent hNext
    rw [hinter] at hxInter
    exact Set.mem_singleton_iff.mp hxInter
  have ht1 : t = 1 := by
    apply AffineMap.lineMap_injective (k := ℝ)
      (collar_segmentEndpoints_ne γ controlRadii j hj)
    rw [AffineMap.lineMap_apply_one]
    exact hxVertex
  linarith [ht.2]

private lemma collar_dist_lineMap_lineMap
    (A B : EuclideanSpace ℝ (Fin 2)) (c₁ c₂ : ℝ) :
    dist (AffineMap.lineMap A B c₁) (AffineMap.lineMap A B c₂) =
      dist c₁ c₂ * dist A B := by
  rw [dist_eq_norm, Real.dist_eq, dist_eq_norm]
  have hvec :
      AffineMap.lineMap A B c₁ - AffineMap.lineMap A B c₂ =
        (c₁ - c₂) • (B - A) := by
    apply PiLp.ext
    intro k
    simp [AffineMap.lineMap_apply_module]
    ring
  rw [hvec, norm_smul, Real.norm_eq_abs]
  have hnorm : ‖B - A‖ = ‖A - B‖ := by
    rw [show B - A = -(A - B) by abel, norm_neg]
  rw [hnorm]

private lemma collar_real_dist_to_Icc_of_mem_Ioo_expansion
    {L R ε t : ℝ} (hε : 0 < ε) (hLR : L < R)
    (ht : t ∈ Set.Ioo (L - ε) (R + ε)) :
    ∃ u : ℝ, u ∈ Set.Icc L R ∧ dist t u < ε := by
  by_cases htL : t < L
  · refine ⟨L, ⟨le_rfl, le_of_lt hLR⟩, ?_⟩
    rw [Real.dist_eq, abs_of_neg (sub_neg.mpr htL)]
    linarith [ht.1]
  · by_cases htR : t ≤ R
    · refine ⟨t, ⟨le_of_not_gt htL, htR⟩, ?_⟩
      simpa using hε
    · have hRt : R < t := lt_of_not_ge htR
      refine ⟨R, ⟨le_of_lt hLR, le_rfl⟩, ?_⟩
      rw [Real.dist_eq, abs_of_pos (sub_pos.mpr hRt)]
      linarith [ht.2]

private lemma collar_lineMap_sub_left
    (A B : EuclideanSpace ℝ (Fin 2)) (t : ℝ) :
    AffineMap.lineMap A B t - A = t • (B - A) := by
  apply PiLp.ext
  intro k
  simp [AffineMap.lineMap_apply_module]
  ring

private lemma collar_lineMap_sub_right
    (A B : EuclideanSpace ℝ (Fin 2)) (t : ℝ) :
    AffineMap.lineMap A B t - B = (1 - t) • (A - B) := by
  apply PiLp.ext
  intro k
  simp [AffineMap.lineMap_apply_module]
  ring

private lemma collar_lineMap_add_sub_left
    (A B n : EuclideanSpace ℝ (Fin 2)) (t s : ℝ) :
    AffineMap.lineMap A B t + s • n - A = t • (B - A) + s • n := by
  apply PiLp.ext
  intro k
  simp [AffineMap.lineMap_apply_module, sub_eq_add_neg]
  ring

private lemma collar_lineMap_add_sub_right
    (A B n : EuclideanSpace ℝ (Fin 2)) (t s : ℝ) :
    AffineMap.lineMap A B t + s • n - B = (1 - t) • (A - B) + s • n := by
  apply PiLp.ext
  intro k
  simp [AffineMap.lineMap_apply_module, sub_eq_add_neg]
  ring

private lemma collar_PlanarRot90_neg (v : EuclideanSpace ℝ (Fin 2)) :
    PlanarRot90 (-v) = -PlanarRot90 v := by
  apply PiLp.ext
  intro k
  fin_cases k <;> simp [PlanarRot90]

private lemma collar_scaled_eighth_mul_lt_quarter {D μ w : ℝ}
    (hD : 0 < D) (hμ : 0 < μ) (hw : w ≤ μ / (8 * (D + 1))) :
    w * D < μ / 4 := by
  have hDnonneg : 0 ≤ D := le_of_lt hD
  have hdenpos : 0 < 8 * (D + 1) := by positivity
  have hscaled : μ / (8 * (D + 1)) * D < μ / 4 := by
    have hden_ne : 8 * (D + 1) ≠ 0 := ne_of_gt hdenpos
    field_simp [hden_ne]
    nlinarith
  exact (mul_le_mul_of_nonneg_right hw hDnonneg).trans_lt hscaled

private lemma collar_scaled_sixteenth_mul_lt_eighth {D μ w : ℝ}
    (hD : 0 < D) (hμ : 0 < μ) (hw : w ≤ μ / (16 * (D + 1))) :
    w * D < μ / 8 := by
  have hDnonneg : 0 ≤ D := le_of_lt hD
  have hdenpos : 0 < 16 * (D + 1) := by positivity
  have hscaled : μ / (16 * (D + 1)) * D < μ / 8 := by
    have hden_ne : 16 * (D + 1) ≠ 0 := ne_of_gt hdenpos
    field_simp [hden_ne]
    nlinarith
  exact (mul_le_mul_of_nonneg_right hw hDnonneg).trans_lt hscaled

private lemma collar_scaled_quarter_mul_lt {D η w : ℝ}
    (hD : 0 < D) (hη : 0 < η) (hw : w ≤ η / (4 * (D + 1))) :
    w * D < η := by
  have hDnonneg : 0 ≤ D := le_of_lt hD
  have hdenpos : 0 < 4 * (D + 1) := by positivity
  have hscaled : η / (4 * (D + 1)) * D < η := by
    have hden_ne : 4 * (D + 1) ≠ 0 := ne_of_gt hdenpos
    field_simp [hden_ne]
    nlinarith
  exact (mul_le_mul_of_nonneg_right hw hDnonneg).trans_lt hscaled

private lemma collar_coneBound_mono
    (small large : ℝ) (hsmall : small ≤ large) (P : ℝ → ℝ → ℝ → Prop)
    (hlarge : ∀ c t s : ℝ, 0 ≤ c → 0 < t → s ≠ 0 →
      |s| < large * t → P c t s) :
    ∀ c t s : ℝ, 0 ≤ c → 0 < t → s ≠ 0 → |s| < small * t → P c t s := by
  intro c t s hc ht hs hlt
  exact hlarge c t s hc ht hs
    (hlt.trans_le (mul_le_mul_of_nonneg_right hsmall (le_of_lt ht)))

private lemma collar_twoConeBounds_mono
    (small₁ small₂ large : ℝ) (hsmall₁ : small₁ ≤ large) (hsmall₂ : small₂ ≤ large)
    (P : ℝ → ℝ → ℝ → ℝ → Prop)
    (hlarge : ∀ a c b r : ℝ, 0 < a → 0 < c → 0 < b * r →
      |b| < large * a → |r| < large * c → P a c b r) :
    ∀ a c b r : ℝ, 0 < a → 0 < c → 0 < b * r →
      |b| < small₁ * a → |r| < small₂ * c → P a c b r := by
  intro a c b r ha hc hbr hb hr
  exact hlarge a c b r ha hc hbr
    (hb.trans_le (mul_le_mul_of_nonneg_right hsmall₁ (le_of_lt ha)))
    (hr.trans_le (mul_le_mul_of_nonneg_right hsmall₂ (le_of_lt hc)))

private lemma collar_normal_orthogonal (A B : EuclideanSpace ℝ (Fin 2)) :
    inner ℝ (B - A) (PlanarRot90 (B - A)) = 0 :=
  PlanarRot90Orthogonal (B - A)

private lemma collar_normal_norm_eq_segment_length
    (A B : EuclideanSpace ℝ (Fin 2)) : ‖PlanarRot90 (B - A)‖ = dist A B := by
  calc
    ‖PlanarRot90 (B - A)‖ = ‖B - A‖ := PlanarRot90Norm (B - A)
    _ = ‖A - B‖ := by rw [show B - A = -(A - B) by abel, norm_neg]
    _ = dist A B := by rw [dist_eq_norm]

private lemma collar_initialAwayExists (γ : PolygonalArc) {η : ℝ}
    (controlRadii : PolygonalArcCollarControlRadii γ η) (j : ℕ)
    (hj : j + 1 < γ.vertices.length) (hprev : 0 < j) (L : ℝ)
    (hL : 0 < L) (hLone : L ≤ 1) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ t : ℝ, t ∈ Set.Icc L (1 : ℝ) →
        ∀ q, q ∈ segment ℝ γ.vertices[j - 1] γ.vertices[j] →
          δ ≤ dist (AffineMap.lineMap γ.vertices[j] γ.vertices[j + 1] t) q := by
  let A := (AffineMap.lineMap γ.vertices[j] γ.vertices[j + 1]) '' Set.Icc L (1 : ℝ)
  let B := segment ℝ γ.vertices[j - 1] γ.vertices[j]
  have hAne : A.Nonempty :=
    ⟨AffineMap.lineMap γ.vertices[j] γ.vertices[j + 1] L,
      ⟨L, ⟨le_rfl, hLone⟩, rfl⟩⟩
  have hBne : B.Nonempty := ⟨γ.vertices[j - 1], by simp [B, left_mem_segment]⟩
  have hAc : IsCompact A := by
    dsimp [A]
    exact isCompact_Icc.image AffineMap.lineMap_continuous
  have hBc : IsCompact B := by
    dsimp [B]
    rw [segment_eq_image_lineMap]
    exact isCompact_Icc.image AffineMap.lineMap_continuous
  have hdisj : Disjoint A B := by
    exact collar_initialCenterline_disjoint_previous γ controlRadii j hj hprev L hL
  obtain ⟨δ, hδpos, hδ⟩ :=
    PositiveSeparation (A := A) (B := B) hAne hBne hAc hBc hdisj
  refine ⟨δ, hδpos, ?_⟩
  intro t ht q hq
  exact hδ _ ⟨t, ht, rfl⟩ q hq

private lemma collar_terminalAwayExists (γ : PolygonalArc) {η : ℝ}
    (controlRadii : PolygonalArcCollarControlRadii γ η) (j : ℕ)
    (hj : j + 1 < γ.vertices.length)
    (hnext : (j + 1) + 1 < γ.vertices.length) (R : ℝ)
    (hRzero : 0 ≤ R) (hR : R < 1) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) R →
        ∀ q, q ∈ segment ℝ γ.vertices[j + 1] γ.vertices[j + 2] →
          δ ≤ dist (AffineMap.lineMap γ.vertices[j] γ.vertices[j + 1] t) q := by
  let A := (AffineMap.lineMap γ.vertices[j] γ.vertices[j + 1]) '' Set.Icc (0 : ℝ) R
  let B := segment ℝ γ.vertices[j + 1] γ.vertices[j + 2]
  have hAne : A.Nonempty :=
    ⟨AffineMap.lineMap γ.vertices[j] γ.vertices[j + 1] 0,
      ⟨0, ⟨le_rfl, hRzero⟩, rfl⟩⟩
  have hBne : B.Nonempty := ⟨γ.vertices[j + 1], by simp [B, left_mem_segment]⟩
  have hAc : IsCompact A := by
    dsimp [A]
    exact isCompact_Icc.image AffineMap.lineMap_continuous
  have hBc : IsCompact B := by
    dsimp [B]
    rw [segment_eq_image_lineMap]
    exact isCompact_Icc.image AffineMap.lineMap_continuous
  have hdisj : Disjoint A B := by
    exact collar_terminalCenterline_disjoint_next γ controlRadii j hj hnext R hR
  obtain ⟨δ, hδpos, hδ⟩ :=
    PositiveSeparation (A := A) (B := B) hAne hBne hAc hBc hdisj
  refine ⟨δ, hδpos, ?_⟩
  intro t ht q hq
  exact hδ _ ⟨t, ht, rfl⟩ q hq

private lemma collar_successiveAwayExists (γ : PolygonalArc) {η : ℝ}
    (controlRadii : PolygonalArcCollarControlRadii γ η) (j : ℕ)
    (hj : j + 1 < γ.vertices.length)
    (hnext : (j + 1) + 1 < γ.vertices.length) (R L : ℝ)
    (hRzero : 0 ≤ R) (hR : R < 1) (hL : 0 < L) (hLone : L ≤ 1) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) R →
        ∀ u : ℝ, u ∈ Set.Icc L (1 : ℝ) →
          δ ≤ dist (AffineMap.lineMap γ.vertices[j] γ.vertices[j + 1] t)
            (AffineMap.lineMap γ.vertices[j + 1] γ.vertices[j + 2] u) := by
  let A := (AffineMap.lineMap γ.vertices[j] γ.vertices[j + 1]) '' Set.Icc (0 : ℝ) R
  let B := (AffineMap.lineMap γ.vertices[j + 1] γ.vertices[j + 2]) '' Set.Icc L (1 : ℝ)
  have hAne : A.Nonempty :=
    ⟨AffineMap.lineMap γ.vertices[j] γ.vertices[j + 1] 0,
      ⟨0, ⟨le_rfl, hRzero⟩, rfl⟩⟩
  have hBne : B.Nonempty :=
    ⟨AffineMap.lineMap γ.vertices[j + 1] γ.vertices[j + 2] L,
      ⟨L, ⟨le_rfl, hLone⟩, rfl⟩⟩
  have hAc : IsCompact A := by
    dsimp [A]
    exact isCompact_Icc.image AffineMap.lineMap_continuous
  have hBc : IsCompact B := by
    dsimp [B]
    exact isCompact_Icc.image AffineMap.lineMap_continuous
  have hdisj : Disjoint A B := by
    exact collar_successiveCenterlines_disjoint γ controlRadii j hj hnext R L hR hL
  obtain ⟨δ, hδpos, hδ⟩ :=
    PositiveSeparation (A := A) (B := B) hAne hBne hAc hBc hdisj
  refine ⟨δ, hδpos, ?_⟩
  intro t ht u hu
  exact hδ _ ⟨t, ht, rfl⟩ _ ⟨u, hu, rfl⟩

private lemma collar_initialSignedConeDisjointPrevious
    (γ : PolygonalArc) (j : ℕ) (hj : j + 1 < γ.vertices.length)
    (hprev : 0 < j) (κ : ℝ)
    (hbound : ∀ c t s : ℝ, 0 ≤ c → 0 < t → s ≠ 0 → |s| < κ * t →
      c • (γ.vertices[j - 1] - γ.vertices[j]) ≠
        t • (γ.vertices[j + 1] - γ.vertices[j]) +
          s • PlanarRot90 (γ.vertices[j + 1] - γ.vertices[j])) :
    Disjoint
      {z | ∃ t : ℝ, t ∈ Set.Ioo (0 : ℝ) (1 : ℝ) ∧
        ∃ s : ℝ, s ≠ 0 ∧ |s| < κ * t ∧
          z = AffineMap.lineMap γ.vertices[j] γ.vertices[j + 1] t +
            s • PlanarRot90 (γ.vertices[j + 1] - γ.vertices[j])}
      (segment ℝ γ.vertices[j - 1] γ.vertices[j]) := by
  rw [Set.disjoint_left]
  intro z hzCone hzSeg
  rcases hzCone with ⟨t, ht, s, hs_ne, hs_lt, hz⟩
  rw [segment_eq_image_lineMap] at hzSeg
  rcases hzSeg with ⟨u, hu, hzPrev⟩
  have hPrevVec :
      z - γ.vertices[j] =
        (1 - u) • (γ.vertices[j - 1] - γ.vertices[j]) := by
    rw [← hzPrev]
    exact collar_lineMap_sub_right γ.vertices[j - 1] γ.vertices[j] u
  have hConeVec :
      z - γ.vertices[j] =
        t • (γ.vertices[j + 1] - γ.vertices[j]) +
          s • PlanarRot90 (γ.vertices[j + 1] - γ.vertices[j]) := by
    rw [hz]
    exact collar_lineMap_add_sub_left γ.vertices[j] γ.vertices[j + 1]
      (PlanarRot90 (γ.vertices[j + 1] - γ.vertices[j])) t s
  have heq :
      (1 - u) • (γ.vertices[j - 1] - γ.vertices[j]) =
        t • (γ.vertices[j + 1] - γ.vertices[j]) +
          s • PlanarRot90 (γ.vertices[j + 1] - γ.vertices[j]) :=
    hPrevVec.symm.trans hConeVec
  exact hbound (1 - u) t s (by nlinarith [hu.2]) ht.1 hs_ne hs_lt heq

private lemma collar_terminalSignedConeDisjointNext
    (γ : PolygonalArc) (j : ℕ) (hj : j + 1 < γ.vertices.length)
    (hnext : (j + 1) + 1 < γ.vertices.length) (κ : ℝ)
    (hbound : ∀ c t s : ℝ, 0 ≤ c → 0 < t → s ≠ 0 → |s| < κ * t →
      c • (γ.vertices[j + 2] - γ.vertices[j + 1]) ≠
        t • (γ.vertices[j] - γ.vertices[j + 1]) +
          s • PlanarRot90 (γ.vertices[j] - γ.vertices[j + 1])) :
    Disjoint
      {z | ∃ t : ℝ, t ∈ Set.Ioo (0 : ℝ) (1 : ℝ) ∧
        ∃ s : ℝ, s ≠ 0 ∧ |s| < κ * (1 - t) ∧
          z = AffineMap.lineMap γ.vertices[j] γ.vertices[j + 1] t +
            s • PlanarRot90 (γ.vertices[j + 1] - γ.vertices[j])}
      (segment ℝ γ.vertices[j + 1] γ.vertices[j + 2]) := by
  rw [Set.disjoint_left]
  intro z hzCone hzSeg
  rcases hzCone with ⟨t, ht, s, hs_ne, hs_lt, hz⟩
  rw [segment_eq_image_lineMap] at hzSeg
  rcases hzSeg with ⟨u, hu, hzNext⟩
  have hNextVec :
      z - γ.vertices[j + 1] =
        u • (γ.vertices[j + 2] - γ.vertices[j + 1]) := by
    rw [← hzNext]
    exact collar_lineMap_sub_left γ.vertices[j + 1] γ.vertices[j + 2] u
  have hConeVec :
      z - γ.vertices[j + 1] =
        (1 - t) • (γ.vertices[j] - γ.vertices[j + 1]) +
          s • PlanarRot90 (γ.vertices[j + 1] - γ.vertices[j]) := by
    rw [hz]
    exact collar_lineMap_add_sub_right γ.vertices[j] γ.vertices[j + 1]
      (PlanarRot90 (γ.vertices[j + 1] - γ.vertices[j])) t s
  have hrot :
      (-s) • PlanarRot90 (γ.vertices[j] - γ.vertices[j + 1]) =
        s • PlanarRot90 (γ.vertices[j + 1] - γ.vertices[j]) := by
    have hback : γ.vertices[j] - γ.vertices[j + 1] =
        -(γ.vertices[j + 1] - γ.vertices[j]) := by
      abel
    rw [hback, collar_PlanarRot90_neg]
    simp
  have heq :
      u • (γ.vertices[j + 2] - γ.vertices[j + 1]) =
        (1 - t) • (γ.vertices[j] - γ.vertices[j + 1]) +
          (-s) • PlanarRot90 (γ.vertices[j] - γ.vertices[j + 1]) := by
    have hConeVec' :
        z - γ.vertices[j + 1] =
          (1 - t) • (γ.vertices[j] - γ.vertices[j + 1]) +
            (-s) • PlanarRot90 (γ.vertices[j] - γ.vertices[j + 1]) :=
      hConeVec.trans (by rw [hrot])
    exact hNextVec.symm.trans hConeVec'
  exact hbound u (1 - t) (-s) hu.1 (by nlinarith [ht.2])
    (by simpa using neg_ne_zero.mpr hs_ne) (by simpa [abs_neg] using hs_lt) heq

private lemma collar_successivePositiveNegativeConesDisjoint
    (γ : PolygonalArc) (j : ℕ) (hj : j + 1 < γ.vertices.length)
    (hnext : (j + 1) + 1 < γ.vertices.length) (terminalBound initialBound : ℝ)
    (hbound : ∀ a c b r : ℝ, 0 < a → 0 < c → 0 < b * r →
      |b| < terminalBound * a → |r| < initialBound * c →
        a • (γ.vertices[j] - γ.vertices[j + 1]) +
            b • PlanarRot90 (γ.vertices[j] - γ.vertices[j + 1]) ≠
          c • (γ.vertices[j + 2] - γ.vertices[j + 1]) +
            r • PlanarRot90 (γ.vertices[j + 2] - γ.vertices[j + 1])) :
    Disjoint
      {z | ∃ t : ℝ, t ∈ Set.Ioo (0 : ℝ) (1 : ℝ) ∧
        ∃ s : ℝ, 0 < s ∧ s < terminalBound * (1 - t) ∧
          z = AffineMap.lineMap γ.vertices[j] γ.vertices[j + 1] t +
            s • PlanarRot90 (γ.vertices[j + 1] - γ.vertices[j])}
      {z | ∃ t : ℝ, t ∈ Set.Ioo (0 : ℝ) (1 : ℝ) ∧
        ∃ s : ℝ, s < 0 ∧ |s| < initialBound * t ∧
          z = AffineMap.lineMap γ.vertices[j + 1] γ.vertices[j + 2] t +
            s • PlanarRot90 (γ.vertices[j + 2] - γ.vertices[j + 1])} := by
  rw [Set.disjoint_left]
  intro z hzL hzR
  rcases hzL with ⟨t, ht, s, hs_pos, hs_lt, hzL⟩
  rcases hzR with ⟨u, hu, r, hr_neg, hr_lt, hzR⟩
  have hLeftVec :
      z - γ.vertices[j + 1] =
        (1 - t) • (γ.vertices[j] - γ.vertices[j + 1]) +
          s • PlanarRot90 (γ.vertices[j + 1] - γ.vertices[j]) := by
    rw [hzL]
    exact collar_lineMap_add_sub_right γ.vertices[j] γ.vertices[j + 1]
      (PlanarRot90 (γ.vertices[j + 1] - γ.vertices[j])) t s
  have hRightVec :
      z - γ.vertices[j + 1] =
        u • (γ.vertices[j + 2] - γ.vertices[j + 1]) +
          r • PlanarRot90 (γ.vertices[j + 2] - γ.vertices[j + 1]) := by
    rw [hzR]
    exact collar_lineMap_add_sub_left γ.vertices[j + 1] γ.vertices[j + 2]
      (PlanarRot90 (γ.vertices[j + 2] - γ.vertices[j + 1])) u r
  have hrot :
      (-s) • PlanarRot90 (γ.vertices[j] - γ.vertices[j + 1]) =
        s • PlanarRot90 (γ.vertices[j + 1] - γ.vertices[j]) := by
    have hback : γ.vertices[j] - γ.vertices[j + 1] =
        -(γ.vertices[j + 1] - γ.vertices[j]) := by
      abel
    rw [hback, collar_PlanarRot90_neg]
    simp
  have heq :
      (1 - t) • (γ.vertices[j] - γ.vertices[j + 1]) +
          (-s) • PlanarRot90 (γ.vertices[j] - γ.vertices[j + 1]) =
        u • (γ.vertices[j + 2] - γ.vertices[j + 1]) +
          r • PlanarRot90 (γ.vertices[j + 2] - γ.vertices[j + 1]) := by
    have hLeftVec' :
        z - γ.vertices[j + 1] =
          (1 - t) • (γ.vertices[j] - γ.vertices[j + 1]) +
            (-s) • PlanarRot90 (γ.vertices[j] - γ.vertices[j + 1]) :=
      hLeftVec.trans (by rw [hrot])
    exact hLeftVec'.symm.trans hRightVec
  exact hbound (1 - t) u (-s) r (by nlinarith [ht.2]) hu.1
    (by nlinarith [hs_pos, hr_neg])
    (by simpa [abs_neg, abs_of_pos hs_pos] using hs_lt) hr_lt heq

private lemma collar_successiveNegativePositiveConesDisjoint
    (γ : PolygonalArc) (j : ℕ) (hj : j + 1 < γ.vertices.length)
    (hnext : (j + 1) + 1 < γ.vertices.length) (terminalBound initialBound : ℝ)
    (hbound : ∀ a c b r : ℝ, 0 < a → 0 < c → 0 < b * r →
      |b| < terminalBound * a → |r| < initialBound * c →
        a • (γ.vertices[j] - γ.vertices[j + 1]) +
            b • PlanarRot90 (γ.vertices[j] - γ.vertices[j + 1]) ≠
          c • (γ.vertices[j + 2] - γ.vertices[j + 1]) +
            r • PlanarRot90 (γ.vertices[j + 2] - γ.vertices[j + 1])) :
    Disjoint
      {z | ∃ t : ℝ, t ∈ Set.Ioo (0 : ℝ) (1 : ℝ) ∧
        ∃ s : ℝ, s < 0 ∧ |s| < terminalBound * (1 - t) ∧
          z = AffineMap.lineMap γ.vertices[j] γ.vertices[j + 1] t +
            s • PlanarRot90 (γ.vertices[j + 1] - γ.vertices[j])}
      {z | ∃ t : ℝ, t ∈ Set.Ioo (0 : ℝ) (1 : ℝ) ∧
        ∃ s : ℝ, 0 < s ∧ s < initialBound * t ∧
          z = AffineMap.lineMap γ.vertices[j + 1] γ.vertices[j + 2] t +
            s • PlanarRot90 (γ.vertices[j + 2] - γ.vertices[j + 1])} := by
  rw [Set.disjoint_left]
  intro z hzL hzR
  rcases hzL with ⟨t, ht, s, hs_neg, hs_lt, hzL⟩
  rcases hzR with ⟨u, hu, r, hr_pos, hr_lt, hzR⟩
  have hLeftVec :
      z - γ.vertices[j + 1] =
        (1 - t) • (γ.vertices[j] - γ.vertices[j + 1]) +
          s • PlanarRot90 (γ.vertices[j + 1] - γ.vertices[j]) := by
    rw [hzL]
    exact collar_lineMap_add_sub_right γ.vertices[j] γ.vertices[j + 1]
      (PlanarRot90 (γ.vertices[j + 1] - γ.vertices[j])) t s
  have hRightVec :
      z - γ.vertices[j + 1] =
        u • (γ.vertices[j + 2] - γ.vertices[j + 1]) +
          r • PlanarRot90 (γ.vertices[j + 2] - γ.vertices[j + 1]) := by
    rw [hzR]
    exact collar_lineMap_add_sub_left γ.vertices[j + 1] γ.vertices[j + 2]
      (PlanarRot90 (γ.vertices[j + 2] - γ.vertices[j + 1])) u r
  have hrot :
      (-s) • PlanarRot90 (γ.vertices[j] - γ.vertices[j + 1]) =
        s • PlanarRot90 (γ.vertices[j + 1] - γ.vertices[j]) := by
    have hback : γ.vertices[j] - γ.vertices[j + 1] =
        -(γ.vertices[j + 1] - γ.vertices[j]) := by
      abel
    rw [hback, collar_PlanarRot90_neg]
    simp
  have heq :
      (1 - t) • (γ.vertices[j] - γ.vertices[j + 1]) +
          (-s) • PlanarRot90 (γ.vertices[j] - γ.vertices[j + 1]) =
        u • (γ.vertices[j + 2] - γ.vertices[j + 1]) +
          r • PlanarRot90 (γ.vertices[j + 2] - γ.vertices[j + 1]) := by
    have hLeftVec' :
        z - γ.vertices[j + 1] =
          (1 - t) • (γ.vertices[j] - γ.vertices[j + 1]) +
            (-s) • PlanarRot90 (γ.vertices[j] - γ.vertices[j + 1]) :=
      hLeftVec.trans (by rw [hrot])
    exact hLeftVec'.symm.trans hRightVec
  exact hbound (1 - t) u (-s) r (by nlinarith [ht.2]) hu.1
    (by nlinarith [hs_neg, hr_pos]) (by simpa [abs_neg] using hs_lt)
    (by simpa [abs_of_pos hr_pos] using hr_lt) heq

private lemma collar_tubesDisjointOfCloseToSeparatedMiddle
    (γ : PolygonalArc) {η : ℝ}
    (controlRadii : PolygonalArcCollarControlRadii γ η)
    (middleSegments : PolygonalArcCollarMiddleSegmentData γ controlRadii)
    (forbiddenMargins :
      PolygonalArcCollarMiddleForbiddenMargins γ controlRadii middleSegments)
    (tube : (j : ℕ) → j + 1 < γ.vertices.length →
      Set (EuclideanSpace ℝ (Fin 2)))
    (tube_point_close_to_middle :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length),
        ∀ z ∈ tube j hj, ∃ p ∈ middleSegments.middle j hj,
          dist z p < forbiddenMargins.margin j hj / 2)
    (j : ℕ) (hj : j + 1 < γ.vertices.length)
    (k : ℕ) (hk : k + 1 < γ.vertices.length)
    (hgap : j + 1 < k ∨ k + 1 < j) :
    Disjoint (tube j hj) (tube k hk) := by
  rw [Set.disjoint_left]
  intro z hzj hzk
  obtain ⟨p, hpM, hpClose⟩ := tube_point_close_to_middle j hj z hzj
  obtain ⟨q, hqM, hqClose⟩ := tube_point_close_to_middle k hk z hzk
  have hgap_sym : k + 1 < j ∨ j + 1 < k := by
    cases hgap with
    | inl h => exact Or.inr h
    | inr h => exact Or.inl h
  have hmj :=
    forbiddenMargins.middle_core_separation j hj k hk hgap p hpM q hqM
  have hmk :=
    forbiddenMargins.middle_core_separation k hk j hj hgap_sym q hqM p hpM
  have hpClose' : dist p z < forbiddenMargins.margin j hj / 2 := by
    simpa [dist_comm] using hpClose
  have hmk' : forbiddenMargins.margin k hk ≤ dist p q := by
    simpa [dist_comm] using hmk
  have htri : dist p q ≤ dist p z + dist z q := dist_triangle p z q
  have hsum :
      dist p q <
        forbiddenMargins.margin j hj / 2 + forbiddenMargins.margin k hk / 2 :=
    lt_of_le_of_lt htri (add_lt_add hpClose' hqClose)
  nlinarith [forbiddenMargins.margin_pos j hj,
    forbiddenMargins.margin_pos k hk, hmj, hmk', hsum]

private lemma collar_tubeDisjointNonadjacentSegmentOfCloseToMiddle
    (γ : PolygonalArc) {η : ℝ}
    (controlRadii : PolygonalArcCollarControlRadii γ η)
    (middleSegments : PolygonalArcCollarMiddleSegmentData γ controlRadii)
    (forbiddenMargins :
      PolygonalArcCollarMiddleForbiddenMargins γ controlRadii middleSegments)
    (tube : (j : ℕ) → j + 1 < γ.vertices.length →
      Set (EuclideanSpace ℝ (Fin 2)))
    (tube_point_close_to_middle :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length),
        ∀ z ∈ tube j hj, ∃ p ∈ middleSegments.middle j hj,
          dist z p < forbiddenMargins.margin j hj / 2)
    (j : ℕ) (hj : j + 1 < γ.vertices.length)
    (k : ℕ) (hk : k + 1 < γ.vertices.length)
    (hgap : j + 1 < k ∨ k + 1 < j) :
    Disjoint (tube j hj) (segment ℝ γ.vertices[k] γ.vertices[k + 1]) := by
  rw [Set.disjoint_left]
  intro z hzTube hzSeg
  obtain ⟨p, hpM, hpClose⟩ := tube_point_close_to_middle j hj z hzTube
  have hmargin :=
    forbiddenMargins.middle_segment_separation j hj k hk hgap p hpM z hzSeg
  have hpClose' : dist p z < forbiddenMargins.margin j hj / 2 := by
    simpa [dist_comm] using hpClose
  nlinarith [forbiddenMargins.margin_pos j hj, hmargin, hpClose']

private lemma collar_tubeDisjointNonincidentControlDiskOfCloseToMiddle
    (γ : PolygonalArc) {η : ℝ}
    (controlRadii : PolygonalArcCollarControlRadii γ η)
    (middleSegments : PolygonalArcCollarMiddleSegmentData γ controlRadii)
    (forbiddenMargins :
      PolygonalArcCollarMiddleForbiddenMargins γ controlRadii middleSegments)
    (tube : (j : ℕ) → j + 1 < γ.vertices.length →
      Set (EuclideanSpace ℝ (Fin 2)))
    (tube_point_close_to_middle :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length),
        ∀ z ∈ tube j hj, ∃ p ∈ middleSegments.middle j hj,
          dist z p < forbiddenMargins.margin j hj / 2)
    (j : ℕ) (hj : j + 1 < γ.vertices.length)
    (i : Fin γ.vertices.length) (hij : i.1 ≠ j) (hijs : i.1 ≠ j + 1) :
    Disjoint (tube j hj)
      (Metric.closedBall γ.vertices[i.1] (controlRadii.radius i)) := by
  rw [Set.disjoint_left]
  intro z hzTube hzDisk
  obtain ⟨p, hpM, hpClose⟩ := tube_point_close_to_middle j hj z hzTube
  have hmargin :=
    forbiddenMargins.middle_control_disk_separation j hj i hij hijs p hpM z hzDisk
  have hpClose' : dist p z < forbiddenMargins.margin j hj / 2 := by
    simpa [dist_comm] using hpClose
  nlinarith [forbiddenMargins.margin_pos j hj, hmargin, hpClose']

private lemma collar_tubePointCloseToMiddle
    (γ : PolygonalArc) {η : ℝ}
    (controlRadii : PolygonalArcCollarControlRadii γ η)
    (middleSegments : PolygonalArcCollarMiddleSegmentData γ controlRadii)
    (forbiddenMargins :
      PolygonalArcCollarMiddleForbiddenMargins γ controlRadii middleSegments)
    (j : ℕ) (hj : j + 1 < γ.vertices.length)
    (lowerParam upperParam paramSlack halfWidth : ℝ)
    (paramSlack_pos : 0 < paramSlack)
    (left_lt_right :
      controlRadii.radius ⟨j, Nat.lt_of_succ_lt hj⟩ /
          dist γ.vertices[j] γ.vertices[j + 1] <
        1 - controlRadii.radius ⟨j + 1, hj⟩ /
          dist γ.vertices[j] γ.vertices[j + 1])
    (lowerParam_eq : lowerParam =
      controlRadii.radius ⟨j, Nat.lt_of_succ_lt hj⟩ /
          dist γ.vertices[j] γ.vertices[j + 1] - paramSlack)
    (upperParam_eq : upperParam =
      1 - controlRadii.radius ⟨j + 1, hj⟩ /
          dist γ.vertices[j] γ.vertices[j + 1] + paramSlack)
    (halfWidth_mul_normal_norm_lt_margin_quarter :
      halfWidth * ‖PlanarRot90 (γ.vertices[j + 1] - γ.vertices[j])‖ <
        forbiddenMargins.margin j hj / 4)
    (paramSlack_mul_segmentLength_lt_margin_quarter :
      paramSlack * dist γ.vertices[j] γ.vertices[j + 1] <
        forbiddenMargins.margin j hj / 4) :
    ∀ z ∈ {z | ∃ t : ℝ, t ∈ Set.Ioo lowerParam upperParam ∧
      ∃ s : ℝ, s ∈ Set.Ioo (-halfWidth) halfWidth ∧
        z = AffineMap.lineMap γ.vertices[j] γ.vertices[j + 1] t +
          s • PlanarRot90 (γ.vertices[j + 1] - γ.vertices[j])},
      ∃ p ∈ middleSegments.middle j hj,
        dist z p < forbiddenMargins.margin j hj / 2 := by
  intro z hz
  rcases hz with ⟨t, ht, s, hs, rfl⟩
  obtain ⟨u, huIcc, htu⟩ :=
    collar_real_dist_to_Icc_of_mem_Ioo_expansion paramSlack_pos left_lt_right
      (by simpa [lowerParam_eq, upperParam_eq] using ht)
  let p : EuclideanSpace ℝ (Fin 2) :=
    AffineMap.lineMap γ.vertices[j] γ.vertices[j + 1] u
  have hpM : p ∈ middleSegments.middle j hj := by
    rw [middleSegments.middle_eq j hj]
    exact ⟨u, huIcc, rfl⟩
  refine ⟨p, hpM, ?_⟩
  let q : EuclideanSpace ℝ (Fin 2) :=
    AffineMap.lineMap γ.vertices[j] γ.vertices[j + 1] t
  have hs_abs : |s| < halfWidth := abs_lt.mpr hs
  have hperp :
      dist (AffineMap.lineMap γ.vertices[j] γ.vertices[j + 1] t +
          s • PlanarRot90 (γ.vertices[j + 1] - γ.vertices[j])) q =
        |s| * ‖PlanarRot90 (γ.vertices[j + 1] - γ.vertices[j])‖ := by
    have hsub :
        AffineMap.lineMap γ.vertices[j] γ.vertices[j + 1] t +
            s • PlanarRot90 (γ.vertices[j + 1] - γ.vertices[j]) - q =
          s • PlanarRot90 (γ.vertices[j + 1] - γ.vertices[j]) := by
      simp [q]
    rw [dist_eq_norm, hsub, norm_smul, Real.norm_eq_abs]
  have hperp_lt :
      dist (AffineMap.lineMap γ.vertices[j] γ.vertices[j + 1] t +
          s • PlanarRot90 (γ.vertices[j + 1] - γ.vertices[j])) q <
        forbiddenMargins.margin j hj / 4 := by
    calc
      _ = |s| * ‖PlanarRot90 (γ.vertices[j + 1] - γ.vertices[j])‖ := hperp
      _ ≤ halfWidth * ‖PlanarRot90 (γ.vertices[j + 1] - γ.vertices[j])‖ :=
        mul_le_mul_of_nonneg_right (le_of_lt hs_abs) (norm_nonneg _)
      _ < forbiddenMargins.margin j hj / 4 :=
        halfWidth_mul_normal_norm_lt_margin_quarter
  have hline_lt : dist q p < forbiddenMargins.margin j hj / 4 := by
    have htuD :
        dist t u * dist γ.vertices[j] γ.vertices[j + 1] <
          forbiddenMargins.margin j hj / 4 :=
      (mul_lt_mul_of_pos_right htu
        (dist_pos.mpr (collar_segmentEndpoints_ne γ controlRadii j hj))).trans
        paramSlack_mul_segmentLength_lt_margin_quarter
    calc
      dist q p = dist t u * dist γ.vertices[j] γ.vertices[j + 1] := by
        simpa [q, p] using
          collar_dist_lineMap_lineMap γ.vertices[j] γ.vertices[j + 1] t u
      _ < forbiddenMargins.margin j hj / 4 := htuD
  calc
    dist (AffineMap.lineMap γ.vertices[j] γ.vertices[j + 1] t +
          s • PlanarRot90 (γ.vertices[j + 1] - γ.vertices[j])) p
        ≤ dist (AffineMap.lineMap γ.vertices[j] γ.vertices[j + 1] t +
              s • PlanarRot90 (γ.vertices[j + 1] - γ.vertices[j])) q + dist q p :=
      dist_triangle _ _ _
    _ < forbiddenMargins.margin j hj / 4 +
        forbiddenMargins.margin j hj / 4 := add_lt_add hperp_lt hline_lt
    _ = forbiddenMargins.margin j hj / 2 := by ring

private lemma collar_tubeSubsetEtaNeighborhood
    (γ : PolygonalArc) {η : ℝ}
    (j : ℕ) (hj : j + 1 < γ.vertices.length)
    (lowerParam upperParam halfWidth : ℝ)
    (normal : EuclideanSpace ℝ (Fin 2))
    (lowerParam_pos : 0 < lowerParam) (upperParam_lt_one : upperParam < 1)
    (halfWidth_mul_normal_norm_lt_eta : halfWidth * ‖normal‖ < η) :
    ∀ z ∈ {z | ∃ t : ℝ, t ∈ Set.Ioo lowerParam upperParam ∧
      ∃ s : ℝ, s ∈ Set.Ioo (-halfWidth) halfWidth ∧
        z = AffineMap.lineMap γ.vertices[j] γ.vertices[j + 1] t + s • normal},
      ∃ p ∈ γ.carrier, dist z p < η := by
  intro z hz
  rcases hz with ⟨t, ht, s, hs, rfl⟩
  let p : EuclideanSpace ℝ (Fin 2) :=
    AffineMap.lineMap γ.vertices[j] γ.vertices[j + 1] t
  have hpseg : p ∈ segment ℝ γ.vertices[j] γ.vertices[j + 1] := by
    rw [segment_eq_image_lineMap]
    exact ⟨t, ⟨le_of_lt (lowerParam_pos.trans ht.1),
      le_of_lt (ht.2.trans upperParam_lt_one)⟩, rfl⟩
  have hpcarrier : p ∈ γ.carrier := by
    rw [γ.carrier_eq]
    exact ⟨j, hj, hpseg⟩
  refine ⟨p, hpcarrier, ?_⟩
  have hs_abs : |s| < halfWidth := abs_lt.mpr hs
  have hsub :
      AffineMap.lineMap γ.vertices[j] γ.vertices[j + 1] t + s • normal - p =
        s • normal := by
    dsimp [p]
    abel
  calc
    dist (AffineMap.lineMap γ.vertices[j] γ.vertices[j + 1] t + s • normal) p =
        |s| * ‖normal‖ := by
      rw [dist_eq_norm, hsub, norm_smul, Real.norm_eq_abs]
    _ ≤ halfWidth * ‖normal‖ :=
      mul_le_mul_of_nonneg_right (le_of_lt hs_abs) (norm_nonneg _)
    _ < η := halfWidth_mul_normal_norm_lt_eta

private structure CollarTubeFacts
    (γ : PolygonalArc) {η : ℝ}
    (controlRadii : PolygonalArcCollarControlRadii γ η)
    (middleSegments : PolygonalArcCollarMiddleSegmentData γ controlRadii)
    (forbiddenMargins :
      PolygonalArcCollarMiddleForbiddenMargins γ controlRadii middleSegments)
    (tube leftHalf rightHalf :
      (j : ℕ) → j + 1 < γ.vertices.length → Set (EuclideanSpace ℝ (Fin 2))) : Prop where
  middle_subset_tube :
    ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length),
      middleSegments.middle j hj ⊆ tube j hj
  leftHalf_subset_tube :
    ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length), leftHalf j hj ⊆ tube j hj
  rightHalf_subset_tube :
    ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length), rightHalf j hj ⊆ tube j hj
  tube_subset_eta_neighborhood :
    ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length),
      ∀ z ∈ tube j hj, ∃ p ∈ γ.carrier, dist z p < η
  tube_point_close_to_middle :
    ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length),
      ∀ z ∈ tube j hj, ∃ p ∈ middleSegments.middle j hj,
        dist z p < forbiddenMargins.margin j hj / 2
  tube_disjoint_nonadjacent_segments :
    ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length)
      (k : ℕ) (hk : k + 1 < γ.vertices.length),
        (j + 1 < k ∨ k + 1 < j) →
          Disjoint (tube j hj) (segment ℝ γ.vertices[k] γ.vertices[k + 1])
  tube_disjoint_nonincident_control_disks :
    ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length)
      (i : Fin γ.vertices.length), i.1 ≠ j → i.1 ≠ j + 1 →
        Disjoint (tube j hj)
          (Metric.closedBall γ.vertices[i.1] (controlRadii.radius i))
  tube_disjoint_nonadjacent_middle_cores :
    ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length)
      (k : ℕ) (hk : k + 1 < γ.vertices.length),
        (j + 1 < k ∨ k + 1 < j) →
          Disjoint (tube j hj) (middleSegments.middle k hk)
  tube_disjoint_nonadjacent_tubes :
    ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length)
      (k : ℕ) (hk : k + 1 < γ.vertices.length),
        (j + 1 < k ∨ k + 1 < j) → Disjoint (tube j hj) (tube k hk)

private lemma collar_tubeFacts
    (γ : PolygonalArc) {η : ℝ}
    (controlRadii : PolygonalArcCollarControlRadii γ η)
    (middleSegments : PolygonalArcCollarMiddleSegmentData γ controlRadii)
    (forbiddenMargins :
      PolygonalArcCollarMiddleForbiddenMargins γ controlRadii middleSegments)
    (lowerParam upperParam halfWidth paramSlack :
      (j : ℕ) → j + 1 < γ.vertices.length → ℝ)
    (normal : (j : ℕ) → j + 1 < γ.vertices.length → EuclideanSpace ℝ (Fin 2))
    (tube leftHalf rightHalf :
      (j : ℕ) → j + 1 < γ.vertices.length → Set (EuclideanSpace ℝ (Fin 2)))
    (tube_eq : ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length), tube j hj =
      {z | ∃ t : ℝ, t ∈ Set.Ioo (lowerParam j hj) (upperParam j hj) ∧
        ∃ s : ℝ, s ∈ Set.Ioo (-(halfWidth j hj)) (halfWidth j hj) ∧
          z = AffineMap.lineMap γ.vertices[j] γ.vertices[j + 1] t +
            s • normal j hj})
    (leftHalf_eq : ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length), leftHalf j hj =
      {z | ∃ t : ℝ, t ∈ Set.Ioo (lowerParam j hj) (upperParam j hj) ∧
        ∃ s : ℝ, s ∈ Set.Ioo (0 : ℝ) (halfWidth j hj) ∧
          z = AffineMap.lineMap γ.vertices[j] γ.vertices[j + 1] t +
            s • normal j hj})
    (rightHalf_eq : ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length), rightHalf j hj =
      {z | ∃ t : ℝ, t ∈ Set.Ioo (lowerParam j hj) (upperParam j hj) ∧
        ∃ s : ℝ, s ∈ Set.Ioo (-(halfWidth j hj)) (0 : ℝ) ∧
          z = AffineMap.lineMap γ.vertices[j] γ.vertices[j + 1] t +
            s • normal j hj})
    (normal_eq : ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length),
      normal j hj = PlanarRot90 (γ.vertices[j + 1] - γ.vertices[j]))
    (lowerParam_pos : ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length),
      0 < lowerParam j hj)
    (upperParam_lt_one : ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length),
      upperParam j hj < 1)
    (halfWidth_pos : ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length),
      0 < halfWidth j hj)
    (lowerParam_lt_left : ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length),
      lowerParam j hj < controlRadii.radius ⟨j, Nat.lt_of_succ_lt hj⟩ /
        dist γ.vertices[j] γ.vertices[j + 1])
    (right_lt_upperParam : ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length),
      1 - controlRadii.radius ⟨j + 1, hj⟩ /
        dist γ.vertices[j] γ.vertices[j + 1] < upperParam j hj)
    (paramSlack_pos : ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length),
      0 < paramSlack j hj)
    (left_lt_right : ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length),
      controlRadii.radius ⟨j, Nat.lt_of_succ_lt hj⟩ /
          dist γ.vertices[j] γ.vertices[j + 1] <
        1 - controlRadii.radius ⟨j + 1, hj⟩ /
          dist γ.vertices[j] γ.vertices[j + 1])
    (lowerParam_eq : ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length), lowerParam j hj =
      controlRadii.radius ⟨j, Nat.lt_of_succ_lt hj⟩ /
          dist γ.vertices[j] γ.vertices[j + 1] - paramSlack j hj)
    (upperParam_eq : ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length), upperParam j hj =
      1 - controlRadii.radius ⟨j + 1, hj⟩ /
          dist γ.vertices[j] γ.vertices[j + 1] + paramSlack j hj)
    (halfWidth_mul_normal_norm_lt_eta :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length),
        halfWidth j hj * ‖normal j hj‖ < η)
    (halfWidth_mul_normal_norm_lt_margin_quarter :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length),
        halfWidth j hj * ‖normal j hj‖ < forbiddenMargins.margin j hj / 4)
    (paramSlack_mul_segmentLength_lt_margin_quarter :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length),
        paramSlack j hj * dist γ.vertices[j] γ.vertices[j + 1] <
          forbiddenMargins.margin j hj / 4) :
    CollarTubeFacts γ controlRadii middleSegments forbiddenMargins tube leftHalf rightHalf := by
  have hmiddle : ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length),
      middleSegments.middle j hj ⊆ tube j hj := by
    intro j hj z hz
    rw [middleSegments.middle_eq j hj] at hz
    rcases hz with ⟨t, ht, rfl⟩
    rw [tube_eq j hj]
    refine ⟨t, ⟨(lowerParam_lt_left j hj).trans_le ht.1,
      lt_of_le_of_lt ht.2 (right_lt_upperParam j hj)⟩, 0, ?_, by simp⟩
    exact ⟨by simpa using halfWidth_pos j hj, halfWidth_pos j hj⟩
  have hleft : ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length),
      leftHalf j hj ⊆ tube j hj := by
    intro j hj z hz
    rw [leftHalf_eq j hj] at hz
    rcases hz with ⟨t, ht, s, hs, rfl⟩
    rw [tube_eq j hj]
    exact ⟨t, ht, s,
      ⟨lt_trans (neg_neg_of_pos (halfWidth_pos j hj)) hs.1, hs.2⟩, rfl⟩
  have hright : ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length),
      rightHalf j hj ⊆ tube j hj := by
    intro j hj z hz
    rw [rightHalf_eq j hj] at hz
    rcases hz with ⟨t, ht, s, hs, rfl⟩
    rw [tube_eq j hj]
    exact ⟨t, ht, s, ⟨hs.1, hs.2.trans (halfWidth_pos j hj)⟩, rfl⟩
  have heta : ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length),
      ∀ z ∈ tube j hj, ∃ p ∈ γ.carrier, dist z p < η := by
    intro j hj
    rw [tube_eq j hj]
    exact collar_tubeSubsetEtaNeighborhood γ j hj (lowerParam j hj)
      (upperParam j hj) (halfWidth j hj) (normal j hj) (lowerParam_pos j hj)
      (upperParam_lt_one j hj) (halfWidth_mul_normal_norm_lt_eta j hj)
  have hclose : ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length),
      ∀ z ∈ tube j hj, ∃ p ∈ middleSegments.middle j hj,
        dist z p < forbiddenMargins.margin j hj / 2 := by
    intro j hj
    rw [tube_eq j hj]
    rw [normal_eq j hj]
    have hmargin := halfWidth_mul_normal_norm_lt_margin_quarter j hj
    rw [normal_eq j hj] at hmargin
    exact collar_tubePointCloseToMiddle γ controlRadii middleSegments forbiddenMargins
      j hj (lowerParam j hj) (upperParam j hj) (paramSlack j hj)
        (halfWidth j hj) (paramSlack_pos j hj) (left_lt_right j hj)
        (lowerParam_eq j hj) (upperParam_eq j hj)
        hmargin
        (paramSlack_mul_segmentLength_lt_margin_quarter j hj)
  have hsegments := collar_tubeDisjointNonadjacentSegmentOfCloseToMiddle γ
    controlRadii middleSegments forbiddenMargins tube hclose
  have hdisks := collar_tubeDisjointNonincidentControlDiskOfCloseToMiddle γ
    controlRadii middleSegments forbiddenMargins tube hclose
  have hcores : ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length)
      (k : ℕ) (hk : k + 1 < γ.vertices.length),
        (j + 1 < k ∨ k + 1 < j) →
          Disjoint (tube j hj) (middleSegments.middle k hk) := by
    intro j hj k hk hgap
    rw [Set.disjoint_left]
    intro z hzTube hzMiddle
    exact Set.disjoint_left.mp (hsegments j hj k hk hgap) hzTube
      (middleSegments.middle_subset_segment k hk hzMiddle)
  have htubes := collar_tubesDisjointOfCloseToSeparatedMiddle γ controlRadii
    middleSegments forbiddenMargins tube hclose
  exact ⟨hmiddle, hleft, hright, heta, hclose, hsegments, hdisks, hcores, htubes⟩

private structure CollarConeFacts
    (γ : PolygonalArc)
    (initialConeBound terminalConeBound :
      (j : ℕ) → j + 1 < γ.vertices.length → ℝ)
    (normal :
      (j : ℕ) → j + 1 < γ.vertices.length → EuclideanSpace ℝ (Fin 2)) : Prop where
  initial_signed_cone_disjoint_previous_segment :
    ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length) (hprev : 0 < j),
      Disjoint
        {z | ∃ t : ℝ, t ∈ Set.Ioo (0 : ℝ) (1 : ℝ) ∧
          ∃ s : ℝ, s ≠ 0 ∧ |s| < initialConeBound j hj * t ∧
            z = AffineMap.lineMap γ.vertices[j] γ.vertices[j + 1] t + s • normal j hj}
        (segment ℝ γ.vertices[j - 1] γ.vertices[j])
  terminal_signed_cone_disjoint_next_segment :
    ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length)
      (hnext : (j + 1) + 1 < γ.vertices.length),
        Disjoint
          {z | ∃ t : ℝ, t ∈ Set.Ioo (0 : ℝ) (1 : ℝ) ∧
            ∃ s : ℝ, s ≠ 0 ∧ |s| < terminalConeBound j hj * (1 - t) ∧
              z = AffineMap.lineMap γ.vertices[j] γ.vertices[j + 1] t + s • normal j hj}
          (segment ℝ γ.vertices[j + 1] γ.vertices[j + 2])
  successive_positive_negative_cones_disjoint :
    ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length)
      (hnext : (j + 1) + 1 < γ.vertices.length),
        Disjoint
          {z | ∃ t : ℝ, t ∈ Set.Ioo (0 : ℝ) (1 : ℝ) ∧
            ∃ s : ℝ, 0 < s ∧ s < terminalConeBound j hj * (1 - t) ∧
              z = AffineMap.lineMap γ.vertices[j] γ.vertices[j + 1] t + s • normal j hj}
          {z | ∃ t : ℝ, t ∈ Set.Ioo (0 : ℝ) (1 : ℝ) ∧
            ∃ s : ℝ, s < 0 ∧ |s| < initialConeBound (j + 1) hnext * t ∧
              z = AffineMap.lineMap γ.vertices[j + 1] γ.vertices[j + 2] t +
                s • normal (j + 1) hnext}
  successive_negative_positive_cones_disjoint :
    ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length)
      (hnext : (j + 1) + 1 < γ.vertices.length),
        Disjoint
          {z | ∃ t : ℝ, t ∈ Set.Ioo (0 : ℝ) (1 : ℝ) ∧
            ∃ s : ℝ, s < 0 ∧ |s| < terminalConeBound j hj * (1 - t) ∧
              z = AffineMap.lineMap γ.vertices[j] γ.vertices[j + 1] t + s • normal j hj}
          {z | ∃ t : ℝ, t ∈ Set.Ioo (0 : ℝ) (1 : ℝ) ∧
            ∃ s : ℝ, 0 < s ∧ s < initialConeBound (j + 1) hnext * t ∧
              z = AffineMap.lineMap γ.vertices[j + 1] γ.vertices[j + 2] t +
                s • normal (j + 1) hnext}

private lemma collar_coneFacts
    (γ : PolygonalArc)
    (initialConeBound terminalConeBound :
      (j : ℕ) → j + 1 < γ.vertices.length → ℝ)
    (normal :
      (j : ℕ) → j + 1 < γ.vertices.length → EuclideanSpace ℝ (Fin 2))
    (normal_eq : ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length),
      normal j hj = PlanarRot90 (γ.vertices[j + 1] - γ.vertices[j]))
    (initialSource : ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length) (hprev : 0 < j),
      ∃ κ : ℝ, 0 < κ ∧ ∀ c t s : ℝ, 0 ≤ c → 0 < t → s ≠ 0 → |s| < κ * t →
        c • (γ.vertices[j - 1] - γ.vertices[j]) ≠
          t • (γ.vertices[j + 1] - γ.vertices[j]) +
            s • PlanarRot90 (γ.vertices[j + 1] - γ.vertices[j]))
    (terminalSource : ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length)
      (hnext : (j + 1) + 1 < γ.vertices.length),
      ∃ κ : ℝ, 0 < κ ∧ ∀ c t s : ℝ, 0 ≤ c → 0 < t → s ≠ 0 → |s| < κ * t →
        c • (γ.vertices[j + 2] - γ.vertices[j + 1]) ≠
          t • (γ.vertices[j] - γ.vertices[j + 1]) +
            s • PlanarRot90 (γ.vertices[j] - γ.vertices[j + 1]))
    (successiveSource : ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length)
      (hnext : (j + 1) + 1 < γ.vertices.length),
      ∃ κ : ℝ, 0 < κ ∧ ∀ a c b r : ℝ, 0 < a → 0 < c → 0 < b * r →
        |b| < κ * a → |r| < κ * c →
          a • (γ.vertices[j] - γ.vertices[j + 1]) +
              b • PlanarRot90 (γ.vertices[j] - γ.vertices[j + 1]) ≠
            c • (γ.vertices[j + 2] - γ.vertices[j + 1]) +
              r • PlanarRot90 (γ.vertices[j + 2] - γ.vertices[j + 1]))
    (initial_le : ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length) (hprev : 0 < j),
      initialConeBound j hj ≤ Classical.choose (initialSource j hj hprev))
    (terminal_le : ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length)
      (hnext : (j + 1) + 1 < γ.vertices.length),
      terminalConeBound j hj ≤ Classical.choose (terminalSource j hj hnext))
    (successive_terminal_le : ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length)
      (hnext : (j + 1) + 1 < γ.vertices.length),
      terminalConeBound j hj ≤ Classical.choose (successiveSource j hj hnext))
    (successive_initial_le : ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length)
      (hnext : (j + 1) + 1 < γ.vertices.length),
      initialConeBound (j + 1) hnext ≤ Classical.choose (successiveSource j hj hnext)) :
    CollarConeFacts γ initialConeBound terminalConeBound normal := by
  have hiBound : ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length) (hprev : 0 < j),
      ∀ c t s : ℝ, 0 ≤ c → 0 < t → s ≠ 0 → |s| < initialConeBound j hj * t →
        c • (γ.vertices[j - 1] - γ.vertices[j]) ≠
          t • (γ.vertices[j + 1] - γ.vertices[j]) +
            s • PlanarRot90 (γ.vertices[j + 1] - γ.vertices[j]) := by
    intro j hj hprev
    exact collar_coneBound_mono _ _ (initial_le j hj hprev) _
      (Classical.choose_spec (initialSource j hj hprev)).2
  have htBound : ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length)
      (hnext : (j + 1) + 1 < γ.vertices.length),
      ∀ c t s : ℝ, 0 ≤ c → 0 < t → s ≠ 0 → |s| < terminalConeBound j hj * t →
        c • (γ.vertices[j + 2] - γ.vertices[j + 1]) ≠
          t • (γ.vertices[j] - γ.vertices[j + 1]) +
            s • PlanarRot90 (γ.vertices[j] - γ.vertices[j + 1]) := by
    intro j hj hnext
    exact collar_coneBound_mono _ _ (terminal_le j hj hnext) _
      (Classical.choose_spec (terminalSource j hj hnext)).2
  have hsBound : ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length)
      (hnext : (j + 1) + 1 < γ.vertices.length),
      ∀ a c b r : ℝ, 0 < a → 0 < c → 0 < b * r →
        |b| < terminalConeBound j hj * a →
        |r| < initialConeBound (j + 1) hnext * c →
          a • (γ.vertices[j] - γ.vertices[j + 1]) +
              b • PlanarRot90 (γ.vertices[j] - γ.vertices[j + 1]) ≠
            c • (γ.vertices[j + 2] - γ.vertices[j + 1]) +
              r • PlanarRot90 (γ.vertices[j + 2] - γ.vertices[j + 1]) := by
    intro j hj hnext
    exact collar_twoConeBounds_mono _ _ _ (successive_terminal_le j hj hnext)
      (successive_initial_le j hj hnext) _
      (Classical.choose_spec (successiveSource j hj hnext)).2
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro j hj hprev
    rw [normal_eq j hj]
    exact collar_initialSignedConeDisjointPrevious γ j hj hprev
      (initialConeBound j hj) (hiBound j hj hprev)
  · intro j hj hnext
    rw [normal_eq j hj]
    exact collar_terminalSignedConeDisjointNext γ j hj hnext
      (terminalConeBound j hj) (htBound j hj hnext)
  · intro j hj hnext
    rw [normal_eq j hj, normal_eq (j + 1) hnext]
    exact collar_successivePositiveNegativeConesDisjoint γ j hj hnext
      (terminalConeBound j hj) (initialConeBound (j + 1) hnext) (hsBound j hj hnext)
  · intro j hj hnext
    rw [normal_eq j hj, normal_eq (j + 1) hnext]
    exact collar_successiveNegativePositiveConesDisjoint γ j hj hnext
      (terminalConeBound j hj) (initialConeBound (j + 1) hnext) (hsBound j hj hnext)

private structure CollarCenterlineAwayFacts
    (γ : PolygonalArc) {η : ℝ}
    (controlRadii : PolygonalArcCollarControlRadii γ η)
    (initialAwaySeparation :
      (j : ℕ) → (hj : j + 1 < γ.vertices.length) → 0 < j → ℝ)
    (terminalAwaySeparation successiveAwaySeparation :
      ∀ (j : ℕ), (hj : j + 1 < γ.vertices.length) →
        (j + 1) + 1 < γ.vertices.length → ℝ) : Prop where
  initial_centerline_previous_segment_away :
    ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length) (hprev : 0 < j),
      ∀ t : ℝ,
        t ∈ Set.Icc
          (controlRadii.radius ⟨j, Nat.lt_of_succ_lt hj⟩ /
            dist γ.vertices[j] γ.vertices[j + 1]) (1 : ℝ) →
          ∀ q, q ∈ segment ℝ γ.vertices[j - 1] γ.vertices[j] →
            initialAwaySeparation j hj hprev ≤
              dist (AffineMap.lineMap γ.vertices[j] γ.vertices[j + 1] t) q
  terminal_centerline_next_segment_away :
    ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length)
      (hnext : (j + 1) + 1 < γ.vertices.length),
        ∀ t : ℝ,
          t ∈ Set.Icc (0 : ℝ)
            (1 - controlRadii.radius ⟨j + 1, hj⟩ /
              dist γ.vertices[j] γ.vertices[j + 1]) →
            ∀ q, q ∈ segment ℝ γ.vertices[j + 1] γ.vertices[j + 2] →
              terminalAwaySeparation j hj hnext ≤
                dist (AffineMap.lineMap γ.vertices[j] γ.vertices[j + 1] t) q
  successive_centerlines_away :
    ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length)
      (hnext : (j + 1) + 1 < γ.vertices.length),
        ∀ t : ℝ,
          t ∈ Set.Icc (0 : ℝ)
            (1 - controlRadii.radius ⟨j + 1, hj⟩ /
              dist γ.vertices[j] γ.vertices[j + 1]) →
            ∀ u : ℝ,
              u ∈ Set.Icc
                (controlRadii.radius ⟨j + 1, hj⟩ /
                  dist γ.vertices[j + 1] γ.vertices[j + 2]) (1 : ℝ) →
                successiveAwaySeparation j hj hnext ≤
                  dist
                    (AffineMap.lineMap γ.vertices[j] γ.vertices[j + 1] t)
                    (AffineMap.lineMap γ.vertices[j + 1] γ.vertices[j + 2] u)

private lemma collar_centerlineAwayFacts
    (γ : PolygonalArc) {η : ℝ}
    (controlRadii : PolygonalArcCollarControlRadii γ η)
    (leftParam rightParam :
      (j : ℕ) → j + 1 < γ.vertices.length → ℝ)
    (initialAwaySeparation :
      (j : ℕ) → (hj : j + 1 < γ.vertices.length) → 0 < j → ℝ)
    (terminalAwaySeparation successiveAwaySeparation :
      ∀ (j : ℕ), (hj : j + 1 < γ.vertices.length) →
        (j + 1) + 1 < γ.vertices.length → ℝ)
    (initialAwayExists :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length) (hprev : 0 < j),
        ∃ δ : ℝ, 0 < δ ∧
          ∀ t : ℝ, t ∈ Set.Icc (leftParam j hj) (1 : ℝ) →
            ∀ q, q ∈ segment ℝ γ.vertices[j - 1] γ.vertices[j] →
              δ ≤ dist (AffineMap.lineMap γ.vertices[j] γ.vertices[j + 1] t) q)
    (terminalAwayExists :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length)
        (hnext : (j + 1) + 1 < γ.vertices.length),
          ∃ δ : ℝ, 0 < δ ∧
            ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) (rightParam j hj) →
              ∀ q, q ∈ segment ℝ γ.vertices[j + 1] γ.vertices[j + 2] →
                δ ≤ dist (AffineMap.lineMap γ.vertices[j] γ.vertices[j + 1] t) q)
    (successiveAwayExists :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length)
        (hnext : (j + 1) + 1 < γ.vertices.length),
          ∃ δ : ℝ, 0 < δ ∧
            ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) (rightParam j hj) →
              ∀ u : ℝ, u ∈ Set.Icc (leftParam (j + 1) hnext) (1 : ℝ) →
                δ ≤ dist
                  (AffineMap.lineMap γ.vertices[j] γ.vertices[j + 1] t)
                  (AffineMap.lineMap γ.vertices[j + 1] γ.vertices[j + 2] u))
    (leftParam_eq : ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length),
      leftParam j hj = controlRadii.radius ⟨j, Nat.lt_of_succ_lt hj⟩ /
        dist γ.vertices[j] γ.vertices[j + 1])
    (rightParam_eq : ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length),
      rightParam j hj = 1 - controlRadii.radius ⟨j + 1, hj⟩ /
        dist γ.vertices[j] γ.vertices[j + 1])
    (initialAwaySeparation_eq :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length) (hprev : 0 < j),
        initialAwaySeparation j hj hprev =
          Classical.choose (initialAwayExists j hj hprev))
    (terminalAwaySeparation_eq :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length)
        (hnext : (j + 1) + 1 < γ.vertices.length),
          terminalAwaySeparation j hj hnext =
            Classical.choose (terminalAwayExists j hj hnext))
    (successiveAwaySeparation_eq :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length)
        (hnext : (j + 1) + 1 < γ.vertices.length),
          successiveAwaySeparation j hj hnext =
            Classical.choose (successiveAwayExists j hj hnext)) :
    CollarCenterlineAwayFacts γ controlRadii initialAwaySeparation
      terminalAwaySeparation successiveAwaySeparation := by
  refine ⟨?_, ?_, ?_⟩
  · intro j hj hprev t ht q hq
    rw [initialAwaySeparation_eq j hj hprev]
    exact (Classical.choose_spec (initialAwayExists j hj hprev)).2 t
      (by rw [leftParam_eq j hj]; exact ht) q hq
  · intro j hj hnext t ht q hq
    rw [terminalAwaySeparation_eq j hj hnext]
    exact (Classical.choose_spec (terminalAwayExists j hj hnext)).2 t
      (by rw [rightParam_eq j hj]; exact ht) q hq
  · intro j hj hnext t ht u hu
    rw [successiveAwaySeparation_eq j hj hnext]
    exact (Classical.choose_spec (successiveAwayExists j hj hnext)).2 t
      (by rw [rightParam_eq j hj]; exact ht) u
      (by rw [leftParam_eq (j + 1) hnext]; exact hu)

private structure CollarAwayWidthFacts
    (γ : PolygonalArc)
    (halfWidth : (j : ℕ) → j + 1 < γ.vertices.length → ℝ)
    (normal :
      (j : ℕ) → j + 1 < γ.vertices.length → EuclideanSpace ℝ (Fin 2))
    (initialAwaySeparation :
      (j : ℕ) → (hj : j + 1 < γ.vertices.length) → 0 < j → ℝ)
    (terminalAwaySeparation successiveAwaySeparation :
      ∀ (j : ℕ), (hj : j + 1 < γ.vertices.length) →
        (j + 1) + 1 < γ.vertices.length → ℝ) : Prop where
  initial_halfWidth_mul_normal_norm_lt_away_quarter :
    ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length) (hprev : 0 < j),
      halfWidth j hj * ‖normal j hj‖ < initialAwaySeparation j hj hprev / 4
  terminal_halfWidth_mul_normal_norm_lt_away_quarter :
    ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length)
      (hnext : (j + 1) + 1 < γ.vertices.length),
        halfWidth j hj * ‖normal j hj‖ < terminalAwaySeparation j hj hnext / 4
  successive_halfWidth_normal_sum_lt_away_quarter :
    ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length)
      (hnext : (j + 1) + 1 < γ.vertices.length),
        halfWidth j hj * ‖normal j hj‖ +
            halfWidth (j + 1) hnext * ‖normal (j + 1) hnext‖ <
          successiveAwaySeparation j hj hnext / 4

private lemma collar_awayWidthFacts
    (γ : PolygonalArc)
    (segmentLength halfWidth :
      (j : ℕ) → j + 1 < γ.vertices.length → ℝ)
    (normal :
      (j : ℕ) → j + 1 < γ.vertices.length → EuclideanSpace ℝ (Fin 2))
    (initialAwaySeparation :
      (j : ℕ) → (hj : j + 1 < γ.vertices.length) → 0 < j → ℝ)
    (terminalAwaySeparation successiveAwaySeparation :
      ∀ (j : ℕ), (hj : j + 1 < γ.vertices.length) →
        (j + 1) + 1 < γ.vertices.length → ℝ)
    (segmentLength_pos : ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length),
      0 < segmentLength j hj)
    (normal_norm_eq_segmentLength :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length),
        ‖normal j hj‖ = segmentLength j hj)
    (initialAwaySeparation_pos :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length) (hprev : 0 < j),
        0 < initialAwaySeparation j hj hprev)
    (terminalAwaySeparation_pos :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length)
        (hnext : (j + 1) + 1 < γ.vertices.length),
          0 < terminalAwaySeparation j hj hnext)
    (successiveAwaySeparation_pos :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length)
        (hnext : (j + 1) + 1 < γ.vertices.length),
          0 < successiveAwaySeparation j hj hnext)
    (initial_le :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length) (hprev : 0 < j),
        halfWidth j hj ≤ initialAwaySeparation j hj hprev /
          (8 * (segmentLength j hj + 1)))
    (terminal_le :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length)
        (hnext : (j + 1) + 1 < γ.vertices.length),
          halfWidth j hj ≤ terminalAwaySeparation j hj hnext /
            (8 * (segmentLength j hj + 1)))
    (successive_left_le :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length)
        (hnext : (j + 1) + 1 < γ.vertices.length),
          halfWidth j hj ≤ successiveAwaySeparation j hj hnext /
            (16 * (segmentLength j hj + 1)))
    (successive_right_le :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length)
        (hnext : (j + 1) + 1 < γ.vertices.length),
          halfWidth (j + 1) hnext ≤ successiveAwaySeparation j hj hnext /
            (16 * (segmentLength (j + 1) hnext + 1))) :
    CollarAwayWidthFacts γ halfWidth normal initialAwaySeparation
      terminalAwaySeparation successiveAwaySeparation := by
  refine ⟨?_, ?_, ?_⟩
  · intro j hj hprev
    rw [normal_norm_eq_segmentLength j hj]
    exact collar_scaled_eighth_mul_lt_quarter (segmentLength_pos j hj)
      (initialAwaySeparation_pos j hj hprev) (initial_le j hj hprev)
  · intro j hj hnext
    rw [normal_norm_eq_segmentLength j hj]
    exact collar_scaled_eighth_mul_lt_quarter (segmentLength_pos j hj)
      (terminalAwaySeparation_pos j hj hnext) (terminal_le j hj hnext)
  · intro j hj hnext
    rw [normal_norm_eq_segmentLength j hj,
      normal_norm_eq_segmentLength (j + 1) hnext]
    have hleft := collar_scaled_sixteenth_mul_lt_eighth
      (segmentLength_pos j hj) (successiveAwaySeparation_pos j hj hnext)
      (successive_left_le j hj hnext)
    have hright := collar_scaled_sixteenth_mul_lt_eighth
      (segmentLength_pos (j + 1) hnext) (successiveAwaySeparation_pos j hj hnext)
      (successive_right_le j hj hnext)
    nlinarith


lemma PolygonalArcCollarCompatibleOrientedTubeDataExists (γ : PolygonalArc) {η : ℝ}
    (controlRadii : PolygonalArcCollarControlRadii γ η)
    (middleSegments : PolygonalArcCollarMiddleSegmentData γ controlRadii)
    (forbiddenMargins :
      PolygonalArcCollarMiddleForbiddenMargins γ controlRadii middleSegments) :
    Nonempty
      (PolygonalArcCollarCompatibleOrientedTubeData γ controlRadii middleSegments
        forbiddenMargins) := by
  have initialConeAvoidsPreviousRay :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length) (hprev : 0 < j),
        ∃ κ : ℝ, 0 < κ ∧
          ∀ c t s : ℝ, 0 ≤ c → 0 < t → s ≠ 0 → |s| < κ * t →
            c • (γ.vertices[j - 1] - γ.vertices[j]) ≠
              t • (γ.vertices[j + 1] - γ.vertices[j]) +
                s • PlanarRot90 (γ.vertices[j + 1] - γ.vertices[j]) := by
    exact collar_initialConeAvoidsPreviousRay γ controlRadii
  have terminalConeAvoidsNextRay :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length)
        (hnext : (j + 1) + 1 < γ.vertices.length),
          ∃ κ : ℝ, 0 < κ ∧
            ∀ c t s : ℝ, 0 ≤ c → 0 < t → s ≠ 0 → |s| < κ * t →
              c • (γ.vertices[j + 2] - γ.vertices[j + 1]) ≠
                t • (γ.vertices[j] - γ.vertices[j + 1]) +
                  s • PlanarRot90 (γ.vertices[j] - γ.vertices[j + 1]) := by
    exact collar_terminalConeAvoidsNextRay γ controlRadii
  have successiveOutwardConesDisjoint :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length)
        (hnext : (j + 1) + 1 < γ.vertices.length),
          ∃ κ : ℝ, 0 < κ ∧
            ∀ a c b r : ℝ, 0 < a → 0 < c → 0 < b * r →
              |b| < κ * a → |r| < κ * c →
                a • (γ.vertices[j] - γ.vertices[j + 1]) +
                    b • PlanarRot90 (γ.vertices[j] - γ.vertices[j + 1]) ≠
                  c • (γ.vertices[j + 2] - γ.vertices[j + 1]) +
                    r • PlanarRot90 (γ.vertices[j + 2] - γ.vertices[j + 1]) := by
    exact collar_successiveOutwardConesDisjoint γ controlRadii
  let leftParam : (j : ℕ) → j + 1 < γ.vertices.length → ℝ := fun j hj =>
    controlRadii.radius ⟨j, Nat.lt_of_succ_lt hj⟩ /
      dist γ.vertices[j] γ.vertices[j + 1]
  let rightParam : (j : ℕ) → j + 1 < γ.vertices.length → ℝ := fun j hj =>
    1 - controlRadii.radius ⟨j + 1, hj⟩ /
      dist γ.vertices[j] γ.vertices[j + 1]
  let segmentLength : (j : ℕ) → j + 1 < γ.vertices.length → ℝ := fun j hj =>
    dist γ.vertices[j] γ.vertices[j + 1]
  let paramSlack : (j : ℕ) → j + 1 < γ.vertices.length → ℝ := fun j hj =>
    min (leftParam j hj / 2)
      (min ((1 - rightParam j hj) / 2)
        (forbiddenMargins.margin j hj / (8 * (segmentLength j hj + 1))))
  let lowerParam : (j : ℕ) → j + 1 < γ.vertices.length → ℝ := fun j hj =>
    leftParam j hj - paramSlack j hj
  let upperParam : (j : ℕ) → j + 1 < γ.vertices.length → ℝ := fun j hj =>
    rightParam j hj + paramSlack j hj
  let normal : (j : ℕ) → j + 1 < γ.vertices.length →
      EuclideanSpace ℝ (Fin 2) := fun j hj =>
    PlanarRot90 (γ.vertices[j + 1] - γ.vertices[j])
  let initialRayCone : (j : ℕ) → j + 1 < γ.vertices.length → ℝ := fun j hj =>
    if hprev : 0 < j then
      Classical.choose (initialConeAvoidsPreviousRay j hj hprev)
    else
      1
  let terminalRayCone : (j : ℕ) → j + 1 < γ.vertices.length → ℝ := fun j hj =>
    if hnext : (j + 1) + 1 < γ.vertices.length then
      Classical.choose (terminalConeAvoidsNextRay j hj hnext)
    else
      1
  let initialPairCone : (j : ℕ) → j + 1 < γ.vertices.length → ℝ := fun j hj =>
    if hprev : 0 < j then
      Classical.choose
        (successiveOutwardConesDisjoint (j - 1)
          (by
            have hj' : j < γ.vertices.length := Nat.lt_of_succ_lt hj
            simpa [Nat.sub_add_cancel (Nat.succ_le_of_lt hprev)] using hj')
          (by
            simpa [Nat.sub_add_cancel (Nat.succ_le_of_lt hprev)] using hj))
    else
      1
  let terminalPairCone : (j : ℕ) → j + 1 < γ.vertices.length → ℝ := fun j hj =>
    if hnext : (j + 1) + 1 < γ.vertices.length then
      Classical.choose (successiveOutwardConesDisjoint j hj hnext)
    else
      1
  let initialConeBound : (j : ℕ) → j + 1 < γ.vertices.length → ℝ := fun j hj =>
    min (initialRayCone j hj) (initialPairCone j hj)
  let terminalConeBound : (j : ℕ) → j + 1 < γ.vertices.length → ℝ := fun j hj =>
    min (terminalRayCone j hj) (terminalPairCone j hj)
  have leftParam_pos :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length), 0 < leftParam j hj := by
    intro j hj
    simpa [leftParam] using middleSegments.left_parameter_pos j hj
  have leftParam_lt_rightParam :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length),
        leftParam j hj < rightParam j hj := by
    intro j hj
    simpa [leftParam, rightParam] using
      middleSegments.left_parameter_lt_right_parameter j hj
  have rightParam_lt_one :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length), rightParam j hj < 1 := by
    intro j hj
    simpa [rightParam] using middleSegments.right_parameter_lt_one j hj
  have one_sub_rightParam_pos :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length),
        0 < 1 - rightParam j hj := by
    intro j hj
    linarith [rightParam_lt_one j hj]
  have segmentLength_pos :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length),
        0 < segmentLength j hj := by
    intro j hj
    let i0 : Fin γ.vertices.length := ⟨j, Nat.lt_of_succ_lt hj⟩
    let i1 : Fin γ.vertices.length := ⟨j + 1, hj⟩
    have hleft : 0 < controlRadii.radius i0 := controlRadii.radius_pos i0
    have hright : 0 < controlRadii.radius i1 := controlRadii.radius_pos i1
    have hsum :
        controlRadii.radius i0 + controlRadii.radius i1 <
          dist γ.vertices[j] γ.vertices[j + 1] := by
      simpa [i0, i1] using controlRadii.adjacent_radii_sum_lt (j := j) hj
    dsimp [segmentLength]
    nlinarith
  have eta_pos : 0 < η := by
    have hlen : 2 ≤ γ.vertices.length := γ.length_ge_two
    have hidx : (0 : ℕ) < γ.vertices.length := by omega
    exact (controlRadii.radius_pos ⟨0, hidx⟩).trans
      (controlRadii.radius_lt_eta ⟨0, hidx⟩)
  have paramSlack_pos :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length),
        0 < paramSlack j hj := by
    intro j hj
    have hden : 0 < 8 * (segmentLength j hj + 1) := by
      have hD : 0 < segmentLength j hj := segmentLength_pos j hj
      positivity
    dsimp [paramSlack]
    exact lt_min (half_pos (leftParam_pos j hj))
      (lt_min (half_pos (one_sub_rightParam_pos j hj))
        (div_pos (forbiddenMargins.margin_pos j hj) hden))
  have paramSlack_le_left_half :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length),
        paramSlack j hj ≤ leftParam j hj / 2 := by
    intro j hj
    dsimp [paramSlack]
    exact min_le_left _ _
  have paramSlack_le_one_sub_right_half :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length),
        paramSlack j hj ≤ (1 - rightParam j hj) / 2 := by
    intro j hj
    dsimp [paramSlack]
    exact le_trans (min_le_right _ _) (min_le_left _ _)
  have paramSlack_le_margin_scaled :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length),
        paramSlack j hj ≤
          forbiddenMargins.margin j hj / (8 * (segmentLength j hj + 1)) := by
    intro j hj
    dsimp [paramSlack]
    exact le_trans (min_le_right _ _) (min_le_right _ _)
  have paramSlack_mul_segmentLength_lt_margin_quarter :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length),
        paramSlack j hj * segmentLength j hj <
          forbiddenMargins.margin j hj / 4 := by
    intro j hj
    exact collar_scaled_eighth_mul_lt_quarter
      (segmentLength_pos j hj) (forbiddenMargins.margin_pos j hj)
      (paramSlack_le_margin_scaled j hj)
  have lowerParam_pos :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length), 0 < lowerParam j hj := by
    intro j hj
    have hle := paramSlack_le_left_half j hj
    have hleft := leftParam_pos j hj
    dsimp [lowerParam]
    nlinarith
  have lowerParam_lt_leftParam :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length),
        lowerParam j hj < leftParam j hj := by
    intro j hj
    dsimp [lowerParam]
    linarith [paramSlack_pos j hj]
  have rightParam_lt_upperParam :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length),
        rightParam j hj < upperParam j hj := by
    intro j hj
    dsimp [upperParam]
    linarith [paramSlack_pos j hj]
  have upperParam_lt_one :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length), upperParam j hj < 1 := by
    intro j hj
    have hle := paramSlack_le_one_sub_right_half j hj
    have hright := rightParam_lt_one j hj
    dsimp [upperParam]
    nlinarith
  have one_sub_upperParam_pos :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length), 0 < 1 - upperParam j hj := by
    intro j hj
    linarith [upperParam_lt_one j hj]
  have initialRayCone_pos :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length), 0 < initialRayCone j hj := by
    intro j hj
    dsimp [initialRayCone]
    by_cases hprev : 0 < j
    · simpa [hprev] using
        (Classical.choose_spec (initialConeAvoidsPreviousRay j hj hprev)).1
    · simp [hprev]
  have terminalRayCone_pos :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length), 0 < terminalRayCone j hj := by
    intro j hj
    dsimp [terminalRayCone]
    by_cases hnext : (j + 1) + 1 < γ.vertices.length
    · simpa [hnext] using
        (Classical.choose_spec (terminalConeAvoidsNextRay j hj hnext)).1
    · simp [hnext]
  have initialPairCone_pos :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length), 0 < initialPairCone j hj := by
    intro j hj
    dsimp [initialPairCone]
    by_cases hprev : 0 < j
    · simpa [hprev] using
        (Classical.choose_spec
          (successiveOutwardConesDisjoint (j - 1)
            (by
              have hj' : j < γ.vertices.length := Nat.lt_of_succ_lt hj
              simpa [Nat.sub_add_cancel (Nat.succ_le_of_lt hprev)] using hj')
            (by
              simpa [Nat.sub_add_cancel (Nat.succ_le_of_lt hprev)] using hj))).1
    · simp [hprev]
  have terminalPairCone_pos :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length), 0 < terminalPairCone j hj := by
    intro j hj
    dsimp [terminalPairCone]
    by_cases hnext : (j + 1) + 1 < γ.vertices.length
    · simpa [hnext] using
        (Classical.choose_spec (successiveOutwardConesDisjoint j hj hnext)).1
    · simp [hnext]
  have initialConeBound_pos :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length), 0 < initialConeBound j hj := by
    intro j hj
    dsimp [initialConeBound]
    exact lt_min (initialRayCone_pos j hj) (initialPairCone_pos j hj)
  have terminalConeBound_pos :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length), 0 < terminalConeBound j hj := by
    intro j hj
    dsimp [terminalConeBound]
    exact lt_min (terminalRayCone_pos j hj) (terminalPairCone_pos j hj)
  have initialAwayExists :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length) (hprev : 0 < j),
        ∃ δ : ℝ, 0 < δ ∧
          ∀ t : ℝ, t ∈ Set.Icc (leftParam j hj) (1 : ℝ) →
            ∀ q, q ∈ segment ℝ γ.vertices[j - 1] γ.vertices[j] →
              δ ≤ dist (AffineMap.lineMap γ.vertices[j] γ.vertices[j + 1] t) q := by
    intro j hj hprev
    exact collar_initialAwayExists γ controlRadii j hj hprev
      (leftParam j hj) (leftParam_pos j hj)
      (le_of_lt ((leftParam_lt_rightParam j hj).trans (rightParam_lt_one j hj)))
  have terminalAwayExists :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length)
        (hnext : (j + 1) + 1 < γ.vertices.length),
          ∃ δ : ℝ, 0 < δ ∧
            ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) (rightParam j hj) →
              ∀ q, q ∈ segment ℝ γ.vertices[j + 1] γ.vertices[j + 2] →
                δ ≤ dist (AffineMap.lineMap γ.vertices[j] γ.vertices[j + 1] t) q := by
    intro j hj hnext
    exact collar_terminalAwayExists γ controlRadii j hj hnext
      (rightParam j hj)
      (le_of_lt ((leftParam_pos j hj).trans (leftParam_lt_rightParam j hj)))
      (rightParam_lt_one j hj)
  have successiveAwayExists :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length)
        (hnext : (j + 1) + 1 < γ.vertices.length),
          ∃ δ : ℝ, 0 < δ ∧
            ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) (rightParam j hj) →
              ∀ u : ℝ, u ∈ Set.Icc (leftParam (j + 1) hnext) (1 : ℝ) →
                δ ≤
                  dist
                    (AffineMap.lineMap γ.vertices[j] γ.vertices[j + 1] t)
                    (AffineMap.lineMap γ.vertices[j + 1] γ.vertices[j + 2] u) := by
    intro j hj hnext
    exact collar_successiveAwayExists γ controlRadii j hj hnext
      (rightParam j hj) (leftParam (j + 1) hnext)
      (le_of_lt ((leftParam_pos j hj).trans (leftParam_lt_rightParam j hj)))
      (rightParam_lt_one j hj) (leftParam_pos (j + 1) hnext)
      (le_of_lt ((leftParam_lt_rightParam (j + 1) hnext).trans
        (rightParam_lt_one (j + 1) hnext)))
  let initialAwaySeparation :
      (j : ℕ) → (hj : j + 1 < γ.vertices.length) → 0 < j → ℝ :=
    fun j hj hprev => Classical.choose (initialAwayExists j hj hprev)
  let terminalAwaySeparation :
      ∀ (j : ℕ), (hj : j + 1 < γ.vertices.length) →
        (j + 1) + 1 < γ.vertices.length → ℝ :=
    fun j hj hnext => Classical.choose (terminalAwayExists j hj hnext)
  let successiveAwaySeparation :
      ∀ (j : ℕ), (hj : j + 1 < γ.vertices.length) →
        (j + 1) + 1 < γ.vertices.length → ℝ :=
    fun j hj hnext => Classical.choose (successiveAwayExists j hj hnext)
  have initialAwaySeparation_pos :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length) (hprev : 0 < j),
        0 < initialAwaySeparation j hj hprev := by
    intro j hj hprev
    simpa [initialAwaySeparation] using
      (Classical.choose_spec (initialAwayExists j hj hprev)).1
  have terminalAwaySeparation_pos :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length)
        (hnext : (j + 1) + 1 < γ.vertices.length),
          0 < terminalAwaySeparation j hj hnext := by
    intro j hj hnext
    simpa [terminalAwaySeparation] using
      (Classical.choose_spec (terminalAwayExists j hj hnext)).1
  have successiveAwaySeparation_pos :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length)
        (hnext : (j + 1) + 1 < γ.vertices.length),
          0 < successiveAwaySeparation j hj hnext := by
    intro j hj hnext
    simpa [successiveAwaySeparation] using
      (Classical.choose_spec (successiveAwayExists j hj hnext)).1
  let initialAwayWidthTerm : (j : ℕ) → j + 1 < γ.vertices.length → ℝ :=
    fun j hj =>
      if hprev : 0 < j then
        initialAwaySeparation j hj hprev / (8 * (segmentLength j hj + 1))
      else
        1
  let terminalAwayWidthTerm : (j : ℕ) → j + 1 < γ.vertices.length → ℝ :=
    fun j hj =>
      if hnext : (j + 1) + 1 < γ.vertices.length then
        terminalAwaySeparation j hj hnext / (8 * (segmentLength j hj + 1))
      else
        1
  let previousSuccessiveAwayWidthTerm :
      (j : ℕ) → j + 1 < γ.vertices.length → ℝ := fun j hj =>
    if hprev : 0 < j then
      successiveAwaySeparation (j - 1)
          (by
            have hj' : j < γ.vertices.length := Nat.lt_of_succ_lt hj
            simpa [Nat.sub_add_cancel (Nat.succ_le_of_lt hprev)] using hj')
          (by
            simpa [Nat.sub_add_cancel (Nat.succ_le_of_lt hprev)] using hj) /
        (16 * (segmentLength j hj + 1))
    else
      1
  let nextSuccessiveAwayWidthTerm :
      (j : ℕ) → j + 1 < γ.vertices.length → ℝ := fun j hj =>
    if hnext : (j + 1) + 1 < γ.vertices.length then
      successiveAwaySeparation j hj hnext / (16 * (segmentLength j hj + 1))
    else
      1
  let halfWidth : (j : ℕ) → j + 1 < γ.vertices.length → ℝ := fun j hj =>
    min
      (min (η / (4 * (segmentLength j hj + 1)))
        (forbiddenMargins.margin j hj / (8 * (segmentLength j hj + 1))))
      (min
        (min (initialConeBound j hj * lowerParam j hj / 2)
          (terminalConeBound j hj * (1 - upperParam j hj) / 2))
        (min
          (min (initialAwayWidthTerm j hj) (terminalAwayWidthTerm j hj))
          (min (previousSuccessiveAwayWidthTerm j hj)
            (nextSuccessiveAwayWidthTerm j hj))))
  let tube : (j : ℕ) → j + 1 < γ.vertices.length →
      Set (EuclideanSpace ℝ (Fin 2)) := fun j hj =>
    {z | ∃ t : ℝ, t ∈ Set.Ioo (lowerParam j hj) (upperParam j hj) ∧
      ∃ s : ℝ, s ∈ Set.Ioo (-(halfWidth j hj)) (halfWidth j hj) ∧
        z =
          AffineMap.lineMap γ.vertices[j] γ.vertices[j + 1] t +
            s • normal j hj}
  let leftHalf : (j : ℕ) → j + 1 < γ.vertices.length →
      Set (EuclideanSpace ℝ (Fin 2)) := fun j hj =>
    {z | ∃ t : ℝ, t ∈ Set.Ioo (lowerParam j hj) (upperParam j hj) ∧
      ∃ s : ℝ, s ∈ Set.Ioo (0 : ℝ) (halfWidth j hj) ∧
        z =
          AffineMap.lineMap γ.vertices[j] γ.vertices[j + 1] t +
            s • normal j hj}
  let rightHalf : (j : ℕ) → j + 1 < γ.vertices.length →
      Set (EuclideanSpace ℝ (Fin 2)) := fun j hj =>
    {z | ∃ t : ℝ, t ∈ Set.Ioo (lowerParam j hj) (upperParam j hj) ∧
      ∃ s : ℝ, s ∈ Set.Ioo (-(halfWidth j hj)) (0 : ℝ) ∧
        z =
          AffineMap.lineMap γ.vertices[j] γ.vertices[j + 1] t +
            s • normal j hj}
  have initialAwayWidthTerm_pos :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length),
        0 < initialAwayWidthTerm j hj := by
    intro j hj
    dsimp [initialAwayWidthTerm]
    by_cases hprev : 0 < j
    · have hden : 0 < 8 * (segmentLength j hj + 1) := by
        have hD := segmentLength_pos j hj
        positivity
      simpa [hprev] using
        div_pos (initialAwaySeparation_pos j hj hprev) hden
    · simp [hprev]
  have terminalAwayWidthTerm_pos :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length),
        0 < terminalAwayWidthTerm j hj := by
    intro j hj
    dsimp [terminalAwayWidthTerm]
    by_cases hnext : (j + 1) + 1 < γ.vertices.length
    · have hden : 0 < 8 * (segmentLength j hj + 1) := by
        have hD := segmentLength_pos j hj
        positivity
      simpa [hnext] using
        div_pos (terminalAwaySeparation_pos j hj hnext) hden
    · simp [hnext]
  have previousSuccessiveAwayWidthTerm_pos :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length),
        0 < previousSuccessiveAwayWidthTerm j hj := by
    intro j hj
    dsimp [previousSuccessiveAwayWidthTerm]
    by_cases hprev : 0 < j
    · have hden : 0 < 16 * (segmentLength j hj + 1) := by
        have hD := segmentLength_pos j hj
        positivity
      simpa [hprev] using
        div_pos
          (successiveAwaySeparation_pos (j - 1)
            (by
              have hj' : j < γ.vertices.length := Nat.lt_of_succ_lt hj
              simpa [Nat.sub_add_cancel (Nat.succ_le_of_lt hprev)] using hj')
            (by
              simpa [Nat.sub_add_cancel (Nat.succ_le_of_lt hprev)] using hj))
          hden
    · simp [hprev]
  have nextSuccessiveAwayWidthTerm_pos :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length),
        0 < nextSuccessiveAwayWidthTerm j hj := by
    intro j hj
    dsimp [nextSuccessiveAwayWidthTerm]
    by_cases hnext : (j + 1) + 1 < γ.vertices.length
    · have hden : 0 < 16 * (segmentLength j hj + 1) := by
        have hD := segmentLength_pos j hj
        positivity
      simpa [hnext] using
        div_pos (successiveAwaySeparation_pos j hj hnext) hden
    · simp [hnext]
  have halfWidth_pos :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length), 0 < halfWidth j hj := by
    intro j hj
    have hD : 0 < segmentLength j hj := segmentLength_pos j hj
    have hden4 : 0 < 4 * (segmentLength j hj + 1) := by positivity
    have hden8 : 0 < 8 * (segmentLength j hj + 1) := by positivity
    have hconeI :
        0 < initialConeBound j hj * lowerParam j hj / 2 := by
      exact half_pos (mul_pos (initialConeBound_pos j hj) (lowerParam_pos j hj))
    have hconeT :
        0 < terminalConeBound j hj * (1 - upperParam j hj) / 2 := by
      exact half_pos
        (mul_pos (terminalConeBound_pos j hj) (one_sub_upperParam_pos j hj))
    dsimp [halfWidth]
    exact lt_min
      (lt_min (div_pos eta_pos hden4)
        (div_pos (forbiddenMargins.margin_pos j hj) hden8))
      (lt_min (lt_min hconeI hconeT)
        (lt_min
          (lt_min (initialAwayWidthTerm_pos j hj) (terminalAwayWidthTerm_pos j hj))
          (lt_min (previousSuccessiveAwayWidthTerm_pos j hj)
            (nextSuccessiveAwayWidthTerm_pos j hj))))
  have halfWidth_le_eta_scaled :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length),
        halfWidth j hj ≤ η / (4 * (segmentLength j hj + 1)) := by
    intro j hj
    dsimp [halfWidth]
    exact le_trans (min_le_left _ _) (min_le_left _ _)
  have halfWidth_le_margin_scaled :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length),
        halfWidth j hj ≤
          forbiddenMargins.margin j hj / (8 * (segmentLength j hj + 1)) := by
    intro j hj
    dsimp [halfWidth]
    exact le_trans (min_le_left _ _) (min_le_right _ _)
  have halfWidth_le_initialConeWidth :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length),
        halfWidth j hj ≤ initialConeBound j hj * lowerParam j hj / 2 := by
    intro j hj
    dsimp [halfWidth]
    exact le_trans (min_le_right _ _)
      (le_trans (min_le_left _ _) (min_le_left _ _))
  have halfWidth_le_terminalConeWidth :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length),
        halfWidth j hj ≤ terminalConeBound j hj * (1 - upperParam j hj) / 2 := by
    intro j hj
    dsimp [halfWidth]
    exact le_trans (min_le_right _ _)
      (le_trans (min_le_left _ _) (min_le_right _ _))
  have halfWidth_le_initialAwayWidthTerm :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length),
        halfWidth j hj ≤ initialAwayWidthTerm j hj := by
    intro j hj
    dsimp [halfWidth]
    exact le_trans (min_le_right _ _)
      (le_trans (min_le_right _ _)
        (le_trans (min_le_left _ _) (min_le_left _ _)))
  have halfWidth_le_terminalAwayWidthTerm :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length),
        halfWidth j hj ≤ terminalAwayWidthTerm j hj := by
    intro j hj
    dsimp [halfWidth]
    exact le_trans (min_le_right _ _)
      (le_trans (min_le_right _ _)
        (le_trans (min_le_left _ _) (min_le_right _ _)))
  have halfWidth_le_previousSuccessiveAwayWidthTerm :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length),
        halfWidth j hj ≤ previousSuccessiveAwayWidthTerm j hj := by
    intro j hj
    dsimp [halfWidth]
    exact le_trans (min_le_right _ _)
      (le_trans (min_le_right _ _)
        (le_trans (min_le_right _ _) (min_le_left _ _)))
  have halfWidth_le_nextSuccessiveAwayWidthTerm :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length),
        halfWidth j hj ≤ nextSuccessiveAwayWidthTerm j hj := by
    intro j hj
    dsimp [halfWidth]
    exact le_trans (min_le_right _ _)
      (le_trans (min_le_right _ _)
        (le_trans (min_le_right _ _) (min_le_right _ _)))
  have halfWidth_lt_initialCone_mul_lowerParam :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length),
        halfWidth j hj < initialConeBound j hj * lowerParam j hj := by
    intro j hj
    have hprod : 0 < initialConeBound j hj * lowerParam j hj :=
      mul_pos (initialConeBound_pos j hj) (lowerParam_pos j hj)
    have hhalf :
        initialConeBound j hj * lowerParam j hj / 2 <
          initialConeBound j hj * lowerParam j hj := by
      nlinarith
    exact lt_of_le_of_lt (halfWidth_le_initialConeWidth j hj) hhalf
  have halfWidth_lt_terminalCone_mul_one_sub_upperParam :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length),
        halfWidth j hj < terminalConeBound j hj * (1 - upperParam j hj) := by
    intro j hj
    have hprod : 0 < terminalConeBound j hj * (1 - upperParam j hj) :=
      mul_pos (terminalConeBound_pos j hj) (one_sub_upperParam_pos j hj)
    have hhalf :
        terminalConeBound j hj * (1 - upperParam j hj) / 2 <
          terminalConeBound j hj * (1 - upperParam j hj) := by
      nlinarith
    exact lt_of_le_of_lt (halfWidth_le_terminalConeWidth j hj) hhalf
  have normal_orthogonal :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length),
        inner ℝ (γ.vertices[j + 1] - γ.vertices[j]) (normal j hj) = 0 := by
    intro j hj
    exact collar_normal_orthogonal γ.vertices[j] γ.vertices[j + 1]
  have normal_norm_eq_segment_length :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length),
        ‖normal j hj‖ = dist γ.vertices[j] γ.vertices[j + 1] := by
    intro j hj
    exact collar_normal_norm_eq_segment_length γ.vertices[j] γ.vertices[j + 1]
  have halfWidth_mul_normal_norm_lt_eta :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length),
        halfWidth j hj * ‖normal j hj‖ < η := by
    intro j hj
    rw [normal_norm_eq_segment_length j hj]
    exact collar_scaled_quarter_mul_lt (segmentLength_pos j hj) eta_pos
      (halfWidth_le_eta_scaled j hj)
  have halfWidth_mul_normal_norm_lt_margin_quarter :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length),
        halfWidth j hj * ‖normal j hj‖ <
          forbiddenMargins.margin j hj / 4 := by
    intro j hj
    rw [normal_norm_eq_segment_length j hj]
    exact collar_scaled_eighth_mul_lt_quarter
      (segmentLength_pos j hj) (forbiddenMargins.margin_pos j hj)
      (halfWidth_le_margin_scaled j hj)
  let tubeFacts : CollarTubeFacts γ controlRadii middleSegments forbiddenMargins
      tube leftHalf rightHalf :=
    collar_tubeFacts γ controlRadii middleSegments forbiddenMargins lowerParam upperParam
      halfWidth paramSlack normal tube leftHalf rightHalf (by intro j hj; rfl)
      (by intro j hj; rfl) (by intro j hj; rfl) (by intro j hj; rfl)
      lowerParam_pos upperParam_lt_one halfWidth_pos
      (by
        intro j hj
        simpa [leftParam] using lowerParam_lt_leftParam j hj)
      (by
        intro j hj
        simpa [rightParam] using rightParam_lt_upperParam j hj)
      paramSlack_pos
      (by
        intro j hj
        simpa [leftParam, rightParam] using leftParam_lt_rightParam j hj)
      (by intro j hj; rfl) (by intro j hj; rfl)
      halfWidth_mul_normal_norm_lt_eta halfWidth_mul_normal_norm_lt_margin_quarter
      (by
        intro j hj
        simpa [segmentLength] using
          paramSlack_mul_segmentLength_lt_margin_quarter j hj)
  let coneFacts : CollarConeFacts γ initialConeBound terminalConeBound normal :=
    collar_coneFacts γ initialConeBound terminalConeBound normal (by intro j hj; rfl)
      initialConeAvoidsPreviousRay terminalConeAvoidsNextRay successiveOutwardConesDisjoint
      (by
        intro j hj hprev
        dsimp [initialConeBound, initialRayCone]
        exact le_trans (min_le_left _ _) (by simp [hprev]))
      (by
        intro j hj hnext
        dsimp [terminalConeBound, terminalRayCone]
        exact le_trans (min_le_left _ _) (by simp [hnext]))
      (by
        intro j hj hnext
        dsimp [terminalConeBound, terminalPairCone]
        exact le_trans (min_le_right _ _) (by simp [hnext]))
      (by
        intro j hj hnext
        dsimp [initialConeBound, initialPairCone]
        exact le_trans (min_le_right _ _) (by simp))
  let centerlineAwayFacts : CollarCenterlineAwayFacts γ controlRadii
      initialAwaySeparation terminalAwaySeparation successiveAwaySeparation :=
    collar_centerlineAwayFacts γ controlRadii leftParam rightParam
      initialAwaySeparation terminalAwaySeparation successiveAwaySeparation
      initialAwayExists terminalAwayExists successiveAwayExists
      (by intro j hj; rfl) (by intro j hj; rfl)
      (by intro j hj hprev; rfl) (by intro j hj hnext; rfl)
      (by intro j hj hnext; rfl)
  let awayWidthFacts : CollarAwayWidthFacts γ halfWidth normal
      initialAwaySeparation terminalAwaySeparation successiveAwaySeparation :=
    collar_awayWidthFacts γ segmentLength halfWidth normal initialAwaySeparation
      terminalAwaySeparation successiveAwaySeparation segmentLength_pos
      (by
        intro j hj
        simpa [segmentLength] using normal_norm_eq_segment_length j hj)
      initialAwaySeparation_pos terminalAwaySeparation_pos successiveAwaySeparation_pos
      (by
        intro j hj hprev
        have hle := halfWidth_le_initialAwayWidthTerm j hj
        dsimp [initialAwayWidthTerm] at hle
        simpa [hprev] using hle)
      (by
        intro j hj hnext
        have hle := halfWidth_le_terminalAwayWidthTerm j hj
        dsimp [terminalAwayWidthTerm] at hle
        simpa [hnext] using hle)
      (by
        intro j hj hnext
        have hle := halfWidth_le_nextSuccessiveAwayWidthTerm j hj
        dsimp [nextSuccessiveAwayWidthTerm] at hle
        simpa [hnext] using hle)
      (by
        intro j hj hnext
        have hle := halfWidth_le_previousSuccessiveAwayWidthTerm (j + 1) hnext
        dsimp [previousSuccessiveAwayWidthTerm] at hle
        simpa [Nat.succ_pos] using hle)
  let orientedTubes :
      PolygonalArcCollarOrientedSeparatedTubeData γ controlRadii middleSegments
        forbiddenMargins :=
    { lowerParam := lowerParam
      upperParam := upperParam
      halfWidth := halfWidth
      normal := normal
      tube := tube
      leftHalf := leftHalf
      rightHalf := rightHalf
      lowerParam_pos := lowerParam_pos
      lowerParam_lt_left_parameter := by
        intro j hj
        simpa [leftParam] using lowerParam_lt_leftParam j hj
      right_parameter_lt_upperParam := by
        intro j hj
        simpa [rightParam] using rightParam_lt_upperParam j hj
      upperParam_lt_one := upperParam_lt_one
      halfWidth_pos := halfWidth_pos
      normal_orthogonal := normal_orthogonal
      normal_norm_eq_segment_length := normal_norm_eq_segment_length
      halfWidth_mul_normal_norm_lt_eta := halfWidth_mul_normal_norm_lt_eta
      halfWidth_mul_normal_norm_lt_margin_quarter :=
        halfWidth_mul_normal_norm_lt_margin_quarter
      lower_parameter_slack_mul_segment_length_lt_margin_quarter := by
        intro j hj
        dsimp [lowerParam, leftParam, segmentLength]
        simpa [sub_sub_cancel] using
          paramSlack_mul_segmentLength_lt_margin_quarter j hj
      upper_parameter_slack_mul_segment_length_lt_margin_quarter := by
        intro j hj
        dsimp [upperParam, rightParam, segmentLength]
        simpa [add_sub_cancel_left] using
          paramSlack_mul_segmentLength_lt_margin_quarter j hj
      tube_eq := by
        intro j hj
        rfl
      leftHalf_eq := by
        intro j hj
        rfl
      rightHalf_eq := by
        intro j hj
        rfl
      middle_subset_tube := tubeFacts.middle_subset_tube
      leftHalf_subset_tube := tubeFacts.leftHalf_subset_tube
      rightHalf_subset_tube := tubeFacts.rightHalf_subset_tube
      tube_subset_eta_neighborhood := tubeFacts.tube_subset_eta_neighborhood
      tube_point_close_to_middle := tubeFacts.tube_point_close_to_middle
      tube_disjoint_nonadjacent_segments := tubeFacts.tube_disjoint_nonadjacent_segments
      tube_disjoint_nonincident_control_disks :=
        tubeFacts.tube_disjoint_nonincident_control_disks
      tube_disjoint_nonadjacent_middle_cores :=
        tubeFacts.tube_disjoint_nonadjacent_middle_cores
      tube_disjoint_nonadjacent_tubes :=
        tubeFacts.tube_disjoint_nonadjacent_tubes
      normal_eq_positive_quarter_turn := by
        intro j hj
        rfl }
  refine ⟨
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
      initial_signed_cone_disjoint_previous_segment :=
        coneFacts.initial_signed_cone_disjoint_previous_segment
      terminal_signed_cone_disjoint_next_segment :=
        coneFacts.terminal_signed_cone_disjoint_next_segment
      successive_positive_negative_cones_disjoint :=
        coneFacts.successive_positive_negative_cones_disjoint
      successive_negative_positive_cones_disjoint :=
        coneFacts.successive_negative_positive_cones_disjoint
      initialAwaySeparation := initialAwaySeparation
      terminalAwaySeparation := terminalAwaySeparation
      successiveAwaySeparation := successiveAwaySeparation
      initialAwaySeparation_pos := initialAwaySeparation_pos
      terminalAwaySeparation_pos := terminalAwaySeparation_pos
      successiveAwaySeparation_pos := successiveAwaySeparation_pos
      initial_centerline_previous_segment_away :=
        centerlineAwayFacts.initial_centerline_previous_segment_away
      terminal_centerline_next_segment_away :=
        centerlineAwayFacts.terminal_centerline_next_segment_away
      successive_centerlines_away := centerlineAwayFacts.successive_centerlines_away
      initial_halfWidth_mul_normal_norm_lt_away_quarter := by
        intro j hj hprev
        simpa [orientedTubes] using
          awayWidthFacts.initial_halfWidth_mul_normal_norm_lt_away_quarter j hj hprev
      terminal_halfWidth_mul_normal_norm_lt_away_quarter := by
        intro j hj hnext
        simpa [orientedTubes] using
          awayWidthFacts.terminal_halfWidth_mul_normal_norm_lt_away_quarter j hj hnext
      successive_halfWidth_normal_sum_lt_away_quarter := by
        intro j hj hnext
        simpa [orientedTubes] using
          awayWidthFacts.successive_halfWidth_normal_sum_lt_away_quarter j hj hnext }⟩
