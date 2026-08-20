import ErdosProblems.Erdos733.ST.Preamble

open Classical
noncomputable section

-- [TABLET NODE: PolygonalReplacementStraightSegmentDisjointCutOrder]
lemma PolygonalReplacementStraightSegmentDisjointCutOrder
    {A B z1 z2 u1 v1 u2 v2 : EuclideanSpace ℝ (Fin 2)}
    {rho1 rho2 left1 center1 right1 left2 center2 right2 : ℝ}
    (hdisj : Disjoint (Metric.closedBall z1 rho1) (Metric.closedBall z2 rho2))
    (hcut1 : Metric.closedBall z1 rho1 ∩ segment ℝ A B = segment ℝ u1 v1)
    (hcut2 : Metric.closedBall z2 rho2 ∩ segment ℝ A B = segment ℝ u2 v2)
    (hu1 : u1 = AffineMap.lineMap A B left1)
    (hv1 : v1 = AffineMap.lineMap A B right1)
    (hu2 : u2 = AffineMap.lineMap A B left2)
    (hv2 : v2 = AffineMap.lineMap A B right2)
    (hleft1_center1 : left1 < center1) (hcenter1_right1 : center1 < right1)
    (hcenter_order : center1 < center2)
    (hleft2_center2 : left2 < center2) (hcenter2_right2 : center2 < right2) :
    right1 < left2 := by
-- BODY
  have lineMap_mem_segment_of_between :
      ∀ {alpha beta s : ℝ}, alpha < beta → alpha ≤ s → s ≤ beta →
        AffineMap.lineMap A B s ∈
          segment ℝ (AffineMap.lineMap A B alpha) (AffineMap.lineMap A B beta) := by
    intro alpha beta s halpha_beta halpha_s hs_beta
    rw [segment_eq_image_lineMap]
    let theta : ℝ := (s - alpha) / (beta - alpha)
    refine ⟨theta, ?_, ?_⟩
    · constructor
      · dsimp [theta]
        exact div_nonneg (sub_nonneg.mpr halpha_s) (sub_nonneg.mpr halpha_beta.le)
      · dsimp [theta]
        rw [div_le_one (sub_pos.mpr halpha_beta)]
        linarith
    · ext k
      simp [theta, AffineMap.lineMap_apply_module]
      field_simp [sub_ne_zero.mpr halpha_beta.ne']
      ring
  by_contra hnot
  have hleft2_le_right1 : left2 ≤ right1 := le_of_not_gt hnot
  let s : ℝ := max left1 left2
  have hleft1_right1 : left1 < right1 := hleft1_center1.trans hcenter1_right1
  have hleft2_right2 : left2 < right2 := hleft2_center2.trans hcenter2_right2
  have hs_left1 : left1 ≤ s := le_max_left left1 left2
  have hs_left2 : left2 ≤ s := le_max_right left1 left2
  have hleft1_le_right2 : left1 ≤ right2 := by linarith
  have hs_right1 : s ≤ right1 := max_le (le_of_lt hleft1_right1) hleft2_le_right1
  have hs_right2 : s ≤ right2 := max_le hleft1_le_right2 (le_of_lt hleft2_right2)
  have hp1seg : AffineMap.lineMap A B s ∈ segment ℝ u1 v1 := by
    simpa [hu1, hv1] using
      lineMap_mem_segment_of_between hleft1_right1 hs_left1 hs_right1
  have hp2seg : AffineMap.lineMap A B s ∈ segment ℝ u2 v2 := by
    simpa [hu2, hv2] using
      lineMap_mem_segment_of_between hleft2_right2 hs_left2 hs_right2
  have hp1inter :
      AffineMap.lineMap A B s ∈ Metric.closedBall z1 rho1 ∩ segment ℝ A B := by
    simpa [hcut1] using hp1seg
  have hp2inter :
      AffineMap.lineMap A B s ∈ Metric.closedBall z2 rho2 ∩ segment ℝ A B := by
    simpa [hcut2] using hp2seg
  exact (Set.disjoint_left.mp hdisj) hp1inter.1 hp2inter.1
