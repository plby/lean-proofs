import ErdosProblems.Erdos733.ST.Preamble

open Classical
noncomputable section

-- [TABLET NODE: BigonRerouteLocalSegmentDirection]
lemma BigonRerouteLocalSegmentDirection
    (a b c d z : EuclideanSpace ℝ (Fin 2))
    (hab : a ≠ b)
    (hzab : z ∈ segment ℝ a b)
    (hzcd : z ∈ segment ℝ c d)
    (r : ℝ) (hr : 0 < r)
    (hlocal : Metric.ball z r ∩ segment ℝ a b ⊆ segment ℝ c d) :
    ∃ t : ℝ, t ≠ 0 ∧ b - a = t • (d - c) := by
-- BODY
  rw [segment_eq_image_lineMap] at hzab
  rcases hzab with ⟨u, hu, hzu⟩
  have hpre : (AffineMap.lineMap a b) ⁻¹' Metric.ball z r ∈ nhds u := by
    apply AffineMap.lineMap_continuous.continuousAt
    have hzball : z ∈ Metric.ball z r := Metric.mem_ball_self hr
    exact Metric.isOpen_ball.mem_nhds (by simpa [hzu] using hzball)
  rcases Metric.mem_nhds_iff.mp hpre with ⟨eps, heps, hepsSub⟩
  let delta : ℝ := min (eps / 2) (1 / 2)
  have hdelta : 0 < delta := by
    exact lt_min (half_pos heps) (by norm_num)
  let v : ℝ := if u < 1 then u + min delta ((1 - u) / 2) else u - delta
  have hv_ne : v ≠ u := by
    dsimp [v]
    split_ifs with hu1
    · have hminpos : 0 < min delta ((1 - u) / 2) := by
        exact lt_min hdelta (half_pos (sub_pos.mpr hu1))
      linarith
    · linarith
  have hvIcc : v ∈ Set.Icc (0 : ℝ) 1 := by
    dsimp [v]
    split_ifs with hu1
    · constructor
      · have hminnonneg : 0 ≤ min delta ((1 - u) / 2) :=
          le_of_lt (lt_min hdelta (half_pos (sub_pos.mpr hu1)))
        linarith [hu.1]
      · have hle := min_le_right delta ((1 - u) / 2)
        linarith
    · have hu1' : u = 1 := le_antisymm hu.2 (le_of_not_gt hu1)
      subst u
      constructor
      · have hdelta_le : delta ≤ 1 / 2 := min_le_right _ _
        linarith
      · linarith
  have hvNear : v ∈ Metric.ball u eps := by
    rw [Metric.mem_ball, Real.dist_eq]
    dsimp [v]
    split_ifs with hu1
    · have hminpos : 0 < min delta ((1 - u) / 2) := by
        exact lt_min hdelta (half_pos (sub_pos.mpr hu1))
      rw [abs_of_nonneg (by linarith : 0 ≤ u + min delta ((1 - u) / 2) - u)]
      have hle : min delta ((1 - u) / 2) ≤ delta := min_le_left _ _
      have hdelta_eps : delta < eps :=
        (min_le_left (eps / 2) (1 / 2)).trans_lt (half_lt_self heps)
      linarith
    · rw [abs_of_nonpos (by linarith : u - delta - u ≤ 0)]
      have hdelta_eps : delta < eps :=
        (min_le_left (eps / 2) (1 / 2)).trans_lt (half_lt_self heps)
      linarith
  let w := AffineMap.lineMap a b v
  have hwBall : w ∈ Metric.ball z r := hepsSub hvNear
  have hwab : w ∈ segment ℝ a b := by
    rw [segment_eq_image_lineMap]
    exact ⟨v, hvIcc, rfl⟩
  have hwcd : w ∈ segment ℝ c d := hlocal ⟨hwBall, hwab⟩
  have hw_ne_z : w ≠ z := by
    intro hwz
    apply hv_ne
    apply AffineMap.lineMap_injective ℝ hab
    simpa [w, hzu] using hwz
  rw [segment_eq_image_lineMap] at hzcd hwcd
  rcases hzcd with ⟨s, _hs, hzs⟩
  rcases hwcd with ⟨q, _hq, hwq⟩
  have hvu_ne : v - u ≠ 0 := sub_ne_zero.mpr hv_ne
  have hqs_ne : q - s ≠ 0 := by
    intro hzero
    have hqs : q = s := sub_eq_zero.mp hzero
    apply hw_ne_z
    calc
      w = AffineMap.lineMap c d q := hwq.symm
      _ = AffineMap.lineMap c d s := by rw [hqs]
      _ = z := hzs
  refine ⟨(v - u)⁻¹ * (q - s), mul_ne_zero (inv_ne_zero hvu_ne) hqs_ne, ?_⟩
  have hdiff_ab : w - z = (v - u) • (b - a) := by
    rw [← hzu]
    dsimp [w]
    simp only [AffineMap.lineMap_apply_module]
    module
  have hdiff_cd : w - z = (q - s) • (d - c) := by
    rw [← hzs, ← hwq]
    simp only [AffineMap.lineMap_apply_module]
    module
  calc
    b - a = (v - u)⁻¹ • ((v - u) • (b - a)) := by simp [hvu_ne]
    _ = (v - u)⁻¹ • (w - z) := by rw [← hdiff_ab]
    _ = (v - u)⁻¹ • ((q - s) • (d - c)) := by rw [hdiff_cd]
    _ = ((v - u)⁻¹ * (q - s)) • (d - c) := by rw [mul_smul]
