import ErdosProblems.Erdos733.ST.Preamble

open Classical
noncomputable section

-- [TABLET NODE: StraightSegmentEndpointSphereBranch]
lemma StraightSegmentEndpointSphereBranch {a b : EuclideanSpace ℝ (Fin 2)}
    (hab : a ≠ b) {ρ : ℝ} (hρpos : 0 < ρ) (hρlt : ρ < dist a b) :
    ∃! p : EuclideanSpace ℝ (Fin 2),
      p ∈ Metric.sphere a ρ ∧ p ∈ segment ℝ a b := by
-- BODY
  have dist_left_lineMap :
      ∀ {t : ℝ}, 0 ≤ t →
        dist a (AffineMap.lineMap a b t) = t * dist a b := by
    intro t ht
    have h :
        dist a (AffineMap.lineMap a b t) = |t| * dist a b := by
      rw [dist_eq_norm_vsub (EuclideanSpace ℝ (Fin 2))]
      rw [AffineMap.left_vsub_lineMap, norm_smul, Real.norm_eq_abs]
      rw [show ‖a -ᵥ b‖ = dist a b by
        rw [dist_eq_norm_vsub (EuclideanSpace ℝ (Fin 2))]]
    simpa [abs_of_nonneg ht] using h
  let t : ℝ := ρ / dist a b
  have hdist_pos : 0 < dist a b := dist_pos.mpr hab
  have ht_nonneg : 0 ≤ t := by
    dsimp [t]
    exact div_nonneg hρpos.le hdist_pos.le
  have ht_le : t ≤ 1 := by
    dsimp [t]
    exact (div_le_one hdist_pos).2 hρlt.le
  refine ⟨AffineMap.lineMap a b t, ?_, ?_⟩
  · constructor
    · rw [Metric.mem_sphere, dist_comm, dist_left_lineMap ht_nonneg]
      dsimp [t]
      field_simp [hdist_pos.ne']
    · rw [segment_eq_image_lineMap]
      exact ⟨t, ⟨ht_nonneg, ht_le⟩, rfl⟩
  · intro q hq
    rcases hq with ⟨hqSphere, hqSegment⟩
    rw [segment_eq_image_lineMap] at hqSegment
    rcases hqSegment with ⟨s, hs, rfl⟩
    have hs_nonneg : 0 ≤ s := hs.1
    have hsphere_eq : dist a (AffineMap.lineMap a b s) = ρ := by
      simpa [dist_comm] using Metric.mem_sphere.mp hqSphere
    rw [dist_left_lineMap hs_nonneg] at hsphere_eq
    have hs_eq : s = t := by
      dsimp [t]
      exact (eq_div_iff hdist_pos.ne').2 hsphere_eq
    rw [hs_eq]
