import StackExchange.Puzzling139335.N4TwoOneOne.SourceBounds

/-! # Parameters for the aligned outgoing contradiction -/

namespace Puzzling139335.N4TwoOneOne.AlignedOutgoing

noncomputable section

variable {d : SquareDissection} {θ u v : ℝ}

theorem sin_gt_half (h : SourceData d θ u v) : (1 / 2 : ℝ) < Real.sin θ := by
  have hc := mul_self_le_mul_self h.cos_nonneg h.cos_le_half
  by_contra hnot
  have hs := mul_self_le_mul_self h.sin_nonneg (le_of_not_gt hnot)
  nlinarith only [hc, hs, Real.sin_sq_add_cos_sq θ]

theorem height_nonneg (h : SourceData d θ u v) :
    0 ≤ u * Real.sin θ + v * Real.cos θ :=
  add_nonneg (mul_nonneg (h.cos_nonneg.trans h.cos_le_u) h.sin_nonneg)
    (mul_nonneg h.v_nonneg h.cos_nonneg)

theorem start_above_height (h : SourceData d θ u v) :
    u * Real.sin θ + v * Real.cos θ < 1 - v :=
  h.height_coefficient_le_half.trans_lt
    ((sin_gt_half h).trans_le (by linarith [h.v_le_one_sub_sin]))

theorem cos_pos (h : SourceData d θ u v) (hθ : θ < Real.pi / 2) :
    0 < Real.cos θ :=
  Real.cos_pos_of_mem_Ioo ⟨by linarith [h.angle_nonneg, Real.pi_pos], hθ⟩

/-- A short positive displacement along either reflected base line remains
above the source and moves less than one third horizontally. -/
theorem exists_short_step {H c s v : ℝ} (hH0 : 0 ≤ H)
    (hstart : H < 1 - v) (hv : 0 < v)
    (hc : 0 < c) (hc_half : c ≤ 1 / 2) (hs : 0 ≤ s) (hs_one : s ≤ 1) :
    ∃ t : ℝ, 0 < t ∧ t < 1 ∧ 0 < c * t ∧ c * t < 1 / 3 ∧
      H < 1 - v - s * t ∧ 1 - v - s * t < 1 := by
  let t : ℝ := (1 - v - H) / 2
  have ht : 0 < t := by dsimp [t]; linarith
  have ht_half : t < 1 / 2 := by dsimp [t]; linarith
  have hct := mul_le_mul_of_nonneg_right hc_half ht.le
  have hst := mul_le_mul_of_nonneg_right hs_one ht.le
  have hst0 := mul_nonneg hs ht.le
  refine ⟨t, ht, by linarith, mul_pos hc ht, by linarith, ?_, by linarith⟩
  dsimp [t] at hst ⊢
  linarith

end

end Puzzling139335.N4TwoOneOne.AlignedOutgoing
