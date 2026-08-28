import Wikipedia.HopfProblem.OrbitPairHomotopyFiberTransportTimes

/-!
# A continuous sweep between adjacent sides of the unit square

Each intermediate ray ends on the top or right side of the square. Therefore
a map constant on those two sides turns this sweep into a based homotopy
between its bottom and left sides, without reparameterization at either end.
-/

noncomputable section

namespace Wikipedia.HopfProblem.OrbitPair.HomotopyCorner

def scale (r : unitInterval) : ℝ := max (1 - (r : ℝ)) (r : ℝ)

theorem scale_pos (r : unitInterval) : 0 < scale r := by
  have h₁ := le_max_left (1 - (r : ℝ)) (r : ℝ)
  have h₂ := le_max_right (1 - (r : ℝ)) (r : ℝ)
  unfold scale
  linarith

theorem continuous_scale : Continuous scale :=
  (continuous_const.sub continuous_subtype_val).max continuous_subtype_val

def sweep (r t : unitInterval) : unitInterval × unitInterval :=
  (⟨(t : ℝ) * (1 - (r : ℝ)) / scale r, by
    constructor
    · exact div_nonneg (mul_nonneg t.property.1 (sub_nonneg.mpr r.property.2))
        (scale_pos r).le
    · apply (div_le_one (scale_pos r)).mpr
      exact (mul_le_of_le_one_left (sub_nonneg.mpr r.property.2) t.property.2).trans
        (le_max_left _ _)⟩,
    ⟨(t : ℝ) * (r : ℝ) / scale r, by
      constructor
      · exact div_nonneg (mul_nonneg t.property.1 r.property.1) (scale_pos r).le
      · apply (div_le_one (scale_pos r)).mpr
        exact (mul_le_of_le_one_left r.property.1 t.property.2).trans (le_max_right _ _)⟩)

theorem continuous_sweep :
    Continuous (fun z : unitInterval × unitInterval ↦ sweep z.1 z.2) := by
  have hr : Continuous (fun z : unitInterval × unitInterval ↦ (z.1 : ℝ)) :=
    continuous_subtype_val.comp continuous_fst
  have ht : Continuous (fun z : unitInterval × unitInterval ↦ (z.2 : ℝ)) :=
    continuous_subtype_val.comp continuous_snd
  have hscale : Continuous (fun z : unitInterval × unitInterval ↦ scale z.1) :=
    continuous_scale.comp continuous_fst
  exact (((ht.mul (continuous_const.sub hr)).div hscale
    (fun z ↦ (scale_pos z.1).ne')).subtype_mk _).prodMk
      (((ht.mul hr).div hscale (fun z ↦ (scale_pos z.1).ne')).subtype_mk _)

theorem sweep_zero (t : unitInterval) : sweep 0 t = (t, 0) := by
  ext <;> simp [sweep, scale]

theorem sweep_one (t : unitInterval) : sweep 1 t = (0, t) := by
  ext <;> simp [sweep, scale]

theorem sweep_start (r : unitInterval) : sweep r 0 = (0, 0) := by
  ext <;> simp [sweep]

theorem sweep_end (r : unitInterval) : (sweep r 1).1 = 1 ∨ (sweep r 1).2 = 1 := by
  by_cases h : (r : ℝ) ≤ 1 - (r : ℝ)
  · left
    have hpos : 0 < 1 - (r : ℝ) := by
      simpa only [scale, max_eq_left h] using scale_pos r
    apply Subtype.ext
    simp [sweep, scale, max_eq_left h, hpos.ne']
  · right
    have h' : 1 - (r : ℝ) ≤ (r : ℝ) := (lt_of_not_ge h).le
    have hpos : 0 < (r : ℝ) := by
      simpa only [scale, max_eq_right h'] using scale_pos r
    apply Subtype.ext
    simp [sweep, scale, max_eq_right h', hpos.ne']

end Wikipedia.HopfProblem.OrbitPair.HomotopyCorner
