import Wikipedia.NoExoticSixSphere.RoundedCornerGraphWindow

/-! # Exact far-end tests for the rounded boundary graph -/

namespace NoExoticSixSphere.SmoothCornerRounding

variable (χ : ContDiffBump (0 : ℝ))

theorem graphHeight_lt_neg_twice_outer_iff (u : ℝ) :
    graphHeight χ u < -2 * χ.rOut ↔ u < -2 * χ.rOut := by
  by_cases hl : u ≤ -χ.rOut
  · rw [graphHeight_of_left χ hl]
  · by_cases hr : χ.rOut ≤ u
    · rw [graphHeight_of_right χ hr]
      exact iff_of_false (by linarith [χ.rOut_pos]) (by linarith [χ.rOut_pos])
    · have ha : |u| < χ.rOut := abs_lt.mpr ⟨lt_of_not_ge hl, lt_of_not_ge hr⟩
      have hb := roundedAbs_le χ u
      have ht : -2 * χ.rOut < graphHeight χ u := by
        dsimp [graphHeight]
        linarith [χ.rIn_lt_rOut, χ.rOut_pos]
      exact iff_of_false (not_lt.mpr ht.le) (by linarith [χ.rOut_pos])

theorem graphRadial_lt_neg_twice_outer_iff (u : ℝ) :
    graphRadial χ u < -2 * χ.rOut ↔ 2 * χ.rOut < u := by
  by_cases hl : u ≤ -χ.rOut
  · rw [graphRadial_of_left χ hl]
    exact iff_of_false (by linarith [χ.rOut_pos]) (by linarith [χ.rOut_pos])
  · by_cases hr : χ.rOut ≤ u
    · rw [graphRadial_of_right χ hr]
      constructor <;> intro h <;> linarith
    · have ha : |u| < χ.rOut := abs_lt.mpr ⟨lt_of_not_ge hl, lt_of_not_ge hr⟩
      have hb := roundedAbs_le χ u
      have ht : -2 * χ.rOut < graphRadial χ u := by
        dsimp [graphRadial]
        linarith [χ.rIn_lt_rOut, χ.rOut_pos]
      exact iff_of_false (not_lt.mpr ht.le) (by linarith [χ.rOut_pos])

end NoExoticSixSphere.SmoothCornerRounding
