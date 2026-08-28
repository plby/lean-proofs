import Wikipedia.NoExoticSixSphere.RoundedCornerGraph

/-! # Exact interval cut out by a sufficiently wide rounded-corner window -/

open Set

namespace NoExoticSixSphere.SmoothCornerRounding

variable (χ : ContDiffBump (0 : ℝ))

theorem graph_window_iff {δ γ u : ℝ} (hδ : 2 * χ.rOut < δ) (hγ : 2 * χ.rOut < γ) :
    -δ < graphHeight χ u ∧ -γ < graphRadial χ u ↔ u ∈ Ioo (-δ) γ := by
  have hdiff := graph_difference χ u
  change graphHeight χ u - graphRadial χ u = u at hdiff
  constructor
  · rintro ⟨ht, hq⟩
    exact ⟨by linarith [graphRadial_nonpos χ u], by linarith [graphHeight_nonpos χ u]⟩
  · intro hu
    by_cases hl : u ≤ -χ.rOut
    · rw [graphHeight_of_left χ hl, graphRadial_of_left χ hl]
      exact ⟨hu.1, by linarith [χ.rOut_pos]⟩
    · by_cases hr : χ.rOut ≤ u
      · rw [graphHeight_of_right χ hr, graphRadial_of_right χ hr]
        exact ⟨by linarith [χ.rOut_pos], by linarith [hu.2]⟩
      · have ha : |u| < χ.rOut := abs_lt.mpr ⟨lt_of_not_ge hl, lt_of_not_ge hr⟩
        have hb := roundedAbs_le χ u
        constructor
        · dsimp [graphHeight]
          linarith [χ.rIn_lt_rOut]
        · dsimp [graphRadial]
          linarith [χ.rIn_lt_rOut]

end NoExoticSixSphere.SmoothCornerRounding
