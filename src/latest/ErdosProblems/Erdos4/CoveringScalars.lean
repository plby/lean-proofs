import ErdosProblems.Erdos4.CoveringError

/-! Scalar inequalities for the outer conditional covering estimate. -/

namespace Erdos4.CoveringScalars

theorem exposure_ratio_le {C D M s σ τ : ℝ}
    (hC : 0 ≤ C) (hD : 0 < D) (hM : 0 < M) (hs : 0 < s)
    (hσ : σ ≤ C / s) (hτ : M / (D * s) ≤ τ) :
    σ / τ ≤ C * D / M := by
  have hτpos : 0 < τ := (div_pos hM (mul_pos hD hs)).trans_le hτ
  calc
    _ ≤ (C / s) / τ := div_le_div_of_nonneg_right hσ hτpos.le
    _ ≤ (C / s) / (M / (D * s)) :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) hτ
    _ = _ := by field_simp

theorem collision_ratio_le (j : ℕ) {c D M s σ τ B α : ℝ}
    (hc : 0 < c) (hD : 0 < D) (hM : 0 < M) (hs : 0 < s)
    (hσ : c / s ≤ σ) (hτ : M / (D * s) ≤ τ) (hB : 0 ≤ B) (hα : 0 ≤ α) :
    B * α / (σ ^ j * τ) ≤ (B * D / (c ^ j * M)) * (α * s ^ (j + 1)) := by
  have hσpos : 0 < σ := (div_pos hc hs).trans_le hσ
  have hden : (c / s) ^ j * (M / (D * s)) ≤ σ ^ j * τ :=
    mul_le_mul (pow_le_pow_left₀ (by positivity) hσ j) hτ (by positivity) (by positivity)
  calc
    _ ≤ B * α / ((c / s) ^ j * (M / (D * s))) :=
      div_le_div_of_nonneg_left (mul_nonneg hB hα) (by positivity) hden
    _ = _ := by rw [div_pow, pow_succ]; field_simp

end Erdos4.CoveringScalars
