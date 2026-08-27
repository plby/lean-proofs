import Arxiv.Arxiv2411_18291.RatioPerturbation

/-! # Ratio errors with the actual denominator factor retained -/

namespace Arxiv2411_18291

theorem reciprocal_error_of_denominator_factor {h h₀ v B : ℝ}
    (hh : 0 < h) (hh₀ : 0 < h₀) (hd : |h - h₀| ≤ v) (hB : h₀ ≤ B * h) :
    |1 / h - 1 / h₀| ≤ B * v / h₀ ^ 2 := by
  have hv0 : 0 ≤ v := (abs_nonneg _).trans hd
  have heq : 1 / h - 1 / h₀ = (h₀ - h) / (h * h₀) := by field_simp
  rw [heq, abs_div, abs_of_pos (mul_pos hh hh₀)]
  calc
    _ ≤ v / (h * h₀) :=
      div_le_div_of_nonneg_right (by simpa only [abs_sub_comm] using hd) (by positivity)
    _ ≤ _ := by
      apply (div_le_div_iff₀ (mul_pos hh hh₀) (pow_pos hh₀ 2)).mpr
      have hm := mul_le_mul_of_nonneg_left hB (mul_nonneg hv0 hh₀.le)
      nlinarith only [hm]

theorem ratio_error_of_denominator_factor {N N₀ h h₀ E v B : ℝ}
    (hN₀ : 0 ≤ N₀) (hh : 0 < h) (hh₀ : 0 < h₀)
    (hN : |N - N₀| ≤ E) (hd : |h - h₀| ≤ v) (hB : h₀ ≤ B * h) :
    |N / h - N₀ / h₀| ≤ B * E / h₀ + B * N₀ * v / h₀ ^ 2 := by
  have hE : 0 ≤ E := (abs_nonneg _).trans hN
  have hEdiv : E / h ≤ B * E / h₀ := by
    apply (div_le_div_iff₀ hh hh₀).mpr
    have hm := mul_le_mul_of_nonneg_left hB hE
    nlinarith only [hm]
  calc
    _ = |(N - N₀) / h + N₀ * (1 / h - 1 / h₀)| := by congr 1; ring
    _ ≤ |(N - N₀) / h| + |N₀ * (1 / h - 1 / h₀)| := abs_add_le _ _
    _ = |N - N₀| / h + N₀ * |1 / h - 1 / h₀| := by
      rw [abs_div, abs_of_pos hh, abs_mul, abs_of_nonneg hN₀]
    _ ≤ E / h + N₀ * (B * v / h₀ ^ 2) :=
      add_le_add (div_le_div_of_nonneg_right hN hh.le)
        (mul_le_mul_of_nonneg_left
          (reciprocal_error_of_denominator_factor hh hh₀ hd hB) hN₀)
    _ ≤ B * E / h₀ + N₀ * (B * v / h₀ ^ 2) := add_le_add hEdiv le_rfl
    _ = _ := by ring

end Arxiv2411_18291
