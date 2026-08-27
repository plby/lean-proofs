import Arxiv.Arxiv2411_18291.RatioPerturbation

/-! # A face-degree critical interval absorbs relative degree and count errors -/

namespace Arxiv2411_18291

theorem face_loss_lower_of_relative_errors {m u h h₀ a b d n y : ℝ}
    (hm : 0 ≤ m) (hu : 0 ≤ u) (hh : 0 < h) (hh₀ : 0 < h₀)
    (ha : 0 ≤ a) (hn : 0 ≤ n) (hy : 0 ≤ y) (hyn : y ≤ n)
    (hdn : d ≤ n) (hcritical : y + (b + 1) * a * n ≤ d)
    (huBound : u ≤ b * a * m) (hhBound : h ≤ (1 + a) * h₀) :
    (m / h₀) * y ≤ d * (m - u) / h := by
  have hdu := mul_le_mul_of_nonneg_right hdn hu
  have hnu := mul_le_mul_of_nonneg_left huBound hn
  have hdm := mul_le_mul_of_nonneg_right hcritical hm
  have hym := mul_le_mul_of_nonneg_right hyn (mul_nonneg ha hm)
  have hN : (1 + a) * m * y ≤ d * (m - u) := by
    nlinarith only [hdu, hnu, hdm, hym]
  have hN' := mul_le_mul_of_nonneg_right hN hh₀.le
  have hh' := mul_le_mul_of_nonneg_left hhBound (mul_nonneg hm hy)
  calc
    _ = (m * y) / h₀ := by ring
    _ ≤ _ := by
      apply (div_le_div_iff₀ hh₀ hh).mpr
      nlinarith only [hN', hh']

end Arxiv2411_18291
