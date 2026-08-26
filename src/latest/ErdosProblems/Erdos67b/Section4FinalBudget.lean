import Mathlib.Analysis.Complex.Norm
import Mathlib.Tactic

/-! # The scalar budget for the finite weighted Section 4 contradiction -/

namespace Erdos67b

theorem section4FinalConvolutionBudget
    {H r c ℓ ℓ₀ B M V e T LowSq : ℝ} (Main : ℂ)
    (hH : 0 < H) (hr : 0 < r) (hc : 0 < c) (hℓ : 0 < ℓ)
    (hB : 0 ≤ B) (hV : 0 ≤ V) (he : 0 ≤ e)
    (hT : 0 ≤ T) (hT1 : T ≤ 1) (hℓ₀ : 0 ≤ ℓ₀)
    (hMup : M ≤ 2 * ℓ / r) (hVup : V ≤ 2 * ℓ)
    (hlow : LowSq ≤ ℓ₀ ^ 2 / r + 2 * ℓ₀)
    (hphase : 8 * H * e ≤ c) (hquad : 4 * H * ℓ₀ ≤ c * ℓ)
    (hlinear : 8 * r * H ≤ c * ℓ)
    (htail : 4 * r * H * (1 + 4 * H) ≤ c * ℓ)
    (hmain : c * ℓ / r ≤ ‖Main‖) :
    4 * M * B * V * H + 16 * M * H ^ 3 * e ^ 2 * V +
      16 * H ^ 3 * LowSq + 16 * r * H ^ 3 * (T + 4 * H) ^ 2 ≤
      (16 * B / c ^ 2 + 4) * ‖Main‖ ^ 2 * r * H := by
  let Z : ℝ := c ^ 2 * ℓ ^ 2 * H / r
  have hMV : M * V ≤ 4 * ℓ ^ 2 / r := by
    calc
      M * V ≤ (2 * ℓ / r) * (2 * ℓ) :=
        mul_le_mul hMup hVup hV (by positivity)
      _ = _ := by ring
  have hphaseSq : (8 * H * e) ^ 2 ≤ c ^ 2 :=
    (sq_le_sq₀ (by positivity) hc.le).2 hphase
  have hquadSq : (4 * H * ℓ₀) ^ 2 ≤ (c * ℓ) ^ 2 :=
    (sq_le_sq₀ (by positivity) (by positivity)).2 hquad
  have hlinearProd : (4 * H * ℓ₀) * (8 * r * H) ≤ (c * ℓ) ^ 2 := by
    simpa only [pow_two] using mul_le_mul hquad hlinear (by positivity) (by positivity)
  have htailSq : (4 * r * H * (1 + 4 * H)) ^ 2 ≤ (c * ℓ) ^ 2 :=
    (sq_le_sq₀ (by positivity) (by positivity)).2 htail
  have hfirst : 4 * M * B * V * H ≤ (16 * B / c ^ 2) * Z := by
    have hm := mul_le_mul_of_nonneg_left hMV (show 0 ≤ 4 * B * H by positivity)
    dsimp only [Z]
    calc
      _ ≤ (4 * B * H) * (4 * ℓ ^ 2 / r) := by nlinarith only [hm]
      _ = _ := by field_simp; ring
  have hsecond : 16 * M * H ^ 3 * e ^ 2 * V ≤ Z := by
    have hm := mul_le_mul_of_nonneg_left hMV (show 0 ≤ 16 * H ^ 3 * e ^ 2 by positivity)
    have hs := mul_le_mul_of_nonneg_right hphaseSq (show 0 ≤ ℓ ^ 2 * H / r by positivity)
    dsimp only [Z]
    simp only [div_eq_mul_inv] at hm hs ⊢
    nlinarith only [hm, hs]
  have hthird : 16 * H ^ 3 * (ℓ₀ ^ 2 / r) ≤ Z := by
    have hs := mul_le_mul_of_nonneg_right hquadSq (show 0 ≤ H / r by positivity)
    dsimp only [Z]
    simp only [div_eq_mul_inv] at hs ⊢
    nlinarith only [hs]
  have hfourth : 16 * H ^ 3 * (2 * ℓ₀) ≤ Z := by
    have hs := mul_le_mul_of_nonneg_right hlinearProd (show 0 ≤ H / r by positivity)
    have heq : (4 * H * ℓ₀) * (8 * r * H) * (H / r) = 16 * H ^ 3 * (2 * ℓ₀) := by
      field_simp
      ring
    rw [heq] at hs
    dsimp only [Z]
    simp only [div_eq_mul_inv] at hs ⊢
    nlinarith only [hs]
  have hfifth : 16 * r * H ^ 3 * (T + 4 * H) ^ 2 ≤ Z := by
    have hs := mul_le_mul_of_nonneg_right htailSq (show 0 ≤ H / r by positivity)
    have heq : (4 * r * H * (1 + 4 * H)) ^ 2 * (H / r) =
        16 * r * H ^ 3 * (1 + 4 * H) ^ 2 := by field_simp; ring
    rw [heq] at hs
    calc
      _ ≤ 16 * r * H ^ 3 * (1 + 4 * H) ^ 2 := by gcongr
      _ ≤ Z := by
        dsimp only [Z]
        simp only [div_eq_mul_inv] at hs ⊢
        nlinarith only [hs]
  have hlowBudget : 16 * H ^ 3 * LowSq ≤ 2 * Z := by
    have hl := mul_le_mul_of_nonneg_left hlow (show 0 ≤ 16 * H ^ 3 by positivity)
    nlinarith only [hl, hthird, hfourth]
  have hZ : Z ≤ ‖Main‖ ^ 2 * r * H := by
    have hs := (sq_le_sq₀ (by positivity : 0 ≤ c * ℓ / r) (norm_nonneg Main)).2 hmain
    have hm := mul_le_mul_of_nonneg_right hs (show 0 ≤ r * H by positivity)
    have heq : (c * ℓ / r) ^ 2 * (r * H) = Z := by dsimp [Z]; field_simp
    rw [heq] at hm
    simpa only [mul_assoc] using hm
  calc
    _ ≤ (16 * B / c ^ 2 + 4) * Z := by
      nlinarith only [hfirst, hsecond, hlowBudget, hfifth]
    _ ≤ (16 * B / c ^ 2 + 4) * (‖Main‖ ^ 2 * r * H) :=
      mul_le_mul_of_nonneg_left hZ (by positivity)
    _ = _ := by ring

end Erdos67b
