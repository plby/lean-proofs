import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-! # Normalizing explicit higher large-value inequalities -/

namespace Erdos421

theorem halasz_clear_threshold {V K G T : ℝ} (hV : 0 < V) (hK : 0 < K) (k : ℕ) :
    (G / (V ^ k / K) ^ 2 + 1280 ^ 2 * G ^ 3 * T / (V ^ k / K) ^ 6) * V ^ (6 * k) =
      G * K ^ 2 * V ^ (4 * k) + 1280 ^ 2 * G ^ 3 * T * K ^ 6 := by
  have hVk : V ^ k ≠ 0 := (pow_pos hV _).ne'
  have hv6 : V ^ (6 * k) = (V ^ k) ^ 6 := by rw [← pow_mul]; congr 1; omega
  have hv4 : V ^ (4 * k) = (V ^ k) ^ 4 := by rw [← pow_mul]; congr 1; omega
  rw [hv6, hv4]
  field_simp

theorem largeValue_normalized_halasz {R M V K G T C D E L : ℝ}
    (hM : 0 < M) (hV : 0 < V) (hK : 0 < K) (hG : 0 ≤ G) (hT : 0 ≤ T)
    (hD : 0 ≤ D) (hE : 0 ≤ E) (hKL : K ≤ L) (k : ℕ)
    (henergy : G * M ^ k ≤ D) (hprefactor : C ≤ E * M ^ k)
    (hbound : R ≤ C * (G / (V ^ k / K) ^ 2 +
      1280 ^ 2 * G ^ 3 * T / (V ^ k / K) ^ 6)) :
    R * (M * V ^ 2) ^ (3 * k) ≤
      (E * D * L ^ 2 + 1280 ^ 2 * E * D ^ 3 * L ^ 6) *
        (M ^ k * (M * V ^ 2) ^ (2 * k) + M ^ k * T) := by
  have hL : 0 < L := hK.trans_le hKL
  have hstep := mul_le_mul_of_nonneg_right hbound (pow_nonneg hV.le (6 * k))
  rw [mul_assoc C, halasz_clear_threshold hV hK k] at hstep
  have hstep' := mul_le_mul_of_nonneg_right hstep (pow_nonneg hM.le (3 * k))
  have hright : C * (G * K ^ 2 * V ^ (4 * k) + 1280 ^ 2 * G ^ 3 * T * K ^ 6) * M ^ (3 * k) ≤
      (E * M ^ k) * (G * K ^ 2 * V ^ (4 * k) + 1280 ^ 2 * G ^ 3 * T * K ^ 6) * M ^ (3 * k) := by
    gcongr
  have hidentity : (E * M ^ k) *
      (G * K ^ 2 * V ^ (4 * k) + 1280 ^ 2 * G ^ 3 * T * K ^ 6) * M ^ (3 * k) =
      E * (G * M ^ k) * K ^ 2 * (M ^ k * (M * V ^ 2) ^ (2 * k)) +
        1280 ^ 2 * E * (G * M ^ k) ^ 3 * K ^ 6 * (M ^ k * T) := by
    simp only [mul_pow, ← pow_mul]
    ring
  have hmono : E * (G * M ^ k) * K ^ 2 * (M ^ k * (M * V ^ 2) ^ (2 * k)) +
      1280 ^ 2 * E * (G * M ^ k) ^ 3 * K ^ 6 * (M ^ k * T) ≤
      E * D * L ^ 2 * (M ^ k * (M * V ^ 2) ^ (2 * k)) +
        1280 ^ 2 * E * D ^ 3 * L ^ 6 * (M ^ k * T) := by
    gcongr
  have hsum : E * D * L ^ 2 * (M ^ k * (M * V ^ 2) ^ (2 * k)) +
      1280 ^ 2 * E * D ^ 3 * L ^ 6 * (M ^ k * T) ≤
      (E * D * L ^ 2 + 1280 ^ 2 * E * D ^ 3 * L ^ 6) *
        (M ^ k * (M * V ^ 2) ^ (2 * k) + M ^ k * T) := by
    nlinarith [mul_nonneg (show 0 ≤ E * D * L ^ 2 by positivity)
      (show 0 ≤ M ^ k * T by positivity),
      mul_nonneg (show 0 ≤ 1280 ^ 2 * E * D ^ 3 * L ^ 6 by positivity)
        (show 0 ≤ M ^ k * (M * V ^ 2) ^ (2 * k) by positivity)]
  have heleft : R * V ^ (6 * k) * M ^ (3 * k) = R * (M * V ^ 2) ^ (3 * k) := by
    simp only [mul_pow, ← pow_mul]
    ring
  rw [heleft] at hstep'
  exact hstep'.trans (hright.trans (hidentity.le.trans (hmono.trans hsum)))

theorem largeValue_normalized_mean {R M V C D T : ℝ} (hM : 0 < M) (k : ℕ)
    (hbound : R * V ^ (2 * k) ≤ C * (T + M ^ k) * (D / M ^ k)) :
    R * (M * V ^ 2) ^ k ≤ (C * D) * (M ^ k + T) := by
  have hb := mul_le_mul_of_nonneg_right hbound (pow_nonneg hM.le k)
  have heleft : R * V ^ (2 * k) * M ^ k = R * (M * V ^ 2) ^ k := by
    simp only [mul_pow, ← pow_mul]
    ring
  have heright : C * (T + M ^ k) * (D / M ^ k) * M ^ k = (C * D) * (M ^ k + T) := by
    have hMk : M ^ k ≠ 0 := (pow_pos hM _).ne'
    field_simp
    ring
  rwa [heleft, heright] at hb

end Erdos421
