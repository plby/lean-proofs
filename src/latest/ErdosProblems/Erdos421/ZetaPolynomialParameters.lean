import ErdosProblems.Erdos421.ZetaPolynomialZeroCriterion

/-! # Concrete scales for the polynomial-degree zero detector -/

namespace Erdos421

noncomputable def polynomialDetectorScale (K : ℕ) : ℝ :=
  1 / (131072 * ((K : ℝ) + 1) ^ 3)

noncomputable def polynomialDetectorAmplitude (K : ℕ) : ℝ := ((K : ℝ) + 1) ^ 12

noncomputable def polynomialDetectorRadius (K : ℕ) (B : ℝ) : ℝ :=
  polynomialDetectorScale K /
    (100 * (polynomialDetectorAmplitude K + B * polynomialDetectorScale K + 1))

theorem polynomialDetectorScale_pos (K : ℕ) : 0 < polynomialDetectorScale K := by
  unfold polynomialDetectorScale
  positivity

theorem polynomialDetectorScale_eq (K : ℕ) :
    polynomialDetectorScale K = polynomialLogarithmicExponent K / 2 := by
  unfold polynomialDetectorScale polynomialLogarithmicExponent
  push_cast
  field_simp
  ring

theorem polynomialDetectorScale_le_one (K : ℕ) : polynomialDetectorScale K ≤ 1 := by
  rw [polynomialDetectorScale_eq]
  linarith [polynomialLogarithmicExponent_le_half K]

theorem polynomialDetectorAmplitude_one_le (K : ℕ) : 1 ≤ polynomialDetectorAmplitude K :=
  one_le_pow₀ (by linarith [(Nat.cast_nonneg K : (0 : ℝ) ≤ K)])

theorem polynomialDetectorRadius_pos (K : ℕ) {B : ℝ} (hB : 0 ≤ B) :
    0 < polynomialDetectorRadius K B := by
  have hR := polynomialDetectorScale_pos K
  have hA := polynomialDetectorAmplitude_one_le K
  unfold polynomialDetectorRadius
  positivity

theorem polynomialDetectorRadius_le_inv (K : ℕ) {B : ℝ} (hB : 0 ≤ B) :
    polynomialDetectorRadius K B ≤ 1 / ((K : ℝ) + 1) := by
  have hx : 1 ≤ (K : ℝ) + 1 := by linarith [(Nat.cast_nonneg K : (0 : ℝ) ≤ K)]
  have hR := polynomialDetectorScale_pos K
  have hA := polynomialDetectorAmplitude_one_le K
  have hden : 1 ≤ 100 * (polynomialDetectorAmplitude K + B * polynomialDetectorScale K + 1) :=
    by nlinarith [mul_nonneg hB hR.le]
  calc
    _ ≤ polynomialDetectorScale K := div_le_self hR.le hden
    _ ≤ _ := by
      unfold polynomialDetectorScale
      apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
      have hp : (K : ℝ) + 1 ≤ ((K : ℝ) + 1) ^ 3 := le_self_pow₀ hx (by decide)
      linarith

theorem polynomialDetectorRadius_lower (K : ℕ) {B : ℝ} (hB : 0 ≤ B)
    (hBX : B ≤ (K : ℝ) + 1) :
    1 / (393216000 * ((K : ℝ) + 1) ^ 15) ≤ polynomialDetectorRadius K B / 10 := by
  have hx : 1 ≤ (K : ℝ) + 1 := by linarith [(Nat.cast_nonneg K : (0 : ℝ) ≤ K)]
  have hR := polynomialDetectorScale_pos K
  have hR1 := polynomialDetectorScale_le_one K
  have hA := polynomialDetectorAmplitude_one_le K
  have hXA : (K : ℝ) + 1 ≤ polynomialDetectorAmplitude K := le_self_pow₀ hx (by decide)
  have hBR : B * polynomialDetectorScale K ≤ polynomialDetectorAmplitude K :=
    (mul_le_of_le_one_right hB hR1).trans (hBX.trans hXA)
  have hden : 100 * (polynomialDetectorAmplitude K + B * polynomialDetectorScale K + 1) ≤
      300 * polynomialDetectorAmplitude K := by linarith
  have hb := div_le_div_of_nonneg_left hR.le
    (by positivity : 0 < 100 *
      (polynomialDetectorAmplitude K + B * polynomialDetectorScale K + 1)) hden
  have hh := div_le_div_of_nonneg_right hb (by norm_num : (0 : ℝ) ≤ 10)
  have he : (polynomialDetectorScale K / (300 * polynomialDetectorAmplitude K)) / 10 =
      1 / (393216000 * ((K : ℝ) + 1) ^ 15) := by
    unfold polynomialDetectorScale polynomialDetectorAmplitude
    field_simp
    ring
  rwa [he] at hh

theorem polynomialDetectorRadius_reciprocal_le (K : ℕ) {B : ℝ} (hB : 0 ≤ B)
    (hBX : 1 + 13107200 * (B + 2) ≤ (K : ℝ) + 1) :
    1 + 1 / polynomialDetectorRadius K B ≤ ((K : ℝ) + 1) ^ 16 := by
  have hx : 1 ≤ (K : ℝ) + 1 := by linarith [(Nat.cast_nonneg K : (0 : ℝ) ≤ K)]
  have hR := polynomialDetectorScale_pos K
  have hR1 := polynomialDetectorScale_le_one K
  have hA := polynomialDetectorAmplitude_one_le K
  have hBR : B * polynomialDetectorScale K ≤ B * polynomialDetectorAmplitude K :=
    mul_le_mul_of_nonneg_left (hR1.trans hA) hB
  have hsum : polynomialDetectorAmplitude K + B * polynomialDetectorScale K + 1 ≤
      (B + 2) * polynomialDetectorAmplitude K := by nlinarith
  have he : 1 + 1 / polynomialDetectorRadius K B =
      1 + 100 * (polynomialDetectorAmplitude K + B * polynomialDetectorScale K + 1) /
        polynomialDetectorScale K := by
    unfold polynomialDetectorRadius
    rw [one_div_div]
  rw [he]
  calc
    _ ≤ 1 + 100 * ((B + 2) * polynomialDetectorAmplitude K) / polynomialDetectorScale K :=
      add_le_add le_rfl
        (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hsum (by norm_num)) hR.le)
    _ = 1 + (13107200 * (B + 2)) * ((K : ℝ) + 1) ^ 15 := by
      unfold polynomialDetectorAmplitude polynomialDetectorScale
      rw [div_div_eq_mul_div, div_one]
      ring
    _ ≤ (1 + 13107200 * (B + 2)) * ((K : ℝ) + 1) ^ 15 := by
      have hp : 1 ≤ ((K : ℝ) + 1) ^ 15 := one_le_pow₀ hx
      nlinarith
    _ ≤ ((K : ℝ) + 1) * ((K : ℝ) + 1) ^ 15 :=
      mul_le_mul_of_nonneg_right hBX (by positivity)
    _ = _ := by rw [pow_succ]; ring

end Erdos421
