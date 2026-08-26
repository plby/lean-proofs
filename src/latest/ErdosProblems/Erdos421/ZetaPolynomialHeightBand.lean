import ErdosProblems.Erdos421.ZetaPolynomialExponential

/-! # Nonvanishing on polynomial logarithmic height bands -/

namespace Erdos421

open Complex

theorem polynomialDetector_height_threshold {K : ℕ} (hK : 2 ≤ K) :
    (2 : ℝ) ^ K + polynomialDetectorScale K ≤ Real.exp ((K : ℝ) ^ 16) := by
  have hKR : (2 : ℝ) ≤ K := by exact_mod_cast hK
  have hK0 : (0 : ℝ) ≤ K := Nat.cast_nonneg K
  have hexp : 1 ≤ Real.exp (K : ℝ) := Real.one_le_exp_iff.mpr hK0
  have htwo : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hp : (K : ℝ) + 1 ≤ (K : ℝ) ^ 16 := by
    have hsq : (K : ℝ) + 1 ≤ (K : ℝ) ^ 2 := by nlinarith
    exact hsq.trans (pow_le_pow_right₀ (by linarith) (by decide : 2 ≤ 16))
  calc
    _ ≤ Real.exp (K : ℝ) + 1 :=
      add_le_add (two_pow_le_real_exp K) (polynomialDetectorScale_le_one K)
    _ ≤ Real.exp (K : ℝ) * Real.exp 1 := by
      nlinarith [mul_le_mul_of_nonneg_left htwo (Real.exp_pos (K : ℝ)).le]
    _ = Real.exp ((K : ℝ) + 1) := (Real.exp_add _ _).symm
    _ ≤ _ := Real.exp_le_exp.mpr hp

theorem exists_riemannZeta_polynomial_height_band :
    ∃ K₀ : ℕ, 7228 ≤ K₀ ∧ ∀ K : ℕ, K₀ ≤ K → ∀ t β : ℝ, 1 < |t| →
      (K : ℝ) ^ 16 ≤ Real.log |t| → Real.log |t| ≤ ((K : ℝ) + 1) ^ 16 →
      1 - 1 / (393216000 * ((K : ℝ) + 1) ^ 15) ≤ β →
        riemannZeta ((β : ℂ) + t * I) ≠ 0 := by
  obtain ⟨B, hB, r₀, hr₀, hzero⟩ := exists_riemannZeta_polynomial_zero_criterion
  let K₀ : ℕ := max 7228 (max ⌈1 + 13107200 * (B + 2)⌉₊ ⌈1 / r₀⌉₊)
  have hK₀ : 7228 ≤ K₀ := le_max_left _ _
  refine ⟨K₀, hK₀, ?_⟩
  intro K hK t β ht hlo hhi hβ
  have hKlarge : 7228 ≤ K := hK₀.trans hK
  have hKR : (7228 : ℝ) ≤ K := by exact_mod_cast hKlarge
  have hTp : 0 < |t| := by linarith
  have hBX : 1 + 13107200 * (B + 2) ≤ (K : ℝ) + 1 := by
    have hceil : 1 + 13107200 * (B + 2) ≤ (⌈1 + 13107200 * (B + 2)⌉₊ : ℝ) := Nat.le_ceil _
    have hn : ⌈1 + 13107200 * (B + 2)⌉₊ ≤ K :=
      (le_trans (le_max_left _ _) (le_max_right _ _)).trans hK
    have hc : (⌈1 + 13107200 * (B + 2)⌉₊ : ℝ) ≤ K := Nat.cast_le.mpr hn
    linarith
  have hBr : B ≤ (K : ℝ) + 1 := by linarith
  have hrK : 1 / r₀ < (K : ℝ) + 1 := by
    have hceil : 1 / r₀ ≤ (⌈1 / r₀⌉₊ : ℝ) := Nat.le_ceil _
    have hn : ⌈1 / r₀⌉₊ ≤ K :=
      (le_trans (le_max_right _ _) (le_max_right _ _)).trans hK
    have hc : (⌈1 / r₀⌉₊ : ℝ) ≤ K := Nat.cast_le.mpr hn
    linarith
  have hradius : polynomialDetectorRadius K B < r₀ := by
    apply (polynomialDetectorRadius_le_inv K hB.le).trans_lt
    apply (div_lt_iff₀ (by positivity : 0 < (K : ℝ) + 1)).mpr
    have h := (div_lt_iff₀ hr₀).mp hrK
    nlinarith only [h]
  have hlog : 1 ≤ Real.log |t| := by
    have hp : 1 ≤ (K : ℝ) ^ 16 := one_le_pow₀ (by linarith)
    exact hp.trans hlo
  have hT : 3 ≤ |t| := by
    have hp : (2 : ℝ) ≤ (K : ℝ) ^ 16 :=
      (by linarith : (2 : ℝ) ≤ K).trans (le_self_pow₀ (by linarith) (by decide))
    have he : 3 ≤ Real.exp (Real.log |t|) := by
      have hx := Real.add_one_le_exp (Real.log |t|)
      linarith
    rwa [Real.exp_log hTp] at he
  have hheight : (2 : ℝ) ^ K + polynomialDetectorScale K ≤ |t| := by
    apply (polynomialDetector_height_threshold (by omega : 2 ≤ K)).trans
    simpa only [Real.exp_log hTp] using Real.exp_le_exp.mpr hlo
  have henv := polynomialDetector_envelope_exp_bound hKlarge hB.le hBX hT hlog hhi
  have hwidth := polynomialDetectorRadius_lower K hB.le hBr
  have hR := polynomialDetectorScale_pos K
  have hA : 0 < polynomialDetectorAmplitude K :=
    (by norm_num : (0 : ℝ) < 1).trans_le (polynomialDetectorAmplitude_one_le K)
  apply hzero K (by omega) (polynomialDetectorScale K) (polynomialDetectorAmplitude K)
    t β hR (polynomialDetectorScale_eq K).le hA hheight
  · exact hradius
  · exact henv
  · change 1 - polynomialDetectorRadius K B / 10 ≤ β
    linarith only [hwidth, hβ]

end Erdos421
