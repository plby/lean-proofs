import ErdosProblems.Erdos421.ZetaPolynomialHeightBand
import ErdosProblems.Erdos421.LogarithmicDegreeChoice

/-! # An unconditional log-power zero-free region

The explicit exponent `15/16` is deliberately weaker than the sharp
Korobov--Vinogradov exponent. The mean-value estimates, exponential sums,
zeta growth bounds, and zero detector used here are all proved in this project.
-/

namespace Erdos421

open Complex

theorem riemannZeta_eventually_ne_zero_log_power_strip :
    ∃ T₀ > 1, ∀ t β : ℝ, T₀ ≤ |t| →
      1 - ((2 : ℝ) ^ 44)⁻¹ / (Real.log |t|) ^ (15 / 16 : ℝ) ≤ β →
        riemannZeta ((β : ℂ) + t * I) ≠ 0 := by
  obtain ⟨K₀, hK₀, hband⟩ := exists_riemannZeta_polynomial_height_band
  let T₀ : ℝ := Real.exp (((K₀ : ℝ) + 1) ^ 16)
  have hT₀ : 1 < T₀ := Real.one_lt_exp_iff.mpr (by positivity)
  refine ⟨T₀, hT₀, ?_⟩
  intro t β ht hβ
  have ht1 : 1 < |t| := hT₀.trans_le ht
  have htp : 0 < |t| := by linarith
  have hlog : ((K₀ : ℝ) + 1) ^ 16 ≤ Real.log |t| := by
    have h := Real.log_le_log (Real.exp_pos _) ht
    rwa [Real.log_exp] at h
  have hlog1 : 1 ≤ Real.log |t| :=
    (one_le_pow₀ (by linarith [(Nat.cast_nonneg K₀ : (0 : ℝ) ≤ K₀)])).trans hlog
  have hlogK : (K₀ : ℝ) ^ 16 ≤ Real.log |t| :=
    (pow_le_pow_left₀ (Nat.cast_nonneg K₀) (by linarith : (K₀ : ℝ) ≤ K₀ + 1) 16).trans hlog
  obtain ⟨K, hK, hlo, hhi, hroot⟩ := exists_logarithmic_degree hlog1 hlogK
  have hwidth := logarithmic_degree_width_lower (by linarith : 0 < Real.log |t|) hroot
  apply hband K hK t β ht1 hlo hhi
  linarith only [hβ, hwidth]

end Erdos421
