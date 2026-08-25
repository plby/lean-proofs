import Util.Bernays.VerticalProductDecay
import PrimeNumberTheoremAnd.Wiener

/-!
# Smoothed coefficient cancellation from a continued convolution square
-/

open Set Filter Topology MeasureTheory
open scoped FourierTransform

namespace Bernays

theorem fourier_eq_oscillatory (g : ℝ → ℂ) (y : ℝ) :
    𝓕 g (-y / (2 * Real.pi)) =
      ∫ t : ℝ, g t * Complex.exp ((y : ℂ) * t * Complex.I) := by
  rw [Real.fourier_eq]
  apply integral_congr_ae
  filter_upwards [] with t
  simp only [Circle.smul_def, Real.fourierChar, AddChar.coe_mk,
    Circle.coe_exp, smul_eq_mul, RCLike.inner_apply', conj_trivial]
  rw [mul_comm (g t)]
  congr 1
  congr 1
  push_cast
  field_simp

theorem smoothed_LSeries_eq_fourier (a : ℕ → ℂ)
    (ha : ∀ s : ℂ, 1 < s.re → LSeriesSummable a s)
    (ψ : ℝ → ℂ) (hψ : Integrable ψ) {δ : ℝ} (hδ : 0 < δ) :
    (∑' n : ℕ, LSeries.term a (1 + δ) n *
      𝓕 ψ (1 / (2 * Real.pi) * Real.log ((n : ℝ) / Real.exp (1 / δ)))) =
      𝓕 (verticalProduct (LSeries a) ψ (1 + δ)) (-1 / (2 * Real.pi * δ)) := by
  have hs (σ : ℝ) (hσ : 1 < σ) : Summable (nterm a σ) := by
    have hsum := (ha σ (by simpa using hσ)).norm
    simpa only [norm_term_eq_nterm_re, Complex.ofReal_re] using hsum
  have hid : -1 / (2 * Real.pi * δ) = -(1 / δ) / (2 * Real.pi) := by ring
  rw [hid, fourier_eq_oscillatory]
  rw [show (1 : ℂ) + δ = ((1 + δ : ℝ) : ℂ) by push_cast; rfl]
  rw [first_fourier hs hψ (Real.exp_pos _) (by simpa using hδ)]
  apply integral_congr_ae
  filter_upwards [] with t
  change LSeries a ((1 + δ : ℝ) + t * Complex.I) * ψ t *
    (Real.exp (1 / δ) : ℂ) ^ ((t : ℂ) * Complex.I) = _
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero _)),
    ← Complex.ofReal_log (Real.exp_pos _).le, Real.log_exp]
  dsimp only [verticalProduct]
  congr 1
  congr 1
  ring

theorem LSeries_square_smoothed_cancellation (a : ℕ → ℂ) (F : ℂ → ℂ)
    (ha : ∀ s : ℂ, 1 < s.re → LSeriesSummable a s)
    (had : ∀ s : ℂ, 1 < s.re → DifferentiableAt ℂ (LSeries a) s)
    (hF : ∀ s : ℂ, (1 / 2 : ℝ) < s.re → DifferentiableAt ℂ F s)
    (heq : ∀ s : ℂ, 1 < s.re → F s = LSeries a s ^ 2)
    (hne : ∃ s : ℂ, (1 / 2 : ℝ) < s.re ∧ F s ≠ 0)
    (ψ : ℝ → ℂ) (hψ : ContDiff ℝ 1 ψ) (hsupp : HasCompactSupport ψ) :
    Tendsto (fun δ : ℝ =>
      ‖∑' n : ℕ, LSeries.term a (1 + δ) n *
        𝓕 ψ (1 / (2 * Real.pi) * Real.log ((n : ℝ) / Real.exp (1 / δ)))‖ / Real.sqrt δ)
      (𝓝[>] 0) (𝓝 0) := by
  apply (halfPlane_square_fourier_decay had hF heq hne hψ hsupp).congr'
  filter_upwards [self_mem_nhdsWithin] with δ hδ
  rw [smoothed_LSeries_eq_fourier a ha ψ (hψ.continuous.integrable_of_hasCompactSupport hsupp) hδ]

end Bernays
