import ErdosProblems.Erdos421.PrimeErrorPerronTails
import ErdosProblems.Erdos421.PrimeErrorRectangle

/-! # A numerical unconditional bound for the smoothed prime-counting error -/

namespace Erdos421

open Complex MeasureTheory

theorem smoothedPrimeErrorSum_norm_eq {x σ : ℝ} (hx : 0 < x) (hσ : 1 < σ) :
    ‖smoothedPrimeErrorSum x‖ = (1 / (2 * Real.pi)) *
      ‖∫ y : ℝ, primeErrorPerronIntegrand x ((σ : ℂ) + y * I)‖ := by
  simpa only [primeErrorPerronIntegrand, norm_smul, Real.norm_eq_abs, abs_neg,
    abs_of_pos (by positivity : 0 < 1 / (2 * Real.pi))] using
    congrArg norm (smoothedPrimeErrorSum_eq_integral hx hσ)

theorem exists_smoothedPrimeError_numeric_bound :
    ∃ B > 0, ∃ r > 0, ∃ H₀ > 1, ∃ C > 0, ∀ x a b H : ℝ,
      1 ≤ x → 1 / 2 ≤ a → a ≤ b → 1 < b → b < 1 + r → H₀ ≤ H →
      1 - logPowerZeroWidth H / 64 ≤ a → b ≤ 1 + logPowerZeroWidth H / 64 →
      ‖smoothedPrimeErrorSum x‖ ≤ (1 / (2 * Real.pi)) *
        (4 * Real.pi * x ^ a * (C * H) + 2 * (b - a) * (x ^ b * (C * H) / H ^ 2) +
          2 * (x ^ b * (2 / (b - 1) + B)) / H) := by
  obtain ⟨B, hB, r, hr, htail⟩ := exists_primeErrorPerron_tail_bound
  obtain ⟨H₀, hH₀, C, hC, hrect⟩ := exists_primeErrorPerron_rectangle_bound
  refine ⟨B, hB, r, hr, H₀, hH₀, C, hC, ?_⟩
  intro x a b H hx ha hab hb hbr hH hlo hhi
  have hxp : 0 < x := by linarith
  have hHp : 0 < H := by linarith
  have hfinite := hrect x a b H hx ha hab hH hlo hhi
  have herror := htail x b H hxp hb hbr hHp
  have hnorm := norm_le_norm_sub_add
    (∫ y : ℝ, primeErrorPerronIntegrand x ((b : ℂ) + y * I))
    (∫ y : ℝ in -H..H, primeErrorPerronIntegrand x ((b : ℂ) + y * I))
  rw [smoothedPrimeErrorSum_norm_eq hxp hb]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  linarith only [hfinite, herror, hnorm]

end Erdos421
