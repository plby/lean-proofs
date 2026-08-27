import Mathlib.Probability.Moments.Variance

/-! # A useful lower-tail bound from a constant second-moment ratio

Applying Markov's inequality to `(X - 5*mean)^2` gives a one-sided bound
even when the relative variance is too large for the usual two-sided
Chebyshev estimate to be useful.
-/

open MeasureTheory

namespace Arxiv2411_18291

theorem lower_tail_le_eight_ninths_of_second_moment {Ω : Type*} [MeasurableSpace Ω]
    (ν : Measure Ω) [IsProbabilityMeasure ν] {X : Ω → ℝ} (hX : MemLp X 2 ν)
    {μ : ℝ} (hμ : 0 < μ) (hmean : (∫ ω, X ω ∂ν) = μ)
    (hsecond : (∫ ω, X ω ^ 2 ∂ν) ≤ 3 * μ ^ 2) :
    ν.real {ω | X ω ≤ μ / 2} ≤ 8 / 9 := by
  have hi : Integrable X ν := hX.integrable (by norm_num)
  have hi2 : Integrable (fun ω => X ω ^ 2) ν :=
    (memLp_two_iff_integrable_sq hX.aestronglyMeasurable).mp hX
  have hshift : MemLp (fun ω => X ω - 5 * μ) 2 ν := hX.sub (memLp_const (5 * μ))
  have hshiftInt := (memLp_two_iff_integrable_sq hshift.aestronglyMeasurable).mp hshift
  have hint : (∫ ω, (X ω - 5 * μ) ^ 2 ∂ν) ≤ 18 * μ ^ 2 := by
    have heq : (fun ω => (X ω - 5 * μ) ^ 2) =
        (fun ω => X ω ^ 2 - (10 * μ) * X ω + 25 * μ ^ 2) := by funext ω; ring
    have hiSub : Integrable (fun ω => X ω ^ 2 - (10 * μ) * X ω) ν :=
      hi2.sub (hi.const_mul (10 * μ))
    rw [heq, integral_add hiSub (integrable_const (25 * μ ^ 2)),
      integral_sub (f := fun ω => X ω ^ 2) (g := fun ω => (10 * μ) * X ω)
        hi2 (hi.const_mul (10 * μ)), integral_const_mul, integral_const,
      measureReal_def, measure_univ, ENNReal.toReal_one, smul_eq_mul, one_mul, hmean]
    nlinarith only [hsecond]
  have hsub : {ω | X ω ≤ μ / 2} ⊆
      {ω | (9 * μ / 2) ^ 2 ≤ (X ω - 5 * μ) ^ 2} := by
    intro ω hω
    have hh : 9 * μ / 2 ≤ 5 * μ - X ω := by change X ω ≤ μ / 2 at hω; linarith only [hω]
    have hs := pow_le_pow_left₀ (by positivity : 0 ≤ 9 * μ / 2) hh 2
    change (9 * μ / 2) ^ 2 ≤ (X ω - 5 * μ) ^ 2
    nlinarith only [hs]
  have hmark := mul_meas_ge_le_integral_of_nonneg
    (ae_of_all ν fun ω => sq_nonneg (X ω - 5 * μ)) hshiftInt ((9 * μ / 2) ^ 2)
  have hp := mul_le_mul_of_nonneg_left (measureReal_mono (μ := ν) hsub)
    (sq_nonneg (9 * μ / 2))
  have hh := hp.trans (hmark.trans hint)
  apply (mul_le_mul_iff_right₀ (sq_pos_of_pos hμ)).mp
  nlinarith only [hh]

end Arxiv2411_18291
