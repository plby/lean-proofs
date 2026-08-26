import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# Feasible error choices for a fixed-power selected cofactor

An exponentially small selected-factor tail pays the polynomial cost of
decreasing the upper exponent. This is a scalar parameter theorem, not
an assertion of the still-unproved sparse-prime energy estimate.
-/

open Filter
open scoped Topology

namespace Erdos67b

noncomputable section

theorem mrTendsto_selected_tail_polynomial_cost :
    Tendsto (fun tau : ℝ ↦ (tau + 1) ^ 2 * Real.exp (-2 * tau)) atTop (𝓝 0) := by
  have hshift : Tendsto (fun tau : ℝ ↦ tau + 1) atTop atTop :=
    tendsto_atTop_add_const_right atTop 1 tendsto_id
  have hp := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 2).comp hshift
  have he : Tendsto (fun tau : ℝ ↦ Real.exp (-tau)) atTop (𝓝 0) := by
    simpa only [pow_zero, one_mul] using Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 0
  have hh := (hp.mul he).mul_const (Real.exp 1)
  simp only [zero_mul] at hh
  apply hh.congr'
  filter_upwards [] with tau
  simp only [Function.comp_apply]
  calc
    (tau + 1) ^ 2 * Real.exp (-(tau + 1)) * Real.exp (-tau) * Real.exp 1 =
        (tau + 1) ^ 2 * Real.exp (-(tau + 1) + (-tau) + 1) := by
      simp only [Real.exp_add]
      ring
    _ = _ := by congr 2; ring

theorem mrExists_selected_tail_and_prefix_budget {D E thetaMax : ℝ}
    (hE : 0 < E) (hthetaMax : 0 < thetaMax) :
    ∃ tau : ℝ, 0 ≤ tau ∧ ∃ theta : ℝ, 0 < theta ∧ theta ≤ thetaMax ∧
      theta = 1 / (16 * (tau + 1)) ∧ (tau + 1) * theta = 1 / 16 ∧
      ∃ epsilon : ℝ, 0 < epsilon ∧
        D * theta⁻¹ ^ 2 * (epsilon + Real.exp (-tau)) ^ 2 ≤ E := by
  have hlimit := mrTendsto_selected_tail_polynomial_cost.const_mul (1024 * D)
  simp only [mul_zero] at hlimit
  have hsmall : ∀ᶠ tau : ℝ in atTop,
      1024 * D * ((tau + 1) ^ 2 * Real.exp (-2 * tau)) < E :=
    hlimit.eventually (gt_mem_nhds hE)
  obtain ⟨tau, htau, hmax, htail⟩ :=
    (eventually_ge_atTop (0 : ℝ) |>.and
      ((eventually_ge_atTop (1 / (16 * thetaMax))).and hsmall)).exists
  let theta := 1 / (16 * (tau + 1))
  have hden : 0 < 16 * (tau + 1) := by positivity
  have htheta : 0 < theta := div_pos zero_lt_one hden
  have hthetaBound : theta ≤ thetaMax := by
    apply (div_le_iff₀ hden).2
    have hh := (div_le_iff₀ (by positivity : (0 : ℝ) < 16 * thetaMax)).1 hmax
    nlinarith
  have hproduct : (tau + 1) * theta = 1 / 16 := by
    dsimp only [theta]
    field_simp
  refine ⟨tau, htau, theta, htheta, hthetaBound, rfl, hproduct,
    Real.exp (-tau), Real.exp_pos _, ?_⟩
  have heq : D * theta⁻¹ ^ 2 * (Real.exp (-tau) + Real.exp (-tau)) ^ 2 =
      1024 * D * ((tau + 1) ^ 2 * Real.exp (-2 * tau)) := by
    have hinv : theta⁻¹ = 16 * (tau + 1) := by simp [theta]
    have hexp : Real.exp (-2 * tau) = Real.exp (-tau) ^ 2 := by
      rw [show -2 * tau = (-tau) + (-tau) by ring, Real.exp_add]
      ring
    rw [hinv, hexp]
    ring
  exact heq.le.trans htail.le

end

end Erdos67b
