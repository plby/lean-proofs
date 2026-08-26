import ErdosProblems.Erdos67b.MRSelectedPowerOrder

/-! # The selected tail pays the explicit exponential cutoff cost -/

open Filter
open scoped Topology

namespace Erdos67b

noncomputable section

theorem mrTendsto_selected_tail_cubic_cost :
    Tendsto (fun tau : ℝ ↦ (tau + 1) ^ 3 * Real.exp (-2 * tau)) atTop (𝓝 0) := by
  have hshift : Tendsto (fun tau : ℝ ↦ tau + 1) atTop atTop :=
    tendsto_atTop_add_const_right atTop 1 tendsto_id
  have hp := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 3).comp hshift
  have he : Tendsto (fun tau : ℝ ↦ Real.exp (-tau)) atTop (𝓝 0) := by
    simpa only [pow_zero, one_mul] using Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 0
  have hh := (hp.mul he).mul_const (Real.exp 1)
  simp only [zero_mul] at hh
  apply hh.congr'
  filter_upwards [] with tau
  simp only [Function.comp_apply]
  calc
    _ = (tau + 1) ^ 3 * Real.exp (-(tau + 1) + (-tau) + 1) := by
      simp only [Real.exp_add]
      ring
    _ = _ := by congr 2; ring

theorem mrSelected_shifted_cost_tail_le {r tau : ℝ} (hr : 0 < r) (htau : 0 ≤ tau) :
    (mrPrimeSieveExponent (mrSelectedPowerOrder r (1 / (16 * (tau + 1)))))⁻¹ *
      (1 / (16 * (tau + 1)))⁻¹ ^ 2 *
      (Real.exp (-mrSelectedPowerShift r * tau) + Real.exp (-mrSelectedPowerShift r * tau)) ^ 2 ≤
        (131072 * mrSelectedPowerOrderSlope r *
          Real.exp (mrSelectedPowerOrderSlope r * Real.log 2)) *
          ((tau + 1) ^ 3 * Real.exp (-2 * tau)) := by
  have hcost := mrSelectedPower_cutoff_cost_le hr htau
  have hL := mrSelectedPowerOrderSlope_pos hr
  have heq : Real.exp (mrSelectedPowerOrderSlope r * Real.log 2 * (tau + 1)) *
      Real.exp (-mrSelectedPowerShift r * tau) ^ 2 =
      Real.exp (mrSelectedPowerOrderSlope r * Real.log 2) * Real.exp (-2 * tau) := by
    rw [show Real.exp (-mrSelectedPowerShift r * tau) ^ 2 =
      Real.exp ((-mrSelectedPowerShift r * tau) + (-mrSelectedPowerShift r * tau)) by
        rw [Real.exp_add]; ring]
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    unfold mrSelectedPowerShift
    ring
  calc
    _ ≤ (128 * mrSelectedPowerOrderSlope r * (tau + 1) *
        Real.exp (mrSelectedPowerOrderSlope r * Real.log 2 * (tau + 1))) *
        (1 / (16 * (tau + 1)))⁻¹ ^ 2 *
        (Real.exp (-mrSelectedPowerShift r * tau) +
          Real.exp (-mrSelectedPowerShift r * tau)) ^ 2 := by
      gcongr
    _ = (131072 * mrSelectedPowerOrderSlope r) * (tau + 1) ^ 3 *
        (Real.exp (mrSelectedPowerOrderSlope r * Real.log 2 * (tau + 1)) *
          Real.exp (-mrSelectedPowerShift r * tau) ^ 2) := by simp only [one_div, inv_inv]; ring
    _ = _ := by rw [heq]; ring

theorem mrExists_selected_shifted_cutoff_budget {r D E thetaMax : ℝ}
    (hr : 0 < r) (hD : 0 ≤ D) (hE : 0 < E) (hthetaMax : 0 < thetaMax) :
    ∃ tau : ℝ, 0 ≤ tau ∧ ∃ theta : ℝ, 0 < theta ∧ theta ≤ thetaMax ∧
      theta = 1 / (16 * (tau + 1)) ∧ (tau + 1) * theta = 1 / 16 ∧
      ∃ epsilon : ℝ, 0 < epsilon ∧
        D * (mrPrimeSieveExponent (mrSelectedPowerOrder r theta))⁻¹ * theta⁻¹ ^ 2 *
          (epsilon + Real.exp (-mrSelectedPowerShift r * tau)) ^ 2 ≤ E := by
  let C := 131072 * mrSelectedPowerOrderSlope r *
    Real.exp (mrSelectedPowerOrderSlope r * Real.log 2)
  have hlimit := mrTendsto_selected_tail_cubic_cost.const_mul (D * C)
  simp only [mul_zero] at hlimit
  have hsmall : ∀ᶠ tau : ℝ in atTop,
      (D * C) * ((tau + 1) ^ 3 * Real.exp (-2 * tau)) < E :=
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
  have hproduct : (tau + 1) * theta = 1 / 16 := by dsimp [theta]; field_simp
  refine ⟨tau, htau, theta, htheta, hthetaBound, rfl, hproduct,
    Real.exp (-mrSelectedPowerShift r * tau), Real.exp_pos _, ?_⟩
  have hb := mul_le_mul_of_nonneg_left (mrSelected_shifted_cost_tail_le hr htau) hD
  have hbound : D * (mrPrimeSieveExponent (mrSelectedPowerOrder r theta))⁻¹ * theta⁻¹ ^ 2 *
      (Real.exp (-mrSelectedPowerShift r * tau) + Real.exp (-mrSelectedPowerShift r * tau)) ^ 2 ≤
      (D * C) * ((tau + 1) ^ 3 * Real.exp (-2 * tau)) := by
    dsimp only [theta, C]
    nlinarith only [hb]
  exact hbound.trans htail.le

end

end Erdos67b
