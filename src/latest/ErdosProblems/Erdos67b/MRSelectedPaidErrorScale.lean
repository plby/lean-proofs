import ErdosProblems.Erdos67b.MRSelectedPaidSampleScalar

/-! # Power decay absorbs every fixed polylogarithmic sample count -/

open Filter
open scoped Topology

namespace Erdos67b

noncomputable section

def mrSelectedPaidErrorExponent (r theta : ℝ) : ℝ :=
  (r * theta / 2) * mrPrimeKernelSaving (mrSelectedPowerOrder r theta)

def mrSelectedPaidErrorConstant (r theta E : ℝ) : ℝ :=
  2 * E * mrPrimeSieveExponent (mrSelectedPowerOrder r theta) * theta *
    mrPrimeKernelErrorConstant (mrSelectedPowerOrder r theta) * mrPrimeBlockMassConstant / r

theorem mrSelectedPaidErrorExponent_pos {r theta : ℝ} (hr : 0 < r) (htheta : 0 < theta) :
    0 < mrSelectedPaidErrorExponent r theta := by
  have := mrPrimeKernelSaving_pos (mrSelectedPowerOrder r theta)
  unfold mrSelectedPaidErrorExponent
  positivity

theorem mrSelectedPaidErrorConstant_nonneg {r theta E : ℝ}
    (hr : 0 < r) (htheta : 0 < theta) (hE : 0 ≤ E) :
    0 ≤ mrSelectedPaidErrorConstant r theta E := by
  have := mrPrimeSieveExponent_pos (mrSelectedPowerOrder r theta)
  have := mrPrimeKernelErrorConstant_pos (mrSelectedPowerOrder r theta)
  have := mrPrimeBlockMassConstant_pos
  unfold mrSelectedPaidErrorConstant
  positivity

theorem mrSelectedPaid_budget_scaled_eq {r theta E X : ℝ} (hr : 0 < r) (hX : 1 < X) (N : ℕ) :
    (Real.log X) ^ 2 * mrSelectedPaidPrimeEnergyBudget r theta E X N =
      80000 * mrPrimeBlockMassConstant * E / r ^ 2 +
        mrSelectedPaidErrorConstant r theta E * N * Real.log X /
          X ^ mrSelectedPaidErrorExponent r theta := by
  have hlog : 0 < Real.log X := Real.log_pos hX
  have hXpos : 0 < X := by linarith
  unfold mrSelectedPaidPrimeEnergyBudget mrSelectedPaidErrorConstant mrSelectedPaidErrorExponent
  field_simp

theorem mrTendsto_selectedPaid_polylog_error {r theta E B : ℝ}
    (hr : 0 < r) (htheta : 0 < theta) (k : ℕ) :
    Tendsto (fun X : ℝ ↦ (mrSelectedPaidErrorConstant r theta E * B) *
      ((Real.log X) ^ (k + 1) / X ^ mrSelectedPaidErrorExponent r theta)) atTop (𝓝 0) := by
  have hh := (isLittleO_log_rpow_rpow_atTop ((k + 1 : ℕ) : ℝ)
    (mrSelectedPaidErrorExponent_pos hr htheta)).tendsto_div_nhds_zero
  have hm := hh.const_mul (mrSelectedPaidErrorConstant r theta E * B)
  simpa only [Real.rpow_natCast, mul_zero] using hm

theorem mrExists_selectedPaid_budget_polylog_threshold {r theta E B epsilon : ℝ}
    (hr : 0 < r) (htheta : 0 < theta) (hE : 0 ≤ E)
    (_hB : 0 ≤ B) (hepsilon : 0 < epsilon) (k : ℕ) :
    ∃ X₀ : ℕ, 2 ≤ X₀ ∧ ∀ X ≥ X₀, ∀ N : ℕ,
      (N : ℝ) ≤ B * (Real.log (X : ℝ)) ^ k →
      (Real.log (X : ℝ)) ^ 2 * mrSelectedPaidPrimeEnergyBudget r theta E X N ≤
        80000 * mrPrimeBlockMassConstant * E / r ^ 2 + epsilon := by
  have hlim := (mrTendsto_selectedPaid_polylog_error (E := E) (B := B) hr htheta k).comp
    tendsto_natCast_atTop_atTop
  obtain ⟨X₁, hX₁⟩ := eventually_atTop.1 (hlim.eventually (gt_mem_nhds hepsilon))
  refine ⟨max 2 X₁, le_max_left _ _, ?_⟩
  intro X hX N hN
  have hXtwo : 2 ≤ X := (le_max_left 2 X₁).trans hX
  have hXone : (1 : ℝ) < X := by exact_mod_cast (show 1 < X by omega)
  have hlog : 0 ≤ Real.log (X : ℝ) := (Real.log_pos hXone).le
  have hC := mrSelectedPaidErrorConstant_nonneg hr htheta hE
  have hsmall := hX₁ X ((le_max_right 2 X₁).trans hX)
  rw [mrSelectedPaid_budget_scaled_eq hr hXone]
  apply add_le_add le_rfl
  calc
    _ ≤ mrSelectedPaidErrorConstant r theta E * (B * (Real.log (X : ℝ)) ^ k) *
        Real.log (X : ℝ) / (X : ℝ) ^ mrSelectedPaidErrorExponent r theta := by gcongr
    _ = (mrSelectedPaidErrorConstant r theta E * B) *
        ((Real.log (X : ℝ)) ^ (k + 1) / (X : ℝ) ^ mrSelectedPaidErrorExponent r theta) := by
      rw [pow_succ]
      ring
    _ ≤ epsilon := hsmall.le

end

end Erdos67b
