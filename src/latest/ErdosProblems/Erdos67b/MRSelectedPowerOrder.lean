import ErdosProblems.Erdos67b.MRPrimePowerCutoffGeometry

/-! # Explicit derivative order and selected-tail shift at an auxiliary power -/

namespace Erdos67b

noncomputable section

def mrSelectedPowerOrder (r theta : ℝ) : ℕ := ⌈4 / (r * theta)⌉₊ + 2

def mrSelectedPowerOrderSlope (r : ℝ) : ℝ := 64 / r + 4

def mrSelectedPowerShift (r : ℝ) : ℝ := mrSelectedPowerOrderSlope r * Real.log 2 / 2 + 1

theorem mrSelectedPowerOrder_ge_two (r theta : ℝ) : 2 ≤ mrSelectedPowerOrder r theta := by
  unfold mrSelectedPowerOrder
  omega

theorem mrSelectedPowerOrder_ge_height (r theta : ℝ) :
    4 / (r * theta) ≤ (mrSelectedPowerOrder r theta : ℝ) := by
  have hh := Nat.le_ceil (4 / (r * theta))
  unfold mrSelectedPowerOrder
  push_cast
  linarith

theorem mrSelectedPowerOrderSlope_pos {r : ℝ} (hr : 0 < r) :
    0 < mrSelectedPowerOrderSlope r := by unfold mrSelectedPowerOrderSlope; positivity

theorem mrSelectedPowerShift_pos {r : ℝ} (hr : 0 < r) : 0 < mrSelectedPowerShift r := by
  have := mrSelectedPowerOrderSlope_pos hr
  have := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  unfold mrSelectedPowerShift
  positivity

theorem mrSelectedPowerOrder_le_tau {r tau : ℝ} (hr : 0 < r) (htau : 0 ≤ tau) :
    (mrSelectedPowerOrder r (1 / (16 * (tau + 1))) : ℝ) + 1 ≤
      mrSelectedPowerOrderSlope r * (tau + 1) := by
  have heq : 4 / (r * (1 / (16 * (tau + 1)))) = 64 * (tau + 1) / r := by field_simp; ring
  have hh := Nat.ceil_lt_add_one (show 0 ≤ 4 / (r * (1 / (16 * (tau + 1)))) by positivity)
  rw [heq] at hh
  unfold mrSelectedPowerOrder mrSelectedPowerOrderSlope
  rw [heq]
  push_cast
  rw [show 64 * (tau + 1) / r = (64 / r) * (tau + 1) by ring] at hh ⊢
  nlinarith

theorem mrSelectedPower_cutoff_cost_le {r tau : ℝ} (hr : 0 < r) (htau : 0 ≤ tau) :
    (mrPrimeSieveExponent (mrSelectedPowerOrder r (1 / (16 * (tau + 1)))))⁻¹ ≤
      128 * mrSelectedPowerOrderSlope r * (tau + 1) *
        Real.exp (mrSelectedPowerOrderSlope r * Real.log 2 * (tau + 1)) := by
  let R := mrSelectedPowerOrder r (1 / (16 * (tau + 1)))
  have hL := mrSelectedPowerOrderSlope_pos hr
  have horder : (R : ℝ) + 1 ≤ mrSelectedPowerOrderSlope r * (tau + 1) :=
    mrSelectedPowerOrder_le_tau hr htau
  have hlogTwo : 0 ≤ Real.log (2 : ℝ) := Real.log_nonneg (by norm_num)
  have hpower : (2 : ℝ) ^ (R + 1) ≤
      Real.exp (mrSelectedPowerOrderSlope r * Real.log 2 * (tau + 1)) := by
    rw [← Real.rpow_natCast, Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
    apply Real.exp_le_exp.mpr
    have hh := mul_le_mul_of_nonneg_left horder hlogTwo
    push_cast
    nlinarith
  rw [mrPrimeSieveExponent_inv_eq]
  change 128 * ((R : ℝ) + 1) * (2 : ℝ) ^ (R + 1) ≤ _
  calc
    _ ≤ 128 * (mrSelectedPowerOrderSlope r * (tau + 1)) *
        Real.exp (mrSelectedPowerOrderSlope r * Real.log 2 * (tau + 1)) := by
      gcongr
    _ = _ := by ring

end

end Erdos67b
