/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.FGKMTGapScale
import ErdosProblems.Erdos4b.RankinMonotonicity

/-! # Monotonicity and divergence of the exact stronger scale -/

namespace Erdos4b

noncomputable section

open Filter

def fgkmtFactor (v : ℝ) : ℝ := v * Real.log (Real.log v) / Real.log v

theorem fgkmtFactor_eq_rankinFactor_mul {v : ℝ} (hv : Real.log v ≠ 0) :
    fgkmtFactor v = rankinFactor v * Real.log v := by
  unfold fgkmtFactor rankinFactor
  field_simp

theorem fgkmtFactor_nonneg {v : ℝ} (hv : Real.exp 2 ≤ v) : 0 ≤ fgkmtFactor v := by
  have hvpos : 0 < v := (Real.exp_pos 2).trans_le hv
  have hlog : 2 ≤ Real.log v := (Real.le_log_iff_exp_le hvpos).mpr hv
  rw [fgkmtFactor_eq_rankinFactor_mul (by linarith : Real.log v ≠ 0)]
  exact mul_nonneg (rankinFactor_nonneg hv) (by linarith)

theorem fgkmtFactor_monotoneOn : MonotoneOn fgkmtFactor (Set.Ici (Real.exp 2)) := by
  intro v hv w hw hvw
  have hvpos : 0 < v := (Real.exp_pos 2).trans_le hv
  have hwpos : 0 < w := hvpos.trans_le hvw
  have hlogv : 2 ≤ Real.log v := (Real.le_log_iff_exp_le hvpos).mpr hv
  have hlogw : 2 ≤ Real.log w := (Real.le_log_iff_exp_le hwpos).mpr hw
  rw [fgkmtFactor_eq_rankinFactor_mul (by linarith : Real.log v ≠ 0),
    fgkmtFactor_eq_rankinFactor_mul (by linarith : Real.log w ≠ 0)]
  exact mul_le_mul (rankinFactor_monotoneOn hv hw hvw) (Real.log_le_log hvpos hvw)
    (by linarith) (rankinFactor_nonneg hw)

theorem fgkmtScale_eq_factor (X : ℝ) :
    fgkmtScale X = Real.log X * fgkmtFactor (Real.log (Real.log X)) := by
  unfold fgkmtScale fgkmtFactor
  ring

theorem fgkmtScale_mono {X Y : ℝ} (hX : 1 < X)
    (hloglog : Real.exp 2 ≤ Real.log (Real.log X)) (hXY : X ≤ Y) :
    fgkmtScale X ≤ fgkmtScale Y := by
  have hlogX : 0 < Real.log X := Real.log_pos hX
  have hlogs := Real.log_le_log (by linarith : 0 < X) hXY
  have hloglogs := Real.log_le_log hlogX hlogs
  have hloglogY := hloglog.trans hloglogs
  rw [fgkmtScale_eq_factor, fgkmtScale_eq_factor]
  exact mul_le_mul hlogs (fgkmtFactor_monotoneOn hloglog hloglogY hloglogs)
    (fgkmtFactor_nonneg hloglog) (hlogX.le.trans hlogs)

theorem eventually_log_le_fgkmtScale :
    ∀ᶠ X : ℝ in atTop, Real.log X ≤ fgkmtScale X := by
  have h1 := Real.tendsto_log_atTop
  have h2 := Real.tendsto_log_atTop.comp h1
  have h3 := Real.tendsto_log_atTop.comp h2
  have h4 := Real.tendsto_log_atTop.comp h3
  filter_upwards [h1.eventually_ge_atTop 1, h2.eventually_ge_atTop 1,
    h3.eventually_ge_atTop 1, h4.eventually_ge_atTop 1] with X hA hV hW hT
  let A := Real.log X
  let V := Real.log A
  let W := Real.log V
  let T := Real.log W
  change 1 ≤ A at hA
  change 1 ≤ V at hV
  change 1 ≤ W at hW
  change 1 ≤ T at hT
  have hWV : W ≤ V := Real.log_le_self (by linarith : 0 ≤ V)
  have hVT : W ≤ V * T := hWV.trans (le_mul_of_one_le_right (by linarith) hT)
  change A ≤ A * V * T / W
  apply (le_div_iff₀ (by linarith : 0 < W)).mpr
  nlinarith [mul_le_mul_of_nonneg_left hVT (by linarith : 0 ≤ A)]

theorem tendsto_fgkmtScale_atTop : Tendsto fgkmtScale atTop atTop :=
  tendsto_atTop_mono' atTop eventually_log_le_fgkmtScale Real.tendsto_log_atTop

end

end Erdos4b
