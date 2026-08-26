import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic

/-! # Turning a fixed power saving into any logarithmic saving -/

namespace Erdos421

open Filter Topology

theorem eventually_power_log_saving {C δ ε : ℝ} (hC : 0 < C) (hδ : 0 < δ) (hε : 0 < ε)
    (A B : ℝ) :
    ∀ᶠ X : ℕ in atTop,
      C * (X : ℝ) ^ (1 - δ) * (Real.log X) ^ B ≤ ε * X / (Real.log X) ^ A := by
  have hlim : Tendsto (fun X : ℕ ↦ (Real.log (X : ℝ)) ^ (A + B) / (X : ℝ) ^ δ)
      atTop (𝓝 0) :=
    ((isLittleO_log_rpow_rpow_atTop (A + B) hδ).tendsto_div_nhds_zero).comp
      tendsto_natCast_atTop_atTop
  filter_upwards [eventually_ge_atTop 2,
    hlim.eventually (gt_mem_nhds (div_pos hε hC))] with X hX hsmall
  have hXp : (0 : ℝ) < X := by exact_mod_cast (by omega : 0 < X)
  have hLp : 0 < Real.log X := Real.log_pos (by exact_mod_cast (by omega : 1 < X))
  have hQ : 0 < (X : ℝ) ^ δ := Real.rpow_pos_of_pos hXp _
  have hs : C * (Real.log X) ^ (A + B) ≤ ε * (X : ℝ) ^ δ := by
    simpa only [mul_comm] using (div_le_div_iff₀ hQ hC).mp hsmall.le
  have hXP : (X : ℝ) ^ (1 - δ) * (X : ℝ) ^ δ = X := by
    rw [← Real.rpow_add hXp, sub_add_cancel, Real.rpow_one]
  apply (le_div_iff₀ (Real.rpow_pos_of_pos hLp A)).mpr
  calc
    _ = (X : ℝ) ^ (1 - δ) * (C * (Real.log X) ^ (A + B)) := by
      rw [Real.rpow_add hLp]
      ring
    _ ≤ (X : ℝ) ^ (1 - δ) * (ε * (X : ℝ) ^ δ) :=
      mul_le_mul_of_nonneg_left hs (Real.rpow_nonneg hXp.le _)
    _ = ε * X := by rw [← mul_left_comm, hXP]

end Erdos421
