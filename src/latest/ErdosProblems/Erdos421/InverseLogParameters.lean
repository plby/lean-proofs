import ErdosProblems.Erdos421.PrimeScaleSaving

/-! # Comparing inverse logarithmic savings with fixed inverse powers -/

namespace Erdos421

open Filter Topology

theorem inverse_log_above_inverse_power {d ε : ℝ} (hd : 0 < d) (hε : 0 < ε) (A : ℝ) :
    ∀ᶠ X : ℕ in atTop, (X : ℝ) ^ (-d) ≤ ε / (Real.log X) ^ A := by
  have ht := ((isLittleO_log_rpow_rpow_atTop A hd).tendsto_div_nhds_zero).comp
    tendsto_natCast_atTop_atTop
  filter_upwards [ht.eventually (gt_mem_nhds hε), eventually_ge_atTop (2 : ℕ)] with X hX hX2
  have hXp : (0 : ℝ) < X := by exact_mod_cast (show 0 < X by omega)
  have hlogp : 0 < Real.log X := Real.log_pos (by exact_mod_cast (show 1 < X by omega))
  apply (le_div_iff₀ (Real.rpow_pos_of_pos hlogp A)).mpr
  rw [Real.rpow_neg hXp.le]
  simpa only [div_eq_mul_inv, mul_comm, Function.comp_apply] using hX.le

theorem twoFactor_log_weight_identity {L ε C A : ℝ} (hL : 0 < L) (hC : 0 < C) (D : ℕ) :
    2 * (C * L ^ D) * ((ε / (2 * C)) / L ^ (A + D)) = ε / L ^ A := by
  rw [Real.rpow_add hL, Real.rpow_natCast]
  have hLA : L ^ A ≠ 0 := (Real.rpow_pos_of_pos hL _).ne'
  have hLD : L ^ D ≠ 0 := (pow_pos hL _).ne'
  field_simp

end Erdos421
