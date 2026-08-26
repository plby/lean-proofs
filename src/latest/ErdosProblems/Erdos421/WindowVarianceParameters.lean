import ErdosProblems.Erdos421.InverseLogParameters

/-! # Numerical parameters for the smoothed variance transfer -/

namespace Erdos421

open Filter Topology

theorem log_power_le_half_eventually (A : ℝ) :
    ∀ᶠ X : ℕ in atTop, (Real.log X) ^ A ≤ (X : ℝ) / 2 := by
  have ht := ((isLittleO_log_rpow_rpow_atTop A
    (by norm_num : (0 : ℝ) < 1)).tendsto_div_nhds_zero).comp tendsto_natCast_atTop_atTop
  filter_upwards [ht.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2)),
    eventually_ge_atTop (1 : ℕ)] with X hsave hX
  have hXp : (0 : ℝ) < X := Nat.cast_pos.mpr (by omega)
  have hb : (Real.log X) ^ A / (X : ℝ) < 1 / 2 := by
    simpa only [Function.comp_apply, Real.rpow_one] using hsave
  have hm := (div_lt_iff₀ hXp).mp hb
  linarith

theorem window_sixth_decay_tail_power {X R V K : ℝ} (hX : 0 < X)
    (hR : 0 ≤ R) (hRX : R ≤ X ^ (9 / 10 : ℝ)) (hV : X / 2 ≤ V) (hK : 0 ≤ K) :
    (2 * K * (R / 2) ^ 6) ^ 2 / (V ^ 5) ^ 2 / V ≤ 2 * K ^ 2 * X ^ (-1 / 5 : ℝ) := by
  have hXp : 0 < X / 2 := by positivity
  have hVp : 0 < V := hXp.trans_le hV
  have hp : 0 < X ^ (9 / 10 : ℝ) := Real.rpow_pos_of_pos hX _
  calc
    _ ≤ (2 * K * ((X ^ (9 / 10 : ℝ)) / 2) ^ 6) ^ 2 / ((X / 2) ^ 5) ^ 2 / (X / 2) := by
      gcongr
    _ = 2 * K ^ 2 * ((X ^ (9 / 10 : ℝ)) ^ 12 / X ^ 11) := by
      field_simp
    _ = _ := by
      rw [← Real.rpow_mul_natCast hX.le, ← Real.rpow_natCast X 11,
        ← Real.rpow_sub hX]
      norm_num

end Erdos421
