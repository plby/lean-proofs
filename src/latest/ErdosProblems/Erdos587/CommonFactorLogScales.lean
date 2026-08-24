import ErdosProblems.Erdos587.CommonFactorPowerScales

/-! The geometric extraction loses only one fixed logarithmic power. -/

namespace Erdos587

theorem common_factor_geometric_size_budgets {T g H J H₀ J₀ T₀ W : ℝ}
    (hT : 0 < T) (hg : 1 ≤ g) (hH : 0 < H) (hJ : 0 < J) (hJH : J ≤ H) (hW : 0 ≤ W)
    (hproper : g * (H * J) ≤ T) (hprod : T ^ (3 / 4 : ℝ) * W ≤ H * J)
    (hT₀ : 0 ≤ T₀) (hT₀upper : T₀ ≤ T / g ^ 2)
    (hvolume : H * J / (8192 * g) ≤ H₀ * J₀)
    (hwidth₁ : min (H / (128 * g)) (H * J / (512 * Real.sqrt T)) ≤ H₀)
    (hwidth₂ : min (H / (128 * g)) (H * J / (512 * Real.sqrt T)) ≤ J₀) :
    T₀ ^ (1 / 4 : ℝ) * W / 8192 ≤ H₀ ∧
      T₀ ^ (1 / 4 : ℝ) * W / 8192 ≤ J₀ ∧
      T₀ ^ (3 / 4 : ℝ) * W / 8192 ≤ H₀ * J₀ := by
  have hgpos : 0 < g := by linarith
  have hfirst := common_factor_first_width_budget hT hgpos hH hJ hJH hW hproper hprod
  have haxis := common_factor_axis_width_budget hT hg hW hprod
  have hvol := common_factor_volume_budget hT hg hW hprod
  have hquarter := mul_le_mul_of_nonneg_right
    (Real.rpow_le_rpow hT₀ hT₀upper (by norm_num : (0 : ℝ) ≤ 1 / 4)) hW
  have hthreequarter := mul_le_mul_of_nonneg_right
    (Real.rpow_le_rpow hT₀ hT₀upper (by norm_num : (0 : ℝ) ≤ 3 / 4)) hW
  have hmin : T₀ ^ (1 / 4 : ℝ) * W / 8192 ≤
      min (H / (128 * g)) (H * J / (512 * Real.sqrt T)) := by
    apply le_min
    · calc
        _ ≤ (H / g) / 8192 := div_le_div_of_nonneg_right (hquarter.trans hfirst) (by norm_num)
        _ ≤ (H / g) / 128 := by
          have hh : 0 ≤ H / g := by positivity
          linarith
        _ = H / (128 * g) := by ring
    · calc
        _ ≤ (H * J / Real.sqrt T) / 8192 :=
          div_le_div_of_nonneg_right (hquarter.trans haxis) (by norm_num)
        _ ≤ (H * J / Real.sqrt T) / 512 := by
          have hh : 0 ≤ H * J / Real.sqrt T := by positivity
          linarith
        _ = H * J / (512 * Real.sqrt T) := by ring
  refine ⟨hmin.trans hwidth₁, hmin.trans hwidth₂, ?_⟩
  calc
    _ ≤ (H * J / g) / 8192 := div_le_div_of_nonneg_right (hthreequarter.trans hvol) (by norm_num)
    _ = H * J / (8192 * g) := by ring
    _ ≤ H₀ * J₀ := hvolume

theorem absorb_geometric_log_loss {T T₀ S p : ℝ} (B : ℕ)
    (hT₀ : 1 ≤ T₀) (hT₀T : T₀ ≤ T) (hlarge : 8192 ≤ 1 + Real.log T)
    (hbudget : T₀ ^ p * (1 + Real.log T) ^ (B + 1) / 8192 ≤ S) :
    T₀ ^ p * (1 + Real.log T₀) ^ B ≤ S := by
  have hT₀pos : 0 < T₀ := by linarith
  have hTpos : 0 < T := hT₀pos.trans_le hT₀T
  have hΛ₀ : 0 ≤ 1 + Real.log T₀ := by have := Real.log_nonneg hT₀; linarith
  have hΛ : 0 ≤ 1 + Real.log T := by linarith
  have hlogs : 1 + Real.log T₀ ≤ 1 + Real.log T :=
    add_le_add (le_refl 1) (Real.log_le_log hT₀pos hT₀T)
  have hpow : (1 + Real.log T₀) ^ B ≤ (1 + Real.log T) ^ B := pow_le_pow_left₀ hΛ₀ hlogs B
  have hextra : 8192 * (1 + Real.log T) ^ B ≤ (1 + Real.log T) ^ (B + 1) := by
    rw [pow_succ]
    have hh := mul_le_mul_of_nonneg_right hlarge (pow_nonneg hΛ B)
    nlinarith
  calc
    _ ≤ T₀ ^ p * (1 + Real.log T) ^ B := mul_le_mul_of_nonneg_left hpow (Real.rpow_nonneg hT₀pos.le p)
    _ ≤ T₀ ^ p * (1 + Real.log T) ^ (B + 1) / 8192 := by
      apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 8192)).mpr
      have hh := mul_le_mul_of_nonneg_left hextra (Real.rpow_nonneg hT₀pos.le p)
      nlinarith
    _ ≤ S := hbudget

end Erdos587
