import ErdosProblems.Erdos421.ComparableWindowScales

/-! # Common upper-endpoint scales for the long-interval asymptotics -/

namespace Erdos421

open Filter Topology

theorem half_interval_log_bounds {a b : ℝ} (hb : 4 ≤ b) (ha : b / 2 ≤ a) (hab : a ≤ b) :
    1 < a ∧ 0 < Real.log a ∧ Real.log b / 2 ≤ Real.log a ∧ Real.log a ≤ Real.log b := by
  have ha1 : 1 < a := by linarith
  have hap : 0 < a := by linarith
  have hbp : 0 < b := by linarith
  have hlog4 := Real.log_le_log (by norm_num : (0 : ℝ) < 4) hb
  rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.log_pow] at hlog4
  norm_num only [Nat.cast_ofNat] at hlog4
  have hhalf := Real.log_le_log (div_pos hbp (by norm_num : (0 : ℝ) < 2)) ha
  rw [Real.log_div hbp.ne' (by norm_num : (2 : ℝ) ≠ 0)] at hhalf
  exact ⟨ha1, Real.log_pos ha1, by linarith, Real.log_le_log hap hab⟩

theorem half_interval_quadratic_error {a b : ℝ} (hb : 4 ≤ b) (ha : b / 2 ≤ a) (hab : a ≤ b) :
    (b - a) ^ 2 / (a * (Real.log a) ^ 2) ≤ 8 * (b - a) ^ 2 / (b * (Real.log b) ^ 2) := by
  obtain ⟨ha1, hla, hhalf, _⟩ := half_interval_log_bounds hb ha hab
  have hbp : 0 < b := by linarith
  have hlb : 0 < Real.log b := Real.log_pos (by linarith)
  have hden : (b * (Real.log b) ^ 2) / 8 ≤ a * (Real.log a) ^ 2 := by
    have hm := mul_le_mul ha (pow_le_pow_left₀ (by positivity : 0 ≤ Real.log b / 2) hhalf 2)
      (sq_nonneg (Real.log b / 2)) (by linarith : 0 ≤ a)
    nlinarith
  calc
    _ ≤ (b - a) ^ 2 / ((b * (Real.log b) ^ 2) / 8) :=
      div_le_div_of_nonneg_left (sq_nonneg _) (by positivity) hden
    _ = _ := by field_simp

theorem eventually_constant_le_log_scale {C ε : ℝ} (hC : 0 ≤ C) (hε : 0 < ε) (A : ℝ) :
    ∀ᶠ b : ℝ in atTop, C ≤ ε * b / (Real.log b) ^ A := by
  have hCp : 0 < C + 1 := by linarith
  have hlim := (isLittleO_log_rpow_rpow_atTop A (by norm_num : (0 : ℝ) < 1)).tendsto_div_nhds_zero
  filter_upwards [hlim.eventually (gt_mem_nhds (div_pos hε hCp)), eventually_gt_atTop 1]
    with b hsmall hb
  have hbp : 0 < b := by linarith
  have hlb := Real.log_pos hb
  have hp : 0 < (Real.log b) ^ A := Real.rpow_pos_of_pos hlb A
  norm_num only [Real.rpow_one] at hsmall
  have hs := (div_le_iff₀ hbp).mp hsmall.le
  have hm : (C + 1) * (Real.log b) ^ A ≤ ε * b := by
    calc
      _ ≤ (C + 1) * (ε / (C + 1) * b) := mul_le_mul_of_nonneg_left hs hCp.le
      _ = _ := by field_simp
  apply (le_div_iff₀ hp).mpr
  nlinarith

end Erdos421
