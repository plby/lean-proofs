import ErdosProblems.Erdos1148.BufferedExcursionRefinement

/-! # A fixed height threshold makes every buffered excursion long enough -/

namespace Erdos1148.DukeArithmetic

theorem exp_neg_buffered_duration_small {H L c : ℝ} (hc : 0 < c)
    (hH : 1 ≤ H) (hL : 0 ≤ L) (hlarge : 96 / c ≤ H) :
    96 * Real.exp (-(L + 4 * Real.log H)) ≤ c := by
  have hHpos : 0 < H := by linarith
  have hexp : Real.exp (-(L + 4 * Real.log H)) ≤ H⁻¹ := by
    calc
      _ ≤ Real.exp (-Real.log H) := Real.exp_le_exp.mpr (by linarith [Real.log_nonneg hH])
      _ = H⁻¹ := by rw [Real.exp_neg, Real.exp_log hHpos]
  calc
    _ ≤ 96 * H⁻¹ := mul_le_mul_of_nonneg_left hexp (by norm_num)
    _ = 96 / H := by rw [div_eq_mul_inv]
    _ ≤ c := (div_le_iff₀ hHpos).mpr (by nlinarith [(div_le_iff₀ hc).mp hlarge])

end Erdos1148.DukeArithmetic
