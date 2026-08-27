import Arxiv.Arxiv2411_18291.RatioPerturbation

/-! # A lower bound on the critical-window exponent with a half-width step bound -/

noncomputable section

namespace Arxiv2411_18291

def criticalExponent (w B V : ℝ) : ℝ := (w - B) ^ 2 / (2 * (V + (w - B) * B))

theorem criticalExponent_lower_bound {w B V U : ℝ} (hB : 0 < B) (hV : 0 ≤ V)
    (hhalf : B ≤ w / 2) (hbudget : V + w * B ≤ U) :
    w ^ 2 / (8 * U) ≤ criticalExponent w B V := by
  have hw : 0 < w := by linarith only [hB, hhalf]
  have hgap : 0 < w - B := by linarith only [hB, hhalf]
  have hgaplo : w / 2 ≤ w - B := by linarith only [hhalf]
  have hsq := pow_le_pow_left₀ (half_pos hw).le hgaplo 2
  have hnum : w ^ 2 / 4 ≤ (w - B) ^ 2 := by nlinarith only [hsq]
  have hbase : 0 < V + w * B := add_pos_of_nonneg_of_pos hV (mul_pos hw hB)
  have hU : 0 < U := hbase.trans_le hbudget
  have hdenpos : 0 < 2 * (V + (w - B) * B) := by positivity
  have hden : V + (w - B) * B ≤ U := by
    have h := mul_le_mul_of_nonneg_right (show w - B ≤ w by linarith only [hB]) hB.le
    exact (add_le_add le_rfl h).trans hbudget
  unfold criticalExponent
  calc
    _ = (w ^ 2 / 4) / (2 * U) := by ring
    _ ≤ (w - B) ^ 2 / (2 * U) := div_le_div_of_nonneg_right hnum (by positivity)
    _ ≤ _ := by
      apply (div_le_div_iff₀ (mul_pos (by norm_num) hU) hdenpos).mpr
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hden (by norm_num : (0 : ℝ) ≤ 2)) (sq_nonneg _)

end Arxiv2411_18291
