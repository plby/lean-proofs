/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Sign-change probabilities for Littlewood values converge to Gaussian probabilities.
Formal proof: Codex.
-/
import ErdosProblems.Erdos521.PairSignLimit

namespace Erdos521

open MeasureTheory ProbabilityTheory Filter
open scoped Topology

theorem normalized_powerSum_product_neg_iff (ε : ℕ → ℝ) (n : ℕ) (x y : ℝ) :
    (powerSum ε (n + 1) x / Real.sqrt (geometricVariance x (n + 1))) *
        (powerSum ε (n + 1) y / Real.sqrt (geometricVariance y (n + 1))) < 0 ↔
      powerSum ε (n + 1) x * powerSum ε (n + 1) y < 0 := by
  rw [div_mul_div_comm, div_lt_iff₀ (mul_pos
    (Real.sqrt_pos.mpr (geometricVariance_succ_pos x n))
    (Real.sqrt_pos.mpr (geometricVariance_succ_pos y n))), zero_mul]

theorem polynomial_sign_probability_tendsto (d : ℕ → ℕ) (s : ℕ → ℝ)
    (hd : Tendsto d atTop atTop) (hs : Tendsto s atTop atTop)
    (hN : Tendsto (fun j ↦ ((d j + 1 : ℕ) : ℝ) / s j) atTop atTop)
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    Tendsto (fun j ↦ sequenceLaw.real {ε |
      powerSum ε (d j + 1) (1 - a / s j) * powerSum ε (d j + 1) (1 - b / s j) < 0}) atTop
      (𝓝 ((gaussianPair (2 * Real.sqrt (a * b) / (a + b))).real pairSignFlip)) := by
  have h := pair_sign_probability_tendsto (inverse_scale_correlation_sq_le_one ha hb)
    (polynomial_value_pair_central_limit d s hd hs hN ha hb)
  simpa only [PiLp.toLp_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    normalized_powerSum_product_neg_iff] using h

end Erdos521
