/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
The balanced expectation error vanishes as a logarithmic grid is refined.
Formal proof: Codex.
-/
import ErdosProblems.Erdos521.RefinementSpacing
import ErdosProblems.Erdos521.RefinementPowers

namespace Erdos521

open Filter
open scoped Topology

theorem refinement_probability_error_tendsto_zero {ℓ C : ℝ} (hℓ : 0 < ℓ) (hC : 0 ≤ C) :
    Tendsto (fun N : ℕ ↦ (N : ℝ) ^ (1 / 6 : ℝ) * N * C *
      (Real.exp (ℓ / N) - 1) ^ (4 / 3 : ℝ)) atTop (𝓝 0) := by
  have hbound : Tendsto (fun N : ℕ ↦ C * (2 * ℓ) ^ (4 / 3 : ℝ) * (N : ℝ) ^ (-(1 / 6 : ℝ)))
      atTop (𝓝 0) := by
    simpa only [mul_zero, Function.comp_def] using
      ((tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 6)).comp
        (tendsto_natCast_atTop_atTop (R := ℝ))).const_mul (C * (2 * ℓ) ^ (4 / 3 : ℝ))
  apply squeeze_zero' _ _ hbound
  · exact Eventually.of_forall (fun N ↦ by
      have hbase : 0 ≤ Real.exp (ℓ / N) - 1 :=
        sub_nonneg.mpr (Real.one_le_exp_iff.mpr (div_nonneg hℓ.le (Nat.cast_nonneg N)))
      positivity)
  · filter_upwards [eventually_refinement_exp_le hℓ, eventually_ge_atTop 1] with N hN hN₁
    have hN₀ : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
    have hbase : 0 ≤ Real.exp (ℓ / N) - 1 :=
      sub_nonneg.mpr (Real.one_le_exp_iff.mpr (div_nonneg hℓ.le hN₀.le))
    calc
      (N : ℝ) ^ (1 / 6 : ℝ) * N * C * (Real.exp (ℓ / N) - 1) ^ (4 / 3 : ℝ) ≤
          (N : ℝ) ^ (1 / 6 : ℝ) * N * C * ((2 * ℓ) / N) ^ (4 / 3 : ℝ) :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hbase hN (by norm_num)) (by positivity)
      _ = _ := refinement_probability_power hN₀ (by positivity) C

theorem refinement_moment_error_tendsto_zero (B : ℝ) :
    Tendsto (fun N : ℕ ↦ B / ((N : ℝ) ^ (1 / 6 : ℝ)) ^ 7) atTop (𝓝 0) := by
  simp_rw [refinement_moment_power (Nat.cast_nonneg _)]
  simpa only [mul_zero, Function.comp_def] using
    ((tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 7 / 6)).comp
      (tendsto_natCast_atTop_atTop (R := ℝ))).const_mul B

end Erdos521
