/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Almost-sure concentration of the capped central-window statistic for arbitrary deterministic grids.
Formal proof: Codex.
-/
import ErdosProblems.Erdos521.CappedCentralSum
import ErdosProblems.Erdos521.WindowConcentrationScale
import ErdosProblems.Erdos521.SummableDeviations

namespace Erdos521

open MeasureTheory Filter
open scoped Topology

theorem cappedCentralSum_normalized_probability {j : ℕ} (hj : 9 ≤ j)
    (g : ℕ → ℕ → ℝ) (N : ℕ → ℕ) {η : ℝ} (hη : 0 < η) :
    sequenceLaw.real {ε | η ≤ |(cappedCentralSum ε j g N - ∫ ζ, cappedCentralSum ζ j g N ∂sequenceLaw) / j|} ≤
      2 * Real.exp (-(η ^ 2 / 36) * (j : ℝ) ^ (1 / 4 : ℝ)) := by
  have hj₀ : (0 : ℝ) < j := by exact_mod_cast (show 0 < j by omega)
  have heq : {ε | η ≤ |(cappedCentralSum ε j g N - ∫ ζ, cappedCentralSum ζ j g N ∂sequenceLaw) / j|} =
      {ε | η * j ≤ |cappedCentralSum ε j g N - ∫ ζ, cappedCentralSum ζ j g N ∂sequenceLaw|} := by
    ext ε
    simp only [Set.mem_ofPred_eq, abs_div, abs_of_pos hj₀, le_div_iff₀ hj₀]
  rw [heq]
  apply (cappedCentralSum_concentration j g N (mul_nonneg hη.le hj₀.le)).trans
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  exact Real.exp_le_exp.mpr (window_concentration_exponent_le hj η)

theorem ae_cappedCentralSum_centered_div_index_tendsto_zero
    (g : ℕ → ℕ → ℕ → ℝ) (N : ℕ → ℕ → ℕ) :
    ∀ᵐ ε ∂sequenceLaw, Tendsto (fun j : ℕ ↦
      (cappedCentralSum ε j (g j) (N j) - ∫ ζ, cappedCentralSum ζ j (g j) (N j) ∂sequenceLaw) / j)
      atTop (𝓝 0) := by
  apply ae_tendsto_zero_of_deviation_power_bound sequenceLaw
    (fun j ε ↦ (cappedCentralSum ε j (g j) (N j) - ∫ ζ, cappedCentralSum ζ j (g j) (N j) ∂sequenceLaw) / j)
    (p := 3) (by norm_num)
  intro η hη
  refine ⟨2, ?_⟩
  have hc : 0 < η ^ 2 / 36 := by positivity
  filter_upwards [eventually_exp_neg_rpow_le_rpow hc (by norm_num : (0 : ℝ) < 1 / 4) (-3),
    eventually_ge_atTop 9] with j hj hj₉
  exact (cappedCentralSum_normalized_probability hj₉ (g j) (N j) hη).trans
    (mul_le_mul_of_nonneg_left hj (by norm_num))

end Erdos521
