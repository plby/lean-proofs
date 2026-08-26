/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Subdivision and translation of logarithmic intervals.
Formal proof: Codex.
-/
import ErdosProblems.Erdos521.RefinedGridEndpoints
import ErdosProblems.Erdos521.RefinementSpacing

namespace Erdos521

open Filter
open scoped Topology

theorem logGrid_shift (s a δ : ℝ) (i k : ℕ) :
    logGrid s a δ (i + k) = logGrid s (logGridCoefficient a δ i) δ k := by
  have he : -((i + k : ℕ) : ℝ) * δ = -(i : ℝ) * δ + -(k : ℝ) * δ := by
    push_cast
    ring
  unfold logGrid logGridCoefficient
  rw [he, Real.exp_add, mul_assoc]

theorem exists_short_logarithmic_subdivision {ℓ : ℝ} (hℓ : 0 < ℓ) :
    ∃ N : ℕ, 1 ≤ N ∧ Real.exp (ℓ / N) - 1 ≤ 1 / 8 := by
  have hspacing : Tendsto (fun N : ℕ ↦ ℓ / (N : ℝ)) atTop (𝓝 0) :=
    (inverse_nat_spacing_tendsto_right hℓ).mono_right nhdsWithin_le_nhds
  have hexp : Tendsto (fun N : ℕ ↦ Real.exp (ℓ / N) - 1) atTop (𝓝 0) := by
    simpa only [Real.exp_zero, sub_self, Function.comp_def] using
      ((Real.continuous_exp.tendsto 0).comp hspacing).sub_const 1
  obtain ⟨N, hN, hsmall⟩ := ((eventually_ge_atTop 1).and
    (hexp.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 8)))).exists
  exact ⟨N, hN, hsmall.le⟩

end Erdos521
