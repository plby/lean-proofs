/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Normalized geometric weights vanish uniformly near the endpoint.
Formal proof: Codex.
-/
import ErdosProblems.Erdos521.ValueCentralLimit

namespace Erdos521

open Filter
open scoped Topology

theorem normalized_geometric_weights_small (d : ℕ → ℕ) (x : ℕ → ℝ)
    (hd : Tendsto d atTop atTop) (hx : Tendsto x atTop (𝓝 1))
    (hI : ∀ᶠ j : ℕ in atTop, 0 ≤ x j ∧ x j ≤ 1) (r : ℝ) (hr : 0 < r) :
    ∀ᶠ j : ℕ in atTop, ∀ i : ℕ,
      |(x j) ^ i / Real.sqrt (geometricVariance (x j) (d j + 1))| < r := by
  have hV := geometricVariance_tendsto_atTop _ x ((tendsto_add_atTop_nat 1).comp hd) hx
  have hinv : Tendsto (fun j ↦ (Real.sqrt (geometricVariance (x j) (d j + 1)))⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp hV)
  filter_upwards [hI, hinv.eventually (gt_mem_nhds hr)] with j hjI hjinv
  intro i
  have hsqrt : 0 < Real.sqrt (geometricVariance (x j) (d j + 1)) :=
    Real.sqrt_pos.mpr (geometricVariance_succ_pos _ _)
  rw [abs_div, abs_of_nonneg (pow_nonneg hjI.1 i), abs_of_pos hsqrt]
  exact (div_le_div_of_nonneg_right (pow_le_one₀ hjI.1 hjI.2) hsqrt.le).trans_lt
    (by simpa only [one_div] using hjinv)

end Erdos521
