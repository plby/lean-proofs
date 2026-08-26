/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Endpoint scaling limits along logarithmic grids.
Formal proof: Codex.
-/
import ErdosProblems.Erdos521.LogGrid
import ErdosProblems.Erdos521.ScaleLimits

namespace Erdos521

open Filter
open scoped Topology

theorem logGrid_point_tendsto (s : ℕ → ℝ) (hs : Tendsto s atTop atTop) (a δ : ℝ) (i : ℕ) :
    Tendsto (fun j ↦ logGrid (s j) a δ i) atTop (𝓝 1) :=
  inverse_scale_point_tendsto s hs (logGridCoefficient a δ i)

theorem eventually_logGrid_point_bounds (s : ℕ → ℝ) (hs : Tendsto s atTop atTop)
    {a : ℝ} (ha : 0 < a) (δ : ℝ) (i : ℕ) :
    ∀ᶠ j : ℕ in atTop, 0 ≤ logGrid (s j) a δ i ∧ logGrid (s j) a δ i < 1 :=
  eventually_inverse_scale_point_bounds s hs (logGridCoefficient_pos ha δ i)

theorem logGrid_tail_tendsto_zero (n : ℕ → ℕ) (s : ℕ → ℝ)
    (hs : Tendsto s atTop atTop)
    (hN : Tendsto (fun j ↦ ((n j + 1 : ℕ) : ℝ) / s j) atTop atTop)
    {a : ℝ} (ha : 0 < a) (δ : ℝ) (i : ℕ) :
    Tendsto (fun j ↦ logGrid (s j) a δ i ^ (2 * (n j + 1))) atTop (𝓝 0) := by
  have h := (inverse_scale_power_tendsto_zero (fun j ↦ n j + 1) s hs hN
    (logGridCoefficient_pos ha δ i)).pow 2
  simpa only [logGrid, zero_pow (by norm_num : 2 ≠ 0), ← pow_mul, Nat.mul_comm] using h

end Erdos521
