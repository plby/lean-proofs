/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
The Gaussian limit of normalized Littlewood values approaching an endpoint.
Formal proof: Codex.
-/
import ErdosProblems.Erdos521.WeightedCentralLimit
import ErdosProblems.Erdos521.VarianceLimits

namespace Erdos521

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology

theorem polynomial_value_central_limit (d : ℕ → ℕ) (x : ℕ → ℝ)
    (hd : Tendsto d atTop atTop) (hx : Tendsto x atTop (𝓝 1))
    (hI : ∀ᶠ j : ℕ in atTop, 0 ≤ x j ∧ x j ≤ 1) :
    TendstoInDistribution (fun j ε ↦ powerSum ε (d j + 1) (x j) /
      Real.sqrt (geometricVariance (x j) (d j + 1))) atTop (fun y : ℝ ↦ y)
        (fun _ ↦ sequenceLaw) (gaussianReal 0 1) := by
  let s := fun j ↦ Finset.range (d j + 1)
  let a := fun j i ↦ (x j) ^ i / Real.sqrt (geometricVariance (x j) (d j + 1))
  have hV : Tendsto (fun j ↦ geometricVariance (x j) (d j + 1)) atTop atTop :=
    geometricVariance_tendsto_atTop _ x ((tendsto_add_atTop_nat 1).comp hd) hx
  have hinv : Tendsto (fun j ↦ (Real.sqrt (geometricVariance (x j) (d j + 1)))⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp hV)
  have hsmall : ∀ r : ℝ, 0 < r → ∀ᶠ j : ℕ in atTop, ∀ i ∈ s j, |a j i| < r := by
    intro r hr
    filter_upwards [hI, hinv.eventually (gt_mem_nhds hr)] with j hjI hjinv
    intro i _
    have hsqrt : 0 < Real.sqrt (geometricVariance (x j) (d j + 1)) :=
      Real.sqrt_pos.mpr (geometricVariance_succ_pos _ _)
    dsimp [a]
    rw [abs_div, abs_of_nonneg (pow_nonneg hjI.1 i), abs_of_pos hsqrt]
    exact (div_le_div_of_nonneg_right (pow_le_one₀ hjI.1 hjI.2) hsqrt.le).trans_lt
      (by simpa only [one_div] using hjinv)
  have hvariance : Tendsto (fun j ↦ ∑ i ∈ s j, (a j i) ^ 2) atTop (𝓝 (1 : ℝ)) := by
    have heq : (fun _ : ℕ ↦ (1 : ℝ)) =ᶠ[atTop] (fun j ↦ ∑ i ∈ s j, (a j i) ^ 2) :=
      Eventually.of_forall fun j ↦ (normalized_geometric_variance_sum (d j) (x j)).symm
    exact tendsto_const_nhds.congr' heq
  have h := triangular_sign_central_limit s a 1 hsmall hvariance
  apply h.congr _ (Eventually.of_forall fun _ ↦ rfl)
  intro j
  filter_upwards [] with ε
  dsimp [s, a]
  rw [powerSum, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _
  ring

end Erdos521
