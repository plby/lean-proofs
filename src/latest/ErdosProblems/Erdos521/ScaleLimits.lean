/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Geometric-sum asymptotics at distance proportional to the inverse spatial scale.
Formal proof: Codex.
-/
import ErdosProblems.Erdos521.EndpointScale

namespace Erdos521

open Filter
open scoped Topology

theorem inverse_scale_point_tendsto (s : ℕ → ℝ) (hs : Tendsto s atTop atTop) (a : ℝ) :
    Tendsto (fun j ↦ 1 - a / s j) atTop (𝓝 1) := by
  have h := (tendsto_const_nhds (x := (1 : ℝ))).sub ((tendsto_inv_atTop_zero.comp hs).const_mul a)
  simpa only [div_eq_mul_inv, mul_zero, sub_zero, Function.comp_def] using h

theorem eventually_inverse_scale_point_bounds (s : ℕ → ℝ) (hs : Tendsto s atTop atTop)
    {a : ℝ} (ha : 0 < a) :
    ∀ᶠ j : ℕ in atTop, 0 ≤ 1 - a / s j ∧ 1 - a / s j < 1 := by
  filter_upwards [hs.eventually_gt_atTop 0, hs.eventually_ge_atTop a] with j hsj hsa
  refine ⟨sub_nonneg.mpr ((div_le_one hsj).mpr hsa), ?_⟩
  exact sub_lt_self _ (div_pos ha hsj)

theorem inverse_scale_power_tendsto_zero (N : ℕ → ℕ) (s : ℕ → ℝ)
    (hs : Tendsto s atTop atTop) (hN : Tendsto (fun j ↦ (N j : ℝ) / s j) atTop atTop)
    {a : ℝ} (ha : 0 < a) :
    Tendsto (fun j ↦ (1 - a / s j) ^ N j) atTop (𝓝 0) := by
  have hexp : Tendsto (fun j ↦ Real.exp (-a * ((N j : ℝ) / s j))) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp (hN.const_mul_atTop_of_neg (neg_neg_of_pos ha))
  apply squeeze_zero' _ _ hexp
  · exact (eventually_inverse_scale_point_bounds s hs ha).mono fun j hj ↦ pow_nonneg hj.1 _
  · filter_upwards [eventually_inverse_scale_point_bounds s hs ha] with j hj
    have h := pow_le_exp_nat_mul (u := -(a / s j)) hj.1 (by linarith) (N j)
    convert h using 1
    congr 1
    ring

theorem scaled_geometricVariance_tendsto (N : ℕ → ℕ) (s : ℕ → ℝ)
    (hs : Tendsto s atTop atTop) (hN : Tendsto (fun j ↦ (N j : ℝ) / s j) atTop atTop)
    {a : ℝ} (ha : 0 < a) :
    Tendsto (fun j ↦ geometricVariance (1 - a / s j) (N j) / s j) atTop (𝓝 (1 / (2 * a))) := by
  have hdiv : Tendsto (fun j ↦ a / s j) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, mul_zero, Function.comp_def] using (tendsto_inv_atTop_zero.comp hs).const_mul a
  have hden : Tendsto (fun j ↦ a * (2 - a / s j)) atTop (𝓝 (2 * a)) := by
    simpa only [sub_zero, mul_comm a 2] using ((tendsto_const_nhds (x := (2 : ℝ))).sub hdiv).const_mul a
  have htail : Tendsto (fun j ↦ (1 - a / s j) ^ (2 * N j)) atTop (𝓝 0) := by
    have h := (inverse_scale_power_tendsto_zero N s hs hN ha).pow 2
    simpa only [zero_pow (by norm_num : 2 ≠ 0), ← pow_mul, Nat.mul_comm] using h
  have hquot : Tendsto (fun j ↦ (1 - (1 - a / s j) ^ (2 * N j)) / (a * (2 - a / s j)))
      atTop (𝓝 (1 / (2 * a))) := by
    convert ((tendsto_const_nhds (x := (1 : ℝ))).sub htail).div hden (by positivity) using 1 <;>
      first | rfl | simp
  have heq : (fun j ↦ (1 - (1 - a / s j) ^ (2 * N j)) / (a * (2 - a / s j))) =ᶠ[atTop]
      (fun j ↦ geometricVariance (1 - a / s j) (N j) / s j) := by
    filter_upwards [hden.eventually (lt_mem_nhds (by positivity : 0 < 2 * a))] with j hj
    symm
    apply (eq_div_iff hj.ne').mpr
    calc
      (geometricVariance (1 - a / s j) (N j) / s j) * (a * (2 - a / s j)) =
          geometricVariance (1 - a / s j) (N j) * (1 - (1 - a / s j) ^ 2) := by ring
      _ = _ := geometricVariance_mul_one_sub_sq _ _
  exact hquot.congr' heq

end Erdos521
