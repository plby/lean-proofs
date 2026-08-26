/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Divergence and normalization of geometric variances near an endpoint.
Formal proof: Codex.
-/
import ErdosProblems.Erdos521.SmallBall

namespace Erdos521

open Filter
open scoped BigOperators Topology

theorem geometricVariance_tendsto_atTop (N : ℕ → ℕ) (x : ℕ → ℝ)
    (hN : Tendsto N atTop atTop) (hx : Tendsto x atTop (𝓝 1)) :
    Tendsto (fun j ↦ geometricVariance (x j) (N j)) atTop atTop := by
  apply tendsto_atTop.mpr
  intro B
  obtain ⟨K, hK⟩ := exists_nat_gt B
  have hcont : Continuous (fun y : ℝ ↦ geometricVariance y K) := by
    unfold geometricVariance
    fun_prop
  have hfix : Tendsto (fun j ↦ geometricVariance (x j) K) atTop (𝓝 (K : ℝ)) := by
    simpa only [geometricVariance, one_pow, Finset.sum_const, Finset.card_range,
      nsmul_eq_mul, mul_one, Function.comp_def] using hcont.continuousAt.tendsto.comp hx
  filter_upwards [hN.eventually_ge_atTop K, hfix.eventually (lt_mem_nhds hK)] with j hjN hjx
  exact hjx.le.trans (geometricVariance_mono (x j) hjN)

theorem normalized_geometric_variance_sum (n : ℕ) (x : ℝ) :
    (∑ i ∈ Finset.range (n + 1), (x ^ i / Real.sqrt (geometricVariance x (n + 1))) ^ 2) = 1 := by
  have hV := geometricVariance_succ_pos x n
  simp_rw [div_pow, Real.sq_sqrt hV.le]
  rw [← Finset.sum_div]
  have hsum : (∑ i ∈ Finset.range (n + 1), (x ^ i) ^ 2) = geometricVariance x (n + 1) := by
    simp only [geometricVariance, ← pow_mul, Nat.mul_comm]
  rw [hsum, div_self hV.ne']

end Erdos521
