/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
The bulk condition forces divergence of degree divided by spatial scale.
Formal proof: Codex.
-/
import ErdosProblems.Erdos521.EndpointScale

namespace Erdos521

open Filter
open scoped Topology

theorem bulk_degree_ratio_lower {C s : ℝ} {n : ℕ} (hs : 0 < s) (hn : 0 < n)
    (hbulk : 1 - 1 / s ≤ endpointCenter C n) :
    C * Real.log n ≤ ((n + 1 : ℕ) : ℝ) / s := by
  have hn₀ : (0 : ℝ) < n := by exact_mod_cast hn
  have hdiv : C * Real.log n / n ≤ 1 / s := by dsimp [endpointCenter] at hbulk; linarith
  have hmul := (div_le_iff₀ hn₀).mp hdiv
  have hupper : (n : ℝ) / s ≤ ((n + 1 : ℕ) : ℝ) / s := by
    apply div_le_div_of_nonneg_right _ hs.le
    exact_mod_cast Nat.le_succ n
  calc
    C * Real.log n ≤ (n : ℝ) / s := by
      simpa only [div_eq_mul_inv, one_mul, mul_comm, mul_one] using hmul
    _ ≤ _ := hupper

theorem bulk_degree_ratio_tendsto (n : ℕ → ℕ) (s : ℕ → ℝ) {C : ℝ} (hC : 0 < C)
    (hn : Tendsto n atTop atTop) (hs : Tendsto s atTop atTop)
    (hbulk : ∀ᶠ j : ℕ in atTop, 1 - 1 / s j ≤ endpointCenter C (n j)) :
    Tendsto (fun j ↦ ((n j + 1 : ℕ) : ℝ) / s j) atTop atTop := by
  have hlog := (Real.tendsto_log_atTop.comp ((tendsto_natCast_atTop_atTop (R := ℝ)).comp hn)).const_mul_atTop hC
  apply tendsto_atTop_mono' atTop _ hlog
  filter_upwards [hbulk, hs.eventually_gt_atTop 0, hn.eventually_ge_atTop 1] with j hj hsj hnj
  exact bulk_degree_ratio_lower hsj (by omega) hj

end Erdos521
