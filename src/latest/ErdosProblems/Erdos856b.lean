/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos856b.Asymptotics
import ErdosProblems.Erdos856b.Duality

/-!
# Erdős problem 856: the exponent of harmonic LCM avoidance

Problem: https://www.erdosproblems.com/856
Selected claim: https://www.erdosproblems.com/forum/thread/856/proof-claims#proof-claim-85
Selected writeup: https://www.overleaf.com/read/smhxdxnrmkbs#0eb184

Informal authors: RayYoung, Keheng Zhu, Yanping Luo (GPT 5.6 Sol Pro).

`f k N` is the maximum reciprocal sum over subsets of `{1, ..., N}` with no `k`
distinct members having the same pairwise LCM. `M k n r` is the maximum cardinality
of an `r`-uniform family on `Fin n` with no `k` distinct members having equal pairwise unions.

The development proves both weighted transference bounds, existence and duality of the
pressures, and their reduction to the finite-block formula. It uses the repository's proved
Mertens estimate. The prime cutoff and squarefree-kernel argument are simplified: the
logarithmic kernel asymptotic suffices for the full conclusions below.
-/

namespace Erdos856b

open Real Filter
open scoped Topology

/-- Theorem 1.1, with the exact finite-block supremum domain from equation (1.2). -/
theorem erdos_856 (k : ℕ) (hk : 3 ≤ k) :
    Tendsto (fun N : ℕ => log (f k N) / log (log (N : ℝ))) atTop
      (𝓝 (sSup {v : ℝ | ∃ n r : ℕ, 0 < n ∧ 0 < r ∧ r ≤ n ∧
        v = (r : ℝ) / (exp 1 * n) * (M k n r : ℝ) ^ (1 / (r : ℝ))})) := by
  rw [← gamma_eq_finite_block_sup hk]
  exact tendsto_exponentRatio hk

/-- The equivalent matching bounds, with a positive exponent at most one. -/
theorem erdos_856_bounds (k : ℕ) (hk : 3 ≤ k) :
    0 < gamma k ∧ gamma k ≤ 1 ∧
      ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop,
        (log (N : ℝ)) ^ (gamma k - ε) ≤ f k N ∧
          f k N ≤ (log (N : ℝ)) ^ (gamma k + ε) :=
  ⟨gamma_pos hk, gamma_le_one hk, fun _ hε => eventually_matching_bounds hk hε⟩

/-- Theorems 3.1 and 3.5, for every positive weight and every positive error. -/
theorem erdos_856_weighted_bounds (k : ℕ) (hk : 3 ≤ k) {z ε : ℝ}
    (hz : 0 < z) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop,
      (log (N : ℝ)) ^ (log (cosPressure k z) / z - ε) ≤ f k N ∧
        f k N ≤ (log (N : ℝ)) ^ (sunflowerPressure k z - z + ε) := by
  have hlo := weighted_lower_bound hk hz
    (show logPressure k z / z - ε < logPressure k z / z by linarith)
  have hhi := weighted_upper_bound hk hz
    (show sunflowerPressure k z - z < sunflowerPressure k z - z + ε by linarith)
  filter_upwards [hlo, hhi, tendsto_logScale.eventually_gt_atTop 0,
    eventually_gt_atTop (1 : ℕ)] with N hNlo hNhi hL hN1
  have hfpos : 0 < f k N := zero_lt_one.trans_le (one_le_f hk (by omega))
  have hlogN : 0 < log (N : ℝ) := log_pos (by exact_mod_cast hN1)
  have hloglo := (lt_div_iff₀ hL).mp hNlo
  have hloghi := (div_lt_iff₀ hL).mp hNhi
  constructor
  · rw [rpow_def_of_pos hlogN, ← exp_log hfpos]
    apply exp_le_exp.mpr
    simpa only [cosPressure, log_exp, logScale, mul_comm] using hloglo.le
  · rw [rpow_def_of_pos hlogN, ← exp_log hfpos]
    apply exp_le_exp.mpr
    simpa only [logScale, mul_comm] using hloghi.le

/-- The unconditional reduction from weighted pressure to finite extremal quantities. -/
theorem pressure_to_finite_blocks (k : ℕ) (hk : 3 ≤ k) :
    sSup {v : ℝ | ∃ z : ℝ, 0 < z ∧ v = log (cosPressure k z) / z} =
      sSup {v : ℝ | ∃ n r : ℕ, 0 < n ∧ 0 < r ∧ r ≤ n ∧
        v = (r : ℝ) / (exp 1 * n) * (M k n r : ℝ) ^ (1 / (r : ℝ))} :=
  (gamma_eq_sup_log_cosPressure_div hk).symm.trans (gamma_eq_finite_block_sup hk)

end Erdos856b
