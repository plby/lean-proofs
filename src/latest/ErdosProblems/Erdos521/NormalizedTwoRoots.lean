/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Two-root probabilities on intervals measured relative to the endpoint distance.
Formal proof: Codex.
-/
import ErdosProblems.Erdos521.TwoRootProbability
import ErdosProblems.Erdos521.NormalizedSmallBall
import ErdosProblems.Erdos521.LocalVariance

namespace Erdos521

theorem two_root_energy_normalized_le {a b t V d : ℝ}
    (hab : a < b) (hb : b < 1) (ht : 0 < t) (hV : 0 < V) (_hd : 0 ≤ d)
    (hwidth : b - a ≤ d * (1 - b)) (hVscale : 1 / 4 ≤ V * (1 - b)) :
    24 * (b - a) ^ 4 / ((t * Real.sqrt V) ^ 2 * (1 - b) ^ 5) ≤ 96 * d ^ 4 / t ^ 2 := by
  have hL : 0 < 1 - b := sub_pos.mpr hb
  have hwidth4 := pow_le_pow_left₀ (sub_pos.mpr hab).le hwidth 4
  have hden : t ^ 2 * (1 - b) ^ 4 / 4 ≤ t ^ 2 * V * (1 - b) ^ 5 := by
    have h := mul_le_mul_of_nonneg_left hVscale (by positivity : 0 ≤ t ^ 2 * (1 - b) ^ 4)
    nlinarith
  rw [mul_pow, Real.sq_sqrt hV.le]
  calc
    24 * (b - a) ^ 4 / (t ^ 2 * V * (1 - b) ^ 5) ≤
        (24 * (d * (1 - b)) ^ 4) / (t ^ 2 * (1 - b) ^ 4 / 4) :=
      div_le_div₀ (by positivity) (mul_le_mul_of_nonneg_left hwidth4 (by norm_num)) (by positivity) hden
    _ = _ := by field_simp; ring

theorem two_interval_roots_normalized_probability (n L : ℕ) (hL : 2 * L ≤ n + 1)
    {a b d t : ℝ} (ha : 0 ≤ a) (hab : a < b) (hb₀ : 1 / 2 ≤ b) (hb₁ : b < 1)
    (ht : 0 < t) (hd : 0 ≤ d) (hwidth : b - a ≤ d * (1 - b))
    (htail : b ^ (2 * (n + 1)) ≤ 1 / 2) :
    let c : ℝ := 1 / (4 * Real.pi ^ 2)
    sequenceLaw.real {ε | 2 ≤ intervalRootCount ε n a b} ≤
      Real.exp (1 / 2) * (t * Real.sqrt (Real.pi / c) +
        Real.exp (-c * geometricVariance b (n + 1)) +
        2 * Real.exp (-((t * Real.sqrt (geometricVariance b (n + 1))) * (b ^ L)⁻¹) ^ 2 / 2)) +
        96 * d ^ 4 / t ^ 2 := by
  have hV := geometricVariance_succ_pos b n
  have hδ : 0 < t * Real.sqrt (geometricVariance b (n + 1)) := mul_pos ht (Real.sqrt_pos.mpr hV)
  have hlower := geometricVariance_lower hb₁ (n + 1) htail
  rw [inv_eq_one_div, div_le_iff₀ (by positivity : 0 < 4 * (1 - b))] at hlower
  have hVscale : 1 / 4 ≤ geometricVariance b (n + 1) * (1 - b) := by nlinarith
  apply (two_interval_roots_probability_split n ha hab hb₁ hδ).trans
  exact add_le_add (powerSum_smallBall_normalized n L hL hb₀ hb₁.le ht)
    (two_root_energy_normalized_le hab hb₁ ht hV hd hwidth hVscale)

end Erdos521
