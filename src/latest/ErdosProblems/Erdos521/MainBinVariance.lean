/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Uniformly large variances and small terminal tails throughout the central bins.
Formal proof: Codex.
-/
import ErdosProblems.Erdos521.MainBinBulk
import ErdosProblems.Erdos521.DyadicWindowGeometry
import ErdosProblems.Erdos521.WindowScaleGrowth

namespace Erdos521

open Filter
open scoped Topology

theorem dyadic_bin_variance_lower (n k : ℕ) {x : ℝ}
    (hx : x ∈ Set.Icc (dyadicPoint k) (dyadicPoint (k + 1)))
    (htail : x ^ (2 * (n + 1)) ≤ 1 / 2) :
    (2 : ℝ) ^ k / 4 ≤ geometricVariance x (n + 1) := by
  have hx₁ : x < 1 := hx.2.trans_lt (dyadicPoint_lt_one (k + 1))
  have hgap := (le_div_iff₀ (pow_pos (by norm_num : (0 : ℝ) < 2) k)).mp (dyadic_bin_distance hx).2
  apply le_trans _ (geometricVariance_lower hx₁ (n + 1) htail)
  rw [inv_eq_one_div]
  apply (le_div_iff₀ (by positivity : 0 < 4 * (1 - x))).mpr
  nlinarith

theorem bulk_terminal_tail_le {n : ℕ} (hn : 1 ≤ n) {x : ℝ} (hx₀ : 0 ≤ x)
    (hx : x ≤ endpointCenter 1 n) : x ^ (2 * (n + 1)) ≤ (n : ℝ) ^ (-2 : ℝ) := by
  have h := endpointCenter_tail_le (a := 1) (by norm_num) hn (hx₀.trans hx)
  exact (pow_le_pow_left₀ hx₀ hx _).trans (by simpa only [mul_one] using h)

theorem eventually_mainBin_point_variance :
    ∀ᶠ j : ℕ in atTop, ∀ k ∈ mainBinSet j, ∀ x ∈ Set.Icc (dyadicPoint k) (dyadicPoint (k + 1)),
      9 / 10 ≤ x ∧ x < 1 ∧ x ^ (2 * (2 ^ j + 1)) ≤ 1 / 2 ∧
        (2 : ℝ) ^ windowWidthScale j / 4 ≤ geometricVariance x (2 ^ j + 1) := by
  have hdegree : Tendsto (fun j : ℕ ↦ (2 : ℕ) ^ j) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
  have htail : Tendsto (fun j : ℕ ↦ (((2 ^ j : ℕ) : ℝ)) ^ (-2 : ℝ)) atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 2)).comp
      ((tendsto_natCast_atTop_atTop (R := ℝ)).comp hdegree)
  filter_upwards [eventually_mainBin_lower, eventually_mainBin_bulk 1,
    htail.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2)), hdegree.eventually_ge_atTop 1]
    with j hl hu ht hj
  intro k hk x hx
  have hxlow : 9 / 10 ≤ x := (hl k hk).trans hx.1
  have hx₀ : 0 ≤ x := by linarith
  have hxtail := (bulk_terminal_tail_le hj hx₀ (hx.2.trans (hu k hk))).trans ht.le
  refine ⟨hxlow, hx.2.trans_lt (dyadicPoint_lt_one (k + 1)), hxtail, ?_⟩
  have hqk : windowWidthScale j ≤ k := (Nat.sqrt_le_self (Nat.sqrt j)).trans (mainBinSet_mem hk).1
  exact (div_le_div_of_nonneg_right (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hqk) (by norm_num)).trans
    (dyadic_bin_variance_lower (2 ^ j) k hx hxtail)

theorem eventually_mainBin_variance_ge (C p : ℝ) :
    ∀ᶠ j : ℕ in atTop, ∀ k ∈ mainBinSet j, ∀ x ∈ Set.Icc (dyadicPoint k) (dyadicPoint (k + 1)),
      C * (j : ℝ) ^ p ≤ geometricVariance x (2 ^ j + 1) := by
  filter_upwards [eventually_mainBin_point_variance, eventually_const_mul_rpow_le_window_scale (4 * C) p]
    with j hj hgrowth
  intro k hk x hx
  have hV := (hj k hk x hx).2.2.2
  nlinarith

end Erdos521
