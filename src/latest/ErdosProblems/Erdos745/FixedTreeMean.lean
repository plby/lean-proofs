import ErdosProblems.Erdos745.MeanBounds
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds

/-! # Fixed-order tree-component density limits -/

open Filter
open scoped BigOperators Topology

namespace Erdos745

noncomputable section

theorem tree_absent_count_cast_pos {n k : ℕ} (hk : 0 < k) (hkn : k ≤ n) :
    ((n.choose 2 - (n - k).choose 2 - (k - 1) : ℕ) : ℝ) =
      (k : ℝ) * n - (k : ℝ) * ((k : ℝ) + 3) / 2 + 1 := by
  by_cases hk2 : 2 ≤ k
  · exact tree_absent_count_cast hk2 hkn
  · have hk1 : k = 1 := by omega
    subst k
    rw [choose_two_difference hkn]
    norm_num [Nat.cast_sub hkn]
    ring

theorem tendsto_fallingProduct (k : ℕ) :
    Tendsto (fun n ↦ fallingProduct n k) atTop (𝓝 1) := by
  have ht (i : ℕ) : Tendsto (fun n : ℕ ↦ 1 - (i : ℝ) / n) atTop (𝓝 1) := by
    simpa using tendsto_const_nhds.sub (tendsto_const_div_atTop_nhds_zero_nat (i : ℝ))
  simpa only [Finset.prod_const_one, fallingProduct] using
    tendsto_finsetProd (Finset.range k) (fun i _ ↦ ht i)

theorem tendsto_tree_absent_count_div {k : ℕ} (hk : 0 < k) :
    Tendsto (fun n : ℕ ↦
      ((n.choose 2 - (n - k).choose 2 - (k - 1) : ℕ) : ℝ) / n) atTop (𝓝 (k : ℝ)) := by
  have ht := (tendsto_const_nhds (x := (k : ℝ))).add (tendsto_const_div_atTop_nhds_zero_nat
    (1 - (k : ℝ) * ((k : ℝ) + 3) / 2))
  simp only [add_zero] at ht
  apply ht.congr'
  filter_upwards [eventually_ge_atTop k] with n hn
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  rw [tree_absent_count_cast_pos hk hn]
  field_simp
  ring

theorem tendsto_n_mul_log_absence (lam : ℝ) :
    Tendsto (fun n : ℕ ↦ (n : ℝ) * Real.log (1 - lam / n)) atTop (𝓝 (-lam)) := by
  have ht : Tendsto (fun n : ℕ ↦ (n : ℝ) * (-lam / n)) atTop (𝓝 (-lam)) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
    field_simp
  simpa only [neg_div, sub_eq_add_neg] using Real.tendsto_nat_mul_log_one_add_of_tendsto ht

theorem tendsto_tree_absence_power {k : ℕ} (hk : 0 < k) (lam : ℝ) :
    Tendsto (fun n : ℕ ↦ (1 - lam / (n : ℝ)) ^
      (n.choose 2 - (n - k).choose 2 - (k - 1))) atTop (𝓝 (Real.exp (-lam * k))) := by
  have ht := (Real.continuous_exp.tendsto ((k : ℝ) * -lam)).comp
    ((tendsto_tree_absent_count_div hk).mul (tendsto_n_mul_log_absence lam))
  have heq : (k : ℝ) * -lam = -lam * k := by ring
  rw [heq] at ht
  apply ht.congr'
  filter_upwards [eventually_ge_atTop 1,
    tendsto_natCast_atTop_atTop.eventually_gt_atTop lam] with n hn hlamn
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hq : 0 < 1 - lam / (n : ℝ) := by
    have := (div_lt_one hnR).mpr hlamn
    linarith
  have he : (((n.choose 2 - (n - k).choose 2 - (k - 1) : ℕ) : ℝ) / n) *
      ((n : ℝ) * Real.log (1 - lam / n)) =
      ((n.choose 2 - (n - k).choose 2 - (k - 1) : ℕ) : ℝ) * Real.log (1 - lam / n) := by
    field_simp
  simp only [Function.comp_apply]
  rw [he, Real.exp_nat_mul, Real.exp_log hq]

/-- The limiting number of tree components of order `k`, divided by `n`. -/
def treeDensity (lam : ℝ) (k : ℕ) : ℝ :=
  (labelledTreeCount k : ℝ) * lam ^ (k - 1) / k.factorial * Real.exp (-lam * k)

theorem treeMean_div_eq_product {n k : ℕ} (hn : 0 < n) (hk : 0 < k) (hkn : k ≤ n)
    {lam : ℝ} (hlam : 0 ≤ lam) (hlamn : lam ≤ n) :
    treeMean lam n k / n =
      ((labelledTreeCount k : ℝ) * lam ^ (k - 1) / k.factorial) * fallingProduct n k *
        (1 - lam / (n : ℝ)) ^ (n.choose 2 - (n - k).choose 2 - (k - 1)) := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hpow : (n : ℝ) ^ k * (lam / n) ^ (k - 1) = (n : ℝ) * lam ^ (k - 1) := by
    have he : (n : ℝ) ^ k = (n : ℝ) ^ (k - 1) * n := by
      conv_lhs => arg 2; rw [← Nat.sub_add_cancel hk]
      rw [pow_succ]
    rw [he, div_pow]
    field_simp
  rw [treeMean, coe_edgeProbability hlam hn hlamn, choose_eq_fallingProduct hn hkn]
  calc
    _ = (((n : ℝ) ^ k * (lam / n) ^ (k - 1)) / n) *
        ((labelledTreeCount k : ℝ) / k.factorial) * fallingProduct n k *
          (1 - lam / (n : ℝ)) ^ (n.choose 2 - (n - k).choose 2 - (k - 1)) := by ring
    _ = _ := by rw [hpow]; field_simp

theorem tendsto_treeMean_div {k : ℕ} (hk : 0 < k) {lam : ℝ} (hlam : 0 ≤ lam) :
    Tendsto (fun n ↦ treeMean lam n k / n) atTop (𝓝 (treeDensity lam k)) := by
  have ht := ((tendsto_const_nhds
    (x := (labelledTreeCount k : ℝ) * lam ^ (k - 1) / k.factorial)).mul
    (tendsto_fallingProduct k)).mul
    (tendsto_tree_absence_power hk lam)
  simp only [mul_one] at ht
  apply ht.congr'
  filter_upwards [eventually_ge_atTop k,
    tendsto_natCast_atTop_atTop.eventually_ge_atTop lam] with n hkn hlamn
  exact (treeMean_div_eq_product (by omega) hk hkn hlam hlamn).symm

end

end Erdos745
