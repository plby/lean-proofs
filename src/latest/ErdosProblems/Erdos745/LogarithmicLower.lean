import ErdosProblems.Erdos745.LogarithmicMean
import ErdosProblems.Erdos745.TreeSecondMoment

/-! # Unconditional logarithmic lower bound for every positive noncritical density -/

open Filter
open scoped Topology

namespace Erdos745

noncomputable section

theorem tendsto_logarithmic_pair_correction {lam B : ℝ} (hlam : 0 ≤ lam) (hB : 0 ≤ B) :
    Tendsto (fun n : ℕ ↦ 1 / (1 - (edgeProbability lam n : ℝ)) ^
      (logarithmicOrder B n * logarithmicOrder B n)) atTop (𝓝 1) := by
  have hp := (tendsto_logarithmicOrder_pow_div hB 2).mul (tendsto_n_mul_log_absence lam)
  have ht := (Real.continuous_exp.tendsto _).comp hp.neg
  simp only [zero_mul, neg_zero, Real.exp_zero] at ht
  apply ht.congr'
  filter_upwards [eventually_ge_atTop 1,
    tendsto_natCast_atTop_atTop.eventually_gt_atTop lam] with n hn hln
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hq : 0 < 1 - lam / (n : ℝ) := sub_pos.mpr ((div_lt_one hnR).mpr hln)
  rw [coe_edgeProbability hlam (by omega) hln.le]
  have he : -((logarithmicOrder B n : ℝ) ^ 2 / n *
      ((n : ℝ) * Real.log (1 - lam / n))) =
      -((logarithmicOrder B n * logarithmicOrder B n : ℕ) : ℝ) *
        Real.log (1 - lam / n) := by
    rw [Nat.cast_mul]
    field_simp
  dsimp only [Function.comp_apply]
  rw [he, neg_mul, Real.exp_neg, Real.exp_nat_mul, Real.exp_log hq, one_div]

theorem tendsto_secondLargest_lt_logarithmicOrder {lam B : ℝ}
    (hlam : 0 < lam) (hne : lam ≠ 1) (hB : 0 < B) (hBa : B < logarithmicConstant lam) :
    Tendsto (fun n : ℕ ↦ probability lam n
      (fun G ↦ secondLargestComponentOrder G < logarithmicOrder B n)) atTop (𝓝 0) := by
  have hm := (tendsto_inverse_treeMean_log hlam hne hB hBa).const_mul 4
  have hr := ((tendsto_logarithmic_pair_correction hlam.le hB.le).sub
    (tendsto_const_nhds (x := (1 : ℝ)))).const_mul 4
  have ht := hm.add hr
  simp only [mul_zero, sub_self, add_zero] at ht
  apply squeeze_zero' (Eventually.of_forall fun n ↦ probability_nonneg _ _ _) _ ht
  filter_upwards [eventually_treeMean_log_ge_two hlam hne hB hBa,
    (tendsto_logarithmicOrder hB).eventually_gt_atTop 0,
    eventually_ge_atTop 1,
    tendsto_natCast_atTop_atTop.eventually_gt_atTop lam] with n hm hk hn hln
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hq : 0 < 1 - (edgeProbability lam n : ℝ) := by
    rw [coe_edgeProbability hlam.le (by omega) hln.le]
    exact sub_pos.mpr ((div_lt_one hnR).mpr hln)
  have hk' : 0 < logarithmicOrder B n := by exact_mod_cast hk
  simpa only [mul_one_div] using secondLargest_lt_tree_bound hk' hq hm

theorem noncritical_logarithmic_lower {lam B : ℝ}
    (hlam : 0 < lam) (hne : lam ≠ 1) (hB : 0 < B) (hBa : B < logarithmicConstant lam) :
    WithHighProbabilityAt lam (fun n G ↦ B * Real.log (n : ℝ) ≤ secondOrder n G) := by
  have hb : Tendsto (fun n : ℕ ↦ probability lam n
      (fun G ↦ secondOrder n G < B * Real.log (n : ℝ))) atTop (𝓝 0) := by
    apply squeeze_zero (fun n ↦ probability_nonneg _ _ _) _
      (tendsto_secondLargest_lt_logarithmicOrder hlam hne hB hBa)
    intro n
    apply probability_mono
    intro G hG
    have hr := hG.trans_le (logarithmicOrder_ge B n)
    dsimp only [secondOrder] at hr
    exact_mod_cast hr
  have he (n : ℕ) : probability lam n (fun G ↦ B * Real.log (n : ℝ) ≤ secondOrder n G) =
      1 - probability lam n (fun G ↦ secondOrder n G < B * Real.log (n : ℝ)) := by
    rw [← probability_not]
    simp only [not_lt]
  unfold WithHighProbabilityAt
  simp_rw [he]
  simpa only [sub_zero] using (tendsto_const_nhds (x := (1 : ℝ))).sub hb

end

end Erdos745
