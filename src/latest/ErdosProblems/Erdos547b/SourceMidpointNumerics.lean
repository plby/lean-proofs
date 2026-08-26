/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.SourceClaim617PathNumerics

/-! # Conservative midpoint factors and integral two-tier path counts -/

noncomputable section

namespace Erdos547b.ZhaoSourceMidpointNumerics

open Erdos547b.ZhaoSourceParameterSchedule Erdos547b.ZhaoSourceDegreeFormBounds
open Erdos547b.ZhaoSourceClaim617PathNumerics

theorem midpoint_factors {α : ℚ} (hα : 0 < α) (hα1 : α ≤ 1 / 4) :
    99 / 100 ≤ 1 - 2 * eta α - 2 * epsilon α ∧
    99 / 100 ≤ 1 - rootTypicality α ∧
    99 / 100 ≤ 1 - 2 * fourthRoot α ^ 2 - rootTypicality α - epsilon α ∧
    99 / 100 ≤ 1 - degreeError α := by
  obtain ⟨_, _, he0, ht0, _, _, _, _⟩ := parameter_pos hα
  obtain ⟨hr11, hrr1, her, hte3, hdt, hgd, hepg⟩ := parameter_upper_bounds hα hα1
  have he1 : eta α ≤ 1 := by linarith only [hr11, hrr1, her]
  have he3 : eta α ^ 3 ≤ 1 := by
    simpa only [one_pow] using pow_le_pow_left₀ he0.le he1 3
  have ht1 : fourthRoot α ≤ 1 := by linarith only [hte3, he3]
  have ht2 : fourthRoot α ^ 2 ≤ fourthRoot α := pow_succ_le_self ht0.le ht1 1
  have hδ := (rootTypicality_margin hα hα1).2
  exact ⟨by linarith only [hr11, hrr1, her, hepg, hgd, hdt, hte3, he3],
    by linarith only [hδ, ht2, hte3, he3],
    by linarith only [ht2, hte3, he3, hδ, hepg, hgd, hdt],
    by linarith only [hdt, hte3, he3]⟩

theorem low_coefficient_margin {α : ℚ} (hα : 0 < α) (hα1 : α ≤ 1 / 4) :
    9 / 2 ≤ (1 - 2 * eta α - 2 * epsilon α) * (1 - rootTypicality α) *
      (1 - 2 * fourthRoot α ^ 2 - rootTypicality α - epsilon α) *
      (1 - degreeError α) * (49 / 10) := by
  obtain ⟨h₁, h₂, h₃, h₄⟩ := midpoint_factors hα hα1
  calc
    (9 / 2 : ℚ) ≤ (99 / 100) * (99 / 100) * (99 / 100) * (99 / 100) * (49 / 10) := by norm_num
    _ ≤ _ := by gcongr

theorem high_coefficient_margin {α : ℚ} (hα : 0 < α) (hα1 : α ≤ 1 / 4) :
    5 ≤ (1 - 2 * eta α - 2 * epsilon α) * (1 - rootTypicality α) *
      (1 - degreeError α) * (49 / 10) * 2 := by
  obtain ⟨h₁, h₂, _, h₄⟩ := midpoint_factors hα hα1
  calc
    (5 : ℚ) ≤ (99 / 100) * (99 / 100) * (99 / 100) * (49 / 10) * 2 := by norm_num
    _ ≤ _ := by gcongr

theorem degree_scale_large {α : ℚ} {q M : ℕ}
    (hα : 0 < α) (hα1 : α ≤ 1 / 4) (horder : orderThreshold α M ≤ q) :
    (1000000 : ℝ) < (degreeError α : ℝ) * q := by
  have he0 := (parameter_pos hα).2.2.2.2.2.2.2
  have he1 := (path_coefficient_bounds hα hα1).2.2
  have he4 : epsilon α ^ 4 ≤ epsilon α := pow_succ_le_self he0.le he1 3
  obtain ⟨_, _, _, _, he, hd⟩ := reservoir_cleanup_bounds hα hα1
  have hd0 := (parameter_pos hα).2.2.2.2.1
  have he4d : epsilon α ^ 4 ≤ degreeError α := by linarith only [he4, he, hd0]
  have hp := orderThreshold_product hα horder
  have hM : (1 : ℚ) ≤ ((M : ℚ) + 1) ^ 2 := by
    nlinarith only [sq_nonneg (M : ℚ), (Nat.cast_nonneg M : (0 : ℚ) ≤ M)]
  have hm := mul_le_mul_of_nonneg_right he4d (Nat.cast_nonneg q : (0 : ℚ) ≤ q)
  exact_mod_cast (show (1000000 : ℚ) < degreeError α * q by nlinarith only [hp, hM, hm])

theorem five_degreeError_lt_rho {α : ℚ} (hα : 0 < α) (hα1 : α ≤ 1 / 4) :
    5 * degreeError α < rho α := by
  have h := high_reservoir_margin hα hα1
  have hσ := (reservoir_cleanup_bounds hα hα1).2.1
  have hρ := (parameter_pos hα).2.1
  have hm := mul_le_mul_of_nonneg_left (hσ.trans (by norm_num : (1 / 16 : ℚ) ≤ 1)) hρ.le
  simpa only [mul_one] using h.trans_le hm

def highCount (α : ℚ) (q : ℕ) : ℕ := ⌈5 * (degreeError α : ℝ) * q⌉₊

theorem highCount_le_postponed {α : ℚ} {q : ℕ} (hα : 0 < α) (hα1 : α ≤ 1 / 4) :
    highCount α q ≤ postponedCount α q := by
  have hρ : (0 : ℝ) < rho α := by exact_mod_cast (parameter_pos hα).2.1
  have hdρ : 5 * (degreeError α : ℝ) < rho α := by exact_mod_cast five_degreeError_lt_rho hα hα1
  apply Nat.ceil_le_ceil
  exact mul_le_mul_of_nonneg_right (by linarith only [hdρ, hρ]) (Nat.cast_nonneg q)

theorem postponedCount_lt_low_capacity {α : ℚ} {q M : ℕ}
    (hα : 0 < α) (hα1 : α ≤ 1 / 4) (horder : orderThreshold α M ≤ q) :
    (postponedCount α q : ℝ) < (9 / 2 : ℝ) * (rho α : ℝ) * q := by
  have hdq := degree_scale_large hα hα1 horder
  have hdρ : 5 * (degreeError α : ℝ) < rho α := by exact_mod_cast five_degreeError_lt_rho hα hα1
  have hm := mul_le_mul_of_nonneg_right hdρ.le (Nat.cast_nonneg q : (0 : ℝ) ≤ q)
  have hr : (0 : ℝ) ≤ rho α := by exact_mod_cast (parameter_pos hα).2.1.le
  have hc : (postponedCount α q : ℝ) < 4 * (rho α : ℝ) * q + 1 := Nat.ceil_lt_add_one (by positivity)
  linarith only [hdq, hm, hc]

theorem highCount_lt_high_capacity {α : ℚ} {q M : ℕ}
    (hα : 0 < α) (hα1 : α ≤ 1 / 4) (horder : orderThreshold α M ≤ q) :
    (highCount α q : ℝ) < 5 * (rho α : ℝ) * (fourthRoot α : ℝ) ^ 2 * q := by
  have hdq := degree_scale_large hα hα1 horder
  have hmargin : 5 * (degreeError α : ℝ) < (rho α : ℝ) * (fourthRoot α : ℝ) ^ 2 := by
    exact_mod_cast high_reservoir_margin hα hα1
  have hm := mul_le_mul_of_nonneg_right hmargin.le (Nat.cast_nonneg q : (0 : ℝ) ≤ q)
  have hd : (0 : ℝ) ≤ degreeError α := by exact_mod_cast (parameter_pos hα).2.2.2.2.1.le
  have hc : (highCount α q : ℝ) < 5 * (degreeError α : ℝ) * q + 1 := Nat.ceil_lt_add_one (by positivity)
  nlinarith only [hdq, hm, hc]

theorem low_degree_integer {α : ℚ} {q deg : ℕ}
    (hdeg : (1 - 5 * (degreeError α : ℝ)) * q ≤ (deg : ℝ)) : q - highCount α q ≤ deg := by
  have hc : 5 * (degreeError α : ℝ) * q ≤ (highCount α q : ℝ) := Nat.le_ceil _
  have h : (q : ℝ) ≤ (deg : ℝ) + highCount α q := by nlinarith only [hdeg, hc]
  have hnat : q ≤ deg + highCount α q := by exact_mod_cast h
  omega

end Erdos547b.ZhaoSourceMidpointNumerics

#print axioms Erdos547b.ZhaoSourceMidpointNumerics.midpoint_factors
#print axioms Erdos547b.ZhaoSourceMidpointNumerics.highCount_le_postponed
#print axioms Erdos547b.ZhaoSourceMidpointNumerics.postponedCount_lt_low_capacity
#print axioms Erdos547b.ZhaoSourceMidpointNumerics.highCount_lt_high_capacity
#print axioms Erdos547b.ZhaoSourceMidpointNumerics.low_degree_integer
