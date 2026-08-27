import ErdosProblems.Erdos745.Model
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Algebra.Order.Floor.Ring

/-! # Integer logarithmic scales and their elementary limits -/

open Filter
open scoped Topology

namespace Erdos745

noncomputable section

def logarithmicOrder (B : ℝ) (n : ℕ) : ℕ := ⌈B * Real.log (n : ℝ)⌉₊

theorem logarithmicOrder_ge (B : ℝ) (n : ℕ) :
    B * Real.log (n : ℝ) ≤ (logarithmicOrder B n : ℝ) := Nat.le_ceil _

theorem eventually_logarithmicOrder_le {B : ℝ} (hB : 0 ≤ B) :
    ∀ᶠ n : ℕ in atTop,
      (logarithmicOrder B n : ℝ) ≤ (B + 1) * Real.log (n : ℝ) := by
  have hlog : Tendsto (fun n : ℕ ↦ Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [hlog.eventually_ge_atTop 1] with n hn
  have hround := Nat.ceil_lt_add_one (mul_nonneg hB (by linarith : 0 ≤ Real.log (n : ℝ)))
  change (logarithmicOrder B n : ℝ) < B * Real.log (n : ℝ) + 1 at hround
  nlinarith

theorem tendsto_logarithmicOrder {B : ℝ} (hB : 0 < B) :
    Tendsto (fun n : ℕ ↦ (logarithmicOrder B n : ℝ)) atTop atTop := by
  have hlog : Tendsto (fun n : ℕ ↦ Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  exact tendsto_atTop_mono (logarithmicOrder_ge B) (hlog.const_mul_atTop hB)

theorem tendsto_logarithmicOrder_pow_div {B : ℝ} (hB : 0 ≤ B) (j : ℕ) :
    Tendsto (fun n : ℕ ↦ (logarithmicOrder B n : ℝ) ^ j / n) atTop (𝓝 0) := by
  have ht : Tendsto (fun n : ℕ ↦ Real.log (n : ℝ) ^ j / n) atTop (𝓝 0) :=
    Real.isLittleO_pow_log_id_atTop.tendsto_div_nhds_zero.comp tendsto_natCast_atTop_atTop
  have ht' := ht.const_mul ((B + 1) ^ j)
  simp only [mul_zero] at ht'
  apply squeeze_zero' (Eventually.of_forall fun n ↦ by positivity) _ ht'
  filter_upwards [eventually_logarithmicOrder_le hB] with n hn
  calc
    _ ≤ ((B + 1) * Real.log (n : ℝ)) ^ j / n :=
      div_le_div_of_nonneg_right (pow_le_pow_left₀ (Nat.cast_nonneg _) hn j) (Nat.cast_nonneg _)
    _ = _ := by rw [mul_pow]; ring

theorem eventually_logarithmicOrder_le_half {B : ℝ} (hB : 0 ≤ B) :
    ∀ᶠ n : ℕ in atTop, 2 * logarithmicOrder B n ≤ n := by
  have ht := tendsto_logarithmicOrder_pow_div hB 1
  simp only [pow_one] at ht
  filter_upwards [ht.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2)),
    eventually_ge_atTop 1] with n hn hn1
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hr := (div_lt_iff₀ hnR).mp hn
  have hle : (2 : ℝ) * logarithmicOrder B n ≤ n := by linarith
  exact_mod_cast hle

theorem tendsto_log_pow_mul_exp {s : ℝ} (hs : 0 < s) (j : ℕ) :
    Tendsto (fun n : ℕ ↦ Real.log (n : ℝ) ^ j *
      Real.exp (-s * Real.log (n : ℝ))) atTop (𝓝 0) := by
  have ht := (isLittleO_pow_exp_pos_mul_atTop j hs).tendsto_div_nhds_zero
  have hlog : Tendsto (fun n : ℕ ↦ Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  simpa only [Function.comp_def, neg_mul, Real.exp_neg, div_eq_mul_inv] using ht.comp hlog

end

end Erdos745
