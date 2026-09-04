import ErdosProblems.Erdos69.Parameters
import Mathlib.Analysis.SpecialFunctions.Exp

/-! # Limits governing the explicit parameter hierarchy -/

open Filter
open scoped Topology

namespace Erdos69.Elementary

noncomputable def coefficientMassBound (q : ℝ) (m : ℕ) : ℝ := |q| * (9 / 16 : ℝ) ^ m
noncomputable def firstCoefficient (q : ℝ) (m : ℕ) : ℝ := q / 2 ^ (6 * m + 1)

theorem tendsto_patternSize : Tendsto patternSize atTop atTop :=
  tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℕ) < 36)

theorem tendsto_fluctuationScale : Tendsto fluctuationScale atTop atTop := by
  apply tendsto_atTop_mono' atTop _ tendsto_patternSize
  filter_upwards with m
  change patternSize m ≤ patternSize m ^ 4
  simpa using Nat.pow_le_pow_right (patternSize_pos m) (show 1 ≤ 4 by omega)

theorem tendsto_inverse_patternSize :
    Tendsto (fun m ↦ (1 : ℝ) / patternSize m) atTop (𝓝 0) :=
  tendsto_one_div_atTop_nhds_zero_nat.comp tendsto_patternSize

theorem tendsto_coefficientMassBound (q : ℝ) :
    Tendsto (coefficientMassBound q) atTop (𝓝 0) := by
  change Tendsto (fun m : ℕ ↦ |q| * (9 / 16 : ℝ) ^ m) atTop (𝓝 0)
  simpa only [mul_zero] using
    (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 9 / 16)
      (by norm_num : (9 / 16 : ℝ) < 1)).const_mul |q|

theorem tendsto_index_mul_coefficientMassBound (q : ℝ) :
    Tendsto (fun m : ℕ ↦ (m : ℝ) * coefficientMassBound q m) atTop (𝓝 0) := by
  have h := (hasSum_coe_mul_geometric_of_norm_lt_one
    (r := (9 / 16 : ℝ)) (by norm_num)).summable.tendsto_atTop_zero
  simpa only [coefficientMassBound, mul_left_comm, mul_zero] using h.const_mul |q|

theorem tendsto_coefficientMassBound_affine (q A D : ℝ) :
    Tendsto (fun m ↦ coefficientMassBound q m * (A * m + D)) atTop (𝓝 0) := by
  have h₁ := (tendsto_index_mul_coefficientMassBound q).const_mul A
  have h₂ := (tendsto_coefficientMassBound q).mul_const D
  convert! h₁.add h₂ using 1
  · funext m
    ring
  · ring_nf

theorem tendsto_index_add_one_div_two_pow :
    Tendsto (fun k : ℕ ↦ ((k : ℝ) + 1) / 2 ^ k) atTop (𝓝 0) := by
  have h₁ := (hasSum_coe_mul_geometric_of_norm_lt_one
    (r := (1 / 2 : ℝ)) (by norm_num)).summable.tendsto_atTop_zero
  have h₂ := tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (1 / 2 : ℝ) < 1)
  convert! h₁.add h₂ using 1
  · funext k
    simp only [div_pow, one_pow]
    ring
  · ring_nf

theorem tendsto_scale_tail :
    Tendsto (fun m ↦ ((fluctuationScale m : ℝ) + 1) / 2 ^ fluctuationScale m)
      atTop (𝓝 0) :=
  tendsto_index_add_one_div_two_pow.comp tendsto_fluctuationScale

theorem firstCoefficient_square_scale (q : ℝ) (m : ℕ) :
    firstCoefficient q m ^ 2 * fluctuationScale m =
      (q ^ 2 / 4) * (6561 / 16 : ℝ) ^ m := by
  have hden : (2 : ℝ) ^ (6 * m + 1) = 2 * (64 : ℝ) ^ m := by
    rw [pow_add, pow_mul]
    norm_num
    ring
  have hscale : (fluctuationScale m : ℝ) = ((36 : ℝ) ^ 4) ^ m := by
    simp only [fluctuationScale, patternSize, Nat.cast_pow, Nat.cast_ofNat, pow_right_comm]
  have hratio : (6561 / 16 : ℝ) = 36 ^ 4 / 64 ^ 2 := by norm_num
  rw [firstCoefficient, hden, hscale, hratio]
  simp_rw [div_pow]
  rw [pow_right_comm (64 : ℝ) 2 m]
  ring

theorem tendsto_firstCoefficient_square_scale {q : ℝ} (hq : 0 < q) :
    Tendsto (fun m ↦ firstCoefficient q m ^ 2 * fluctuationScale m) atTop atTop := by
  simp_rw [firstCoefficient_square_scale]
  exact (tendsto_pow_atTop_atTop_of_one_lt
    (by norm_num : (1 : ℝ) < 6561 / 16)).const_mul_atTop (by positivity)

theorem tendsto_independent_decay {q : ℝ} (hq : 0 < q) :
    Tendsto (fun m ↦ Real.exp (-(firstCoefficient q m ^ 2 * fluctuationScale m)))
      atTop (𝓝 0) :=
  Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp (tendsto_firstCoefficient_square_scale hq))

end Erdos69.Elementary
