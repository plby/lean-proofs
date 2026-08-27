/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.ReserveRegularizationPowerScalars
import ErdosProblems.Erdos207.SourceReservePowerFailure

/-! # Retain the factor two in the actual vortex-size ratio during reserve preparation -/

namespace Erdos207

open scoped NNReal

theorem power_vortex_inner_density_margin
    (t n u p eta eta0 : ℝ≥0) (b step : ℕ) (ht : 2 ≤ t)
    (hstep : 4*b+2 ≤ step) (hp : 1/t^b ≤ p) (heta : eta0 ≤ eta)
    (hcoefficient : 1536 ≤ eta0^6*t) (hsize : t^step*u ≤ 2*n) :
    u ≤ p^4*eta^6*n/1536 := by
  have ht1 : 1 ≤ t := (by norm_num : (1 : ℝ≥0) ≤ 2).trans ht
  have ht0 : 0 < t := zero_lt_one.trans_le ht1
  have hstep1 : 1 ≤ step := by omega
  have hsize' : u ≤ n/t^(step-1) := by
    apply (le_div_iff₀ (pow_pos ht0 _)).mpr
    calc
      u*t^(step-1) = (t^step*u)/t := by
        conv_rhs => rw [← Nat.sub_add_cancel hstep1, pow_succ]
        field_simp
      _ ≤ (2*n)/t := div_le_div_of_nonneg_right hsize zero_le
      _ ≤ n := (div_le_iff₀ ht0).mpr (by
        simpa only [mul_comm n t] using mul_le_mul_of_nonneg_right ht (zero_le (a := n)))
  exact inversePower_inner_margin t p eta eta0 n u b (step-1) ht1 (by omega) hp heta hcoefficient hsize'

theorem source_reserve_reference_endpoint_from_power
    (t u p eta eta0 epsilon : ℝ≥0) (b L : ℕ)
    (ht : 1 ≤ t) (hp : 1/t^b ≤ p) (heta : eta0 ≤ eta) (hu : t^L ≤ u)
    (hgap : 2*b+1 ≤ L) (hcoefficient : 4 ≤ epsilon*eta0*t) :
    1 ≤ (epsilon/4)*(p^2*eta*u) := by
  have hmass : eta0*t ≤ p^2*eta*u := by
    simpa only [pow_zero, div_one, one_pow, one_mul, pow_one] using
      reserve_internal_supply_power_lower t u 1 p eta eta0 0 b L 1 ht
        (by simp only [pow_zero, div_one, le_refl]) hp heta hu (by omega)
  calc
    (1 : ℝ≥0) = 4/4 := by norm_num
    _ ≤ (epsilon*eta0*t)/4 := div_le_div_of_nonneg_right hcoefficient zero_le
    _ = (epsilon/4)*(eta0*t) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hmass zero_le

theorem source_reserve_reference_tolerance
    (t Z xi epsilon : ℝ≥0) (ht : 0 < t) (hepsilon : 0 < epsilon)
    (hxi : xi ≤ Z/t) (hreference : 4*Z/epsilon ≤ t) (hregularization : 1536*Z ≤ t) :
    xi ≤ epsilon/4 ∧ xi ≤ 1/1536 := by
  constructor
  · apply hxi.trans
    apply (div_le_div_iff₀ ht (by norm_num : (0 : ℝ≥0) < 4)).mpr
    have hh := (div_le_iff₀ hepsilon).mp hreference
    simpa only [mul_comm Z 4, mul_comm t epsilon] using hh
  · apply hxi.trans
    apply (div_le_div_iff₀ ht (by norm_num : (0 : ℝ≥0) < 1536)).mpr
    simpa only [one_mul, mul_comm Z 1536] using hregularization

end Erdos207
