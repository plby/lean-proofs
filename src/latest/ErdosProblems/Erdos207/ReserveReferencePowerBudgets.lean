/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.FutureTypicalityPowerBudgets

/-! # The reference codegree scale and the stronger residual-spoke loss budget -/

namespace Erdos207

open scoped NNReal

theorem reserve_link_reference_power_lower
    (t u r p eta eta0 : ℝ≥0) (reserveExp b L gain : ℕ)
    (ht : 1 ≤ t) (hr : 1/t^reserveExp ≤ r) (hp : 1/t^b ≤ p)
    (heta : eta0 ≤ eta) (hu : t^L ≤ u) (hgap : reserveExp+3*b+gain ≤ L) :
    eta0^2*t^gain ≤ r*p^3*eta^2*u := by
  have ht0 : 0 < t := zero_lt_one.trans_le ht
  have hpow : t^gain ≤ t^L/t^(reserveExp+3*b) := by
    apply (le_div_iff₀ (pow_pos ht0 _)).mpr
    rw [← pow_add]
    exact pow_le_pow_right₀ ht (by omega)
  calc
    _ ≤ eta0^2*(t^L/t^(reserveExp+3*b)) := mul_le_mul_of_nonneg_left hpow zero_le
    _ = (1/t^reserveExp)*(1/t^b)^3*eta0^2*t^L := by
      simp only [pow_add, pow_mul, div_pow, one_pow]
      field_simp
      ring
    _ ≤ _ := by gcongr

theorem reserve_link_recenter_loss_power
    (t n u loss H K r p eta eta0 : ℝ≥0) (reserveExp b v c decay : ℕ)
    (ht : 1 ≤ t) (hu : 0 < u) (heta0 : 0 < eta0)
    (hr : 1/t^reserveExp ≤ r) (hp : 1/t^b ≤ p) (heta : eta0 ≤ eta)
    (hloss : loss ≤ H*n/t^c) (hsize : n ≤ K*t^v*u)
    (hgap : reserveExp+3*b+v+decay ≤ c) :
    loss/(r*p^3*eta^2*u) ≤ (H*K/eta0^2)/t^decay := by
  have ht0 : 0 < t := zero_lt_one.trans_le ht
  have hp0 : 0 < 1/t^b := by positivity
  have hr0 : 0 < 1/t^reserveExp := by positivity
  have hratio : t^(reserveExp+3*b+v)/t^c ≤ 1/t^decay := by
    apply (div_le_div_iff₀ (pow_pos ht0 _) (pow_pos ht0 _)).mpr
    simpa only [one_mul, ← pow_add] using pow_le_pow_right₀ ht hgap
  calc
    _ ≤ (H*(K*t^v*u)/t^c)/((1/t^reserveExp)*(1/t^b)^3*eta0^2*u) := by
      apply div_le_div_of_nonneg_right
        (hloss.trans (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hsize zero_le) zero_le)) zero_le
        |>.trans ?_
      gcongr
    _ = (H*K/eta0^2)*(t^(reserveExp+3*b+v)/t^c) := by
      simp only [pow_add, pow_mul, div_pow, one_pow]
      field_simp
      ring
    _ ≤ (H*K/eta0^2)*(1/t^decay) := mul_le_mul_of_nonneg_left hratio zero_le
    _ = _ := by ring

end Erdos207
