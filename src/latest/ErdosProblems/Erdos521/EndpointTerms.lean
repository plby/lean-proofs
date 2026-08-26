/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Decay of the individual terms in the logarithmic endpoint estimate.
Formal proof: Codex.
-/
import ErdosProblems.Erdos521.Decay
import ErdosProblems.Erdos521.LocalMaximal

namespace Erdos521

open Filter
open scoped Topology

noncomputable def endpointCutoff (d : ℝ) (n : ℕ) : ℝ := (n : ℝ) ^ (1 / 2 - d)

theorem endpointCutoff_pos (d : ℝ) {n : ℕ} (hn : 0 < n) : 0 < endpointCutoff d n := by
  exact Real.rpow_pos_of_pos (by exact_mod_cast hn) _

theorem endpointCutoff_sq (d : ℝ) (n : ℕ) :
    endpointCutoff d n ^ 2 = (n : ℝ) ^ (1 - 2 * d) := by
  rw [endpointCutoff, ← Real.rpow_mul_natCast (Nat.cast_nonneg n)]
  congr 1
  norm_num
  ring

theorem eventually_endpoint_smallBall_sqrt {a c d : ℝ} (ha : 0 < a) (hc : 0 < c)
    (hd : 0 < d) :
    ∀ᶠ n : ℕ in atTop,
      Real.sqrt (Real.pi / (c * geometricVariance (endpointCenter a n) (n + 1) /
        (2 * endpointCutoff d n) ^ 2)) ≤ (n : ℝ) ^ (-d / 2) := by
  filter_upwards [eventually_geometricVariance_endpoint_lower ha,
    eventually_const_mul_log_le_rpow (16 * a * Real.pi / c) hd, eventually_ge_atTop 2]
    with n hV hlog hn
  have hn₀ : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hlog₀ : 0 < Real.log n := Real.log_pos (by exact_mod_cast (show 1 < n by omega))
  have hden : 0 < c * ((n : ℝ) / (4 * a * Real.log n)) := by positivity
  have hratio : Real.pi / (c * geometricVariance (endpointCenter a n) (n + 1) /
      (2 * endpointCutoff d n) ^ 2) ≤
      (16 * a * Real.pi / c) * Real.log n * (n : ℝ) ^ (-2 * d) := by
    calc
      _ = (Real.pi * (2 * endpointCutoff d n) ^ 2) /
          (c * geometricVariance (endpointCenter a n) (n + 1)) := by rw [div_div_eq_mul_div]
      _ ≤ (Real.pi * (2 * endpointCutoff d n) ^ 2) /
          (c * ((n : ℝ) / (4 * a * Real.log n))) :=
        div_le_div_of_nonneg_left (by positivity) hden (mul_le_mul_of_nonneg_left hV hc.le)
      _ = _ := by
        rw [mul_pow, endpointCutoff_sq, Real.rpow_sub hn₀, Real.rpow_one]
        rw [show -2 * d = -(2 * d) by ring, Real.rpow_neg hn₀.le]
        field_simp
        norm_num
  have hpower : (16 * a * Real.pi / c) * Real.log n * (n : ℝ) ^ (-2 * d) ≤
      (n : ℝ) ^ (-d) := by
    calc
      _ ≤ (n : ℝ) ^ d * (n : ℝ) ^ (-2 * d) :=
        mul_le_mul_of_nonneg_right hlog (Real.rpow_nonneg hn₀.le _)
      _ = _ := by rw [← Real.rpow_add hn₀]; congr 1; ring
  have h := Real.sqrt_le_sqrt (hratio.trans hpower)
  have hsqrt : Real.sqrt ((n : ℝ) ^ (-d)) = (n : ℝ) ^ (-d / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hn₀.le]
    congr 1
    ring
  exact h.trans_eq hsqrt

theorem eventually_endpoint_variance_exp {a c : ℝ} (ha : 0 < a) (hc : 0 < c) (p : ℝ) :
    ∀ᶠ n : ℕ in atTop,
      Real.exp (-c * geometricVariance (endpointCenter a n) (n + 1)) ≤ (n : ℝ) ^ p := by
  filter_upwards [eventually_geometricVariance_endpoint_lower ha,
    eventually_rpow_le_div_log (C := 4 * a) (q := 1 / 2) (by positivity) (by norm_num),
    eventually_exp_neg_rpow_le_rpow hc (by norm_num : (0 : ℝ) < 1 / 2) p]
    with n hV hpow hexp
  apply le_trans _ hexp
  exact Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_left (hpow.trans hV) (neg_nonpos.mpr hc.le))

theorem eventually_endpoint_cutoff_exp {d : ℝ} (hd : d < 1 / 2) (p : ℝ) :
    ∀ᶠ n : ℕ in atTop,
      Real.exp (-(2 * endpointCutoff d n) ^ 2 / 2) ≤ (n : ℝ) ^ p := by
  have h := eventually_exp_neg_rpow_le_rpow (by norm_num : (0 : ℝ) < 2)
    (by linarith : 0 < 1 - 2 * d) p
  filter_upwards [h] with n hn
  convert hn using 1
  congr 1
  rw [mul_pow, endpointCutoff_sq]
  ring

theorem endpoint_tail_term_le {a d : ℝ} (ha : 0 ≤ a) {n : ℕ} (hn : 1 ≤ n)
    (hx₀ : 0 ≤ endpointCenter a n) (hx₁ : endpointCenter a n ≤ 1) :
    endpointCenter a n ^ (2 * (n + 1)) * geometricVariance (endpointCenter a n) n /
      endpointCutoff d n ^ 2 ≤ (n : ℝ) ^ (-2 * a + 2 * d) := by
  have hn₀ : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  calc
    _ ≤ (n : ℝ) ^ (-2 * a) * n / endpointCutoff d n ^ 2 := by
      apply div_le_div_of_nonneg_right _ (sq_nonneg _)
      exact mul_le_mul (endpointCenter_tail_le ha hn hx₀)
        (geometricVariance_le_count hx₀ hx₁ n) (geometricVariance_nonneg _ _) (by positivity)
    _ = _ := by
      rw [endpointCutoff_sq]
      calc
        (n : ℝ) ^ (-2 * a) * n / (n : ℝ) ^ (1 - 2 * d) =
            (n : ℝ) ^ (-2 * a) * (n : ℝ) ^ (1 : ℝ) / (n : ℝ) ^ (1 - 2 * d) := by
          rw [Real.rpow_one]
        _ = _ := by
          rw [← Real.rpow_add hn₀, ← Real.rpow_sub hn₀]
          congr 1
          ring

theorem endpoint_boundary_term_le (a b d τ : ℝ) {n : ℕ} (hn : 1 ≤ n)
    (hy : 0 ≤ endpointCenter a n + 4 * endpointRadius b n) :
    2 * (geometricVariance (endpointCenter a n + 4 * endpointRadius b n) (2 * n + 1) *
      (1 + Real.log (2 * n + 1))) /
      (endpointCutoff d n ^ 2 * (4 : ℝ) ^ endpointThreshold τ n) ≤
      6 * (1 + Real.log (2 * n + 1)) *
        (n : ℝ) ^ (4 * max (4 * b - a) 0 + 2 * d - τ * Real.log 4) := by
  have hnNat : 0 < n := by omega
  have hn₀ : (0 : ℝ) < n := by exact_mod_cast hnNat
  have hcut := endpointCutoff_pos d hnNat
  have hlog : 0 ≤ 1 + Real.log (2 * (n : ℝ) + 1) := by
    have h := Real.log_nonneg (show (1 : ℝ) ≤ 2 * n + 1 by have := Nat.cast_nonneg (α := ℝ) n; linarith)
    linarith
  have hV := geometricVariance_endpoint_upper hn hy
  have hpow := endpointThreshold_pow_lower τ hnNat
  have hid : (n : ℝ) * (n : ℝ) ^ (4 * max (4 * b - a) 0) /
      ((n : ℝ) ^ (1 - 2 * d) * (n : ℝ) ^ (τ * Real.log 4)) =
      (n : ℝ) ^ (4 * max (4 * b - a) 0 + 2 * d - τ * Real.log 4) := by
    calc
      _ = ((n : ℝ) ^ (1 : ℝ) * (n : ℝ) ^ (4 * max (4 * b - a) 0)) /
          ((n : ℝ) ^ (1 - 2 * d) * (n : ℝ) ^ (τ * Real.log 4)) := by rw [Real.rpow_one]
      _ = _ := by
        rw [← Real.rpow_add hn₀, ← Real.rpow_add hn₀, ← Real.rpow_sub hn₀]
        congr 1
        ring
  calc
    _ ≤ 2 * ((3 * n * (n : ℝ) ^ (4 * max (4 * b - a) 0)) *
        (1 + Real.log (2 * n + 1))) /
        (endpointCutoff d n ^ 2 * (4 : ℝ) ^ endpointThreshold τ n) := by
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hV hlog) (by norm_num))
        (by positivity)
    _ ≤ 2 * ((3 * n * (n : ℝ) ^ (4 * max (4 * b - a) 0)) *
        (1 + Real.log (2 * n + 1))) /
        (endpointCutoff d n ^ 2 * (n : ℝ) ^ (τ * Real.log 4)) := by
      exact div_le_div_of_nonneg_left (by positivity) (by positivity)
        (mul_le_mul_of_nonneg_left hpow (sq_nonneg _))
    _ = 6 * (1 + Real.log (2 * n + 1)) *
        ((n : ℝ) * (n : ℝ) ^ (4 * max (4 * b - a) 0) /
          ((n : ℝ) ^ (1 - 2 * d) * (n : ℝ) ^ (τ * Real.log 4))) := by
      rw [endpointCutoff_sq]
      ring
    _ = _ := by rw [hid]

theorem eventually_endpoint_boundary_term {a b d τ p : ℝ} (ha : 0 < a) (hb : 0 ≤ b)
    (hgap : 4 * max (4 * b - a) 0 + 2 * d + p < τ * Real.log 4) :
    ∀ᶠ n : ℕ in atTop,
      2 * (geometricVariance (endpointCenter a n + 4 * endpointRadius b n) (2 * n + 1) *
        (1 + Real.log (2 * n + 1))) /
        (endpointCutoff d n ^ 2 * (4 : ℝ) ^ endpointThreshold τ n) ≤ 6 * (n : ℝ) ^ (-p) := by
  let e := 4 * max (4 * b - a) 0 + 2 * d - τ * Real.log 4
  have hq : 0 < -p - e := by dsimp [e]; linarith
  filter_upwards [eventually_endpointCenter_bounds ha, eventually_ge_atTop 2,
    eventually_const_mul_one_add_log_le_rpow (C := 1) zero_le_one hq] with n hx hn hlog
  have hn₀ : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hr : 0 ≤ endpointRadius b n := by
    have hlog₀ : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast (show 1 ≤ n by omega))
    exact div_nonneg (mul_nonneg hb hlog₀) hn₀.le
  have h := endpoint_boundary_term_le a b d τ (by omega : 1 ≤ n) (by linarith [hx.1])
  apply h.trans
  change 6 * (1 + Real.log (2 * n + 1)) * (n : ℝ) ^ e ≤ _
  have hmul := mul_le_mul_of_nonneg_right (show 1 + Real.log (2 * n + 1) ≤ (n : ℝ) ^ (-p - e) by
    simpa only [one_mul] using hlog) (Real.rpow_nonneg hn₀.le e)
  have hprod : (n : ℝ) ^ (-p - e) * (n : ℝ) ^ e = (n : ℝ) ^ (-p) := by
    rw [← Real.rpow_add hn₀, sub_add_cancel]
  rw [hprod] at hmul
  nlinarith

end Erdos521
