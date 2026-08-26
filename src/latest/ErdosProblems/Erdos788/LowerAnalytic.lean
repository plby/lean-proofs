import ErdosProblems.Erdos788.LowerArithmetic

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-! # Elementary analytic comparisons for the lower bound -/

namespace Erdos788

/-- For `N ≥ 2`, the square-root logarithmic scale is at most `N`. -/
theorem sqrt_mul_log_le_self {N : ℕ} (hN : 2 ≤ N) :
    Real.sqrt ((N : ℝ) * Real.log (N : ℝ)) ≤ (N : ℝ) := by
  let n : ℝ := N
  have hn : 0 < n := by positivity
  have hlogNonneg : 0 ≤ Real.log n := by
    apply Real.log_nonneg
    simpa [n] using!
      (show (1 : ℝ) ≤ (N : ℝ) by exact_mod_cast (show 1 ≤ N by omega))
  have hlog : Real.log n ≤ n := by
    have := Real.log_le_sub_one_of_pos hn
    linarith
  apply Real.sqrt_le_iff.mpr
  constructor
  · positivity
  · have hmul := mul_le_mul_of_nonneg_left hlog hn.le
    nlinarith

/-- If `b⁴ ≤ N`, multiplying the square-root logarithmic scale by `b + 1`
still costs only a constant multiple of `N`. -/
theorem add_one_mul_sqrt_mul_log_le_four {N b : ℕ} (hN : 2 ≤ N)
    (hb4 : b ^ 4 ≤ N) :
    ((b + 1 : ℕ) : ℝ) * Real.sqrt ((N : ℝ) * Real.log (N : ℝ)) ≤
      4 * (N : ℝ) := by
  let n : ℝ := N
  let br : ℝ := b
  let r : ℝ := Real.sqrt n
  let L : ℝ := Real.log n
  let s : ℝ := Real.sqrt (n * L)
  have hn : 0 < n := by positivity
  have hnOne : 1 ≤ n := by
    simpa [n] using!
      (show (1 : ℝ) ≤ (N : ℝ) by exact_mod_cast (show 1 ≤ N by omega))
  have hL : 0 ≤ L := Real.log_nonneg hnOne
  have hr : 0 ≤ r := Real.sqrt_nonneg _
  have hrSq : r ^ 2 = n := by
    exact Real.sq_sqrt hn.le
  have hs : 0 ≤ s := Real.sqrt_nonneg _
  have hsSq : s ^ 2 = n * L := by
    exact Real.sq_sqrt (mul_nonneg hn.le hL)
  have hlog : L ≤ 2 * r := by
    simpa [L, n, r, Real.sqrt_eq_rpow, mul_comm] using!
      (Real.log_natCast_le_rpow_div N (by norm_num : (0 : ℝ) < 1 / 2))
  by_cases hb : b = 0
  · subst b
    have hsmall := sqrt_mul_log_le_self hN
    dsimp [n, br, r, L, s] at *
    norm_num at *
    nlinarith
  · have hbNat : 1 ≤ b := Nat.one_le_iff_ne_zero.mpr hb
    have hbrOne : 1 ≤ br := by
      simpa [br] using! (show (1 : ℝ) ≤ (b : ℝ) by exact_mod_cast hbNat)
    have hb4R : br ^ 4 ≤ n := by
      simpa [br, n] using!
        (show (b : ℝ) ^ 4 ≤ (N : ℝ) by exact_mod_cast hb4)
    have hbrSqSq : (br ^ 2) ^ 2 ≤ r ^ 2 := by
      nlinarith [hb4R, hrSq]
    have hbrSq : br ^ 2 ≤ r := by
      exact (sq_le_sq₀ (sq_nonneg br) hr).mp hbrSqSq
    have hbrLog : br ^ 2 * L ≤ 2 * n := by
      calc
        br ^ 2 * L ≤ r * (2 * r) :=
          mul_le_mul hbrSq hlog hL hr
        _ = 2 * n := by rw [← hrSq]; ring
    have haddSq : (br + 1) ^ 2 ≤ 4 * br ^ 2 := by
      nlinarith
    have hscale : (br + 1) ^ 2 * (n * L) ≤
        (4 * br ^ 2) * (n * L) :=
      mul_le_mul_of_nonneg_right haddSq (mul_nonneg hn.le hL)
    have hbound : (4 * br ^ 2) * (n * L) ≤ 8 * n ^ 2 := by
      have hmul := mul_le_mul_of_nonneg_left hbrLog
        (show 0 ≤ 4 * n by positivity)
      nlinarith
    have hsqBound : ((br + 1) * s) ^ 2 ≤ (4 * n) ^ 2 := by
      calc
        ((br + 1) * s) ^ 2 = (br + 1) ^ 2 * (n * L) := by
          rw [mul_pow, hsSq]
        _ ≤ (4 * br ^ 2) * (n * L) := hscale
        _ ≤ 8 * n ^ 2 := hbound
        _ ≤ (4 * n) ^ 2 := by nlinarith [sq_nonneg n]
    have hmain : (br + 1) * s ≤ 4 * n := by
      exact (sq_le_sq₀ (mul_nonneg (by positivity) hs) (by positivity)).mp hsqBound
    simpa [br, s, n, L] using! hmain

/-- If `N` is below `b⁴` and `d ≥ b`, then `log d` controls `log N`. -/
theorem log_le_four_log_of_lt_fourth_power {N b d : ℕ}
    (hN : 0 < N) (hNb : N < b ^ 4) (hbd : b ≤ d) :
    Real.log (N : ℝ) ≤ 4 * Real.log (d : ℝ) := by
  have hNdNat : N ≤ d ^ 4 :=
    hNb.le.trans (Nat.pow_le_pow_left hbd 4)
  have hNR : (0 : ℝ) < (N : ℝ) := by positivity
  have hNdR : (N : ℝ) ≤ (d : ℝ) ^ 4 := by
    exact_mod_cast hNdNat
  calc
    Real.log (N : ℝ) ≤ Real.log ((d : ℝ) ^ 4) :=
      Real.log_le_log hNR hNdR
    _ = 4 * Real.log (d : ℝ) := by
      rw [Real.log_pow]
      norm_num

end Erdos788
