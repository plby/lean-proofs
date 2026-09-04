import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Real.Pi.Bounds

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Explicit factorial-tail estimates for the Brun truncation
-/

open Nat Finset

namespace Erdos394

/-- If the base is at most one eighth of the exponent, its factorial quotient
is at most `2⁻ⁿ`. -/
theorem pow_div_factorial_le_one_half_pow {Λ : ℝ} {n : ℕ}
    (hΛ0 : 0 ≤ Λ) (hn : 0 < n) (hΛn : Λ ≤ (n : ℝ) / 8) :
    Λ ^ n / (n.factorial : ℝ) ≤ ((1 : ℝ) / 2) ^ n := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hepos : 0 < Real.exp 1 := Real.exp_pos 1
  have hbase : Λ ≤ (n : ℝ) / (2 * Real.exp 1) := by
    apply hΛn.trans
    rw [div_le_div_iff₀ (by norm_num : (0 : ℝ) < 8)
      (mul_pos (by norm_num) hepos)]
    nlinarith [Real.exp_one_lt_three]
  have hpow : Λ ^ n ≤ ((n : ℝ) / (2 * Real.exp 1)) ^ n :=
    pow_le_pow_left₀ hΛ0 hbase n
  have hsqrt : 1 ≤ Real.sqrt (2 * Real.pi * (n : ℝ)) := by
    rw [Real.one_le_sqrt]
    have htwo : (1 : ℝ) ≤ 2 * Real.pi := by
      linarith [Real.pi_gt_three]
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
    calc
      (1 : ℝ) = 1 * 1 := by ring
      _ ≤ (2 * Real.pi) * (n : ℝ) :=
        mul_le_mul htwo hn1 (by norm_num) (by positivity)
      _ = 2 * Real.pi * (n : ℝ) := by ring
  have hcore0 : 0 ≤ ((n : ℝ) / Real.exp 1) ^ n := by positivity
  have hfac : ((n : ℝ) / Real.exp 1) ^ n ≤ (n.factorial : ℝ) := by
    calc
      ((n : ℝ) / Real.exp 1) ^ n =
          1 * ((n : ℝ) / Real.exp 1) ^ n := by ring
      _ ≤ Real.sqrt (2 * Real.pi * (n : ℝ)) *
          ((n : ℝ) / Real.exp 1) ^ n :=
        mul_le_mul_of_nonneg_right hsqrt hcore0
      _ ≤ (n.factorial : ℝ) := Stirling.le_factorial_stirling n
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < n.factorial)).2
  calc
    Λ ^ n ≤ ((n : ℝ) / (2 * Real.exp 1)) ^ n := hpow
    _ = ((1 : ℝ) / 2) ^ n * ((n : ℝ) / Real.exp 1) ^ n := by
      rw [← mul_pow]
      congr 1
      field_simp
      <;> ring
    _ ≤ ((1 : ℝ) / 2) ^ n * (n.factorial : ℝ) :=
      mul_le_mul_of_nonneg_left hfac (by positivity)

/-- A sufficiently long power of one half is below the exponential density
scale needed later. -/
theorem one_half_pow_le_exp_neg_twentyfour {L : ℝ} {n : ℕ}
    (hLn : 48 * L ≤ (n : ℝ)) :
    ((1 : ℝ) / 2) ^ n ≤ Real.exp (-24 * L) := by
  have hlog2 : (1 : ℝ) / 2 ≤ Real.log 2 :=
    (by norm_num : (1 : ℝ) / 2 < 0.6931471803).le.trans
      Real.log_two_gt_d9.le
  have hn0 : (0 : ℝ) ≤ n := by positivity
  have hexp : -(n : ℝ) * Real.log 2 ≤ -24 * L := by
    have hhalf : 24 * L ≤ (n : ℝ) / 2 := by linarith
    have hmul : (n : ℝ) / 2 ≤ (n : ℝ) * Real.log 2 := by
      nlinarith
    linarith
  calc
    ((1 : ℝ) / 2) ^ n = Real.exp (-(n : ℝ) * Real.log 2) := by
      calc
        ((1 : ℝ) / 2) ^ n = (Real.exp (-Real.log 2)) ^ n := by
          rw [Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
          norm_num [one_div]
        _ = Real.exp ((n : ℝ) * (-Real.log 2)) :=
          (Real.exp_nat_mul (-Real.log 2) n).symm
        _ = Real.exp (-(n : ℝ) * Real.log 2) := by ring_nf
    _ ≤ Real.exp (-24 * L) := Real.exp_le_exp.mpr hexp

/-- Combined explicit factorial-tail estimate. -/
theorem pow_div_factorial_le_exp_neg_twentyfour
    {Λ L : ℝ} {n : ℕ} (hΛ0 : 0 ≤ Λ) (hn : 0 < n)
    (hΛn : Λ ≤ (n : ℝ) / 8) (hLn : 48 * L ≤ (n : ℝ)) :
    Λ ^ n / (n.factorial : ℝ) ≤ Real.exp (-24 * L) :=
  (pow_div_factorial_le_one_half_pow hΛ0 hn hΛn).trans
    (one_half_pow_le_exp_neg_twentyfour hLn)

/-- Even truncation order chosen from a geometric endpoint exponent. -/
noncomputable def geometricBrunOrder (J : ℕ) : ℕ :=
  2 * ⌈100 * (1 + Real.log J)⌉₊

/-- The geometric Brun order is even. -/
theorem geometricBrunOrder_even (J : ℕ) : Even (geometricBrunOrder J) := by
  refine ⟨⌈100 * (1 + Real.log J)⌉₊, ?_⟩
  simp [geometricBrunOrder, two_mul]

/-- The chosen order dominates two hundred times the logarithmic scale. -/
theorem two_hundred_mul_log_le_geometricBrunOrder {J : ℕ} (hJ : 1 ≤ J) :
    200 * (1 + Real.log J) ≤ (geometricBrunOrder J : ℝ) := by
  have hceil := Nat.le_ceil (100 * (1 + Real.log J))
  unfold geometricBrunOrder
  push_cast
  nlinarith

/-- Under the weak reciprocal-mass upper bound, the chosen factorial tail is
below the weak local Euler-product lower bound. -/
theorem geometricBrun_tail_le_of_bounds {J : ℕ} (hJ : 1 ≤ J)
    {Λ V : ℝ} (hΛ0 : 0 ≤ Λ)
    (hΛ : Λ ≤ 12 * (1 + Real.log J))
    (hV : Real.exp (-24 * (1 + Real.log J)) ≤ V) :
    Λ ^ (geometricBrunOrder J + 1) /
        ((geometricBrunOrder J + 1).factorial : ℝ) ≤ V := by
  let L : ℝ := 1 + Real.log J
  let n : ℕ := geometricBrunOrder J + 1
  have hL0 : 0 ≤ L := by
    dsimp [L]
    have hlog : 0 ≤ Real.log J := Real.log_nonneg (by exact_mod_cast hJ)
    linarith
  have hn : 0 < n := by simp [n]
  have hR := two_hundred_mul_log_le_geometricBrunOrder hJ
  have hnL : 200 * L ≤ (n : ℝ) := by
    dsimp [L, n]
    push_cast
    linarith
  have hΛn : Λ ≤ (n : ℝ) / 8 := by
    change Λ ≤ 12 * L at hΛ
    nlinarith
  have hLn : 48 * L ≤ (n : ℝ) := by nlinarith
  apply (pow_div_factorial_le_exp_neg_twentyfour hΛ0 hn hΛn hLn).trans
  simpa [L] using hV

end Erdos394
