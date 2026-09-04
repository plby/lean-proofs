import Mathlib
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Erdős 586: the explicit analytic tail

This file contains the elementary continuation argument used after the
finite certificate at the ten-thousandth prime.  Prime indices in this file
are one-based: `primeAt 1 = 2`.
-/

namespace Erdos586.Tail

open scoped Nat.Prime Topology
open Filter Finset MeasureTheory

/-- The one-indexed prime sequence.  The value at zero is irrelevant. -/
noncomputable def primeAt (r : ℕ) : ℕ :=
  Nat.nth Nat.Prime (r - 1)

/-- The numerator factor in the fixed-`1/5` recurrence. -/
noncomputable def numeratorFactor (q : ℝ) : ℝ :=
  1 + 15 / (4 * q) + 5 / (2 * q ^ 2)

/-- The denominator coefficient in the fixed-`1/5` recurrence. -/
noncomputable def denominatorCoeff (q : ℝ) : ℝ :=
  25 / (16 * q ^ 2)

/-- `p_r - 1`, viewed as a real number. -/
noncomputable def qAt (r : ℕ) : ℝ :=
  (primeAt r : ℝ) - 1

noncomputable def tailN (r : ℕ) : ℝ := numeratorFactor (qAt r)

noncomputable def tailC (r : ℕ) : ℝ := denominatorCoeff (qAt r)

/-- The polynomial antiderivative for `log(x)^9 / x^2`. -/
def P9 (u : ℝ) : ℝ :=
  u ^ 9 + 9 * u ^ 8 + 72 * u ^ 7 + 504 * u ^ 6 + 3024 * u ^ 5 +
    15120 * u ^ 4 + 60480 * u ^ 3 + 181440 * u ^ 2 +
    362880 * u + 362880

def P9Deriv (u : ℝ) : ℝ :=
  9 * u ^ 8 + 72 * u ^ 7 + 504 * u ^ 6 + 3024 * u ^ 5 +
    15120 * u ^ 4 + 60480 * u ^ 3 + 181440 * u ^ 2 +
    362880 * u + 362880

noncomputable def logPowerTail (x : ℝ) : ℝ := Real.log x ^ 9 / x ^ 2

noncomputable def P9Quotient (x : ℝ) : ℝ := P9 (Real.log x) / x

lemma hasDerivAt_P9 (u : ℝ) : HasDerivAt P9 (P9Deriv u) u := by
  have h0 := (hasDerivAt_id u).pow 9
  have h1 := h0.add (((hasDerivAt_id u).pow 8).const_mul (9 : ℝ))
  have h2 := h1.add (((hasDerivAt_id u).pow 7).const_mul (72 : ℝ))
  have h3 := h2.add (((hasDerivAt_id u).pow 6).const_mul (504 : ℝ))
  have h4 := h3.add (((hasDerivAt_id u).pow 5).const_mul (3024 : ℝ))
  have h5 := h4.add (((hasDerivAt_id u).pow 4).const_mul (15120 : ℝ))
  have h6 := h5.add (((hasDerivAt_id u).pow 3).const_mul (60480 : ℝ))
  have h7 := h6.add (((hasDerivAt_id u).pow 2).const_mul (181440 : ℝ))
  have h8 := h7.add ((hasDerivAt_id u).const_mul (362880 : ℝ))
  have h9 := h8.add_const (362880 : ℝ)
  apply (h9.congr_deriv ?_).congr_of_eventuallyEq
  · exact Filter.Eventually.of_forall (fun y => rfl)
  · change _ = P9Deriv u
    unfold P9Deriv
    norm_num [id_eq]
    ring

lemma hasDerivAt_P9Quotient {x : ℝ} (hx : x ≠ 0) :
    HasDerivAt P9Quotient (-logPowerTail x) x := by
  have hcomp := (hasDerivAt_P9 (Real.log x)).comp x (Real.hasDerivAt_log hx)
  have hquot := hcomp.div (hasDerivAt_id x) hx
  apply (hquot.congr_deriv ?_).congr_of_eventuallyEq
  · exact Filter.Eventually.of_forall (fun y => rfl)
  · unfold logPowerTail
    dsimp only [Function.comp_apply, id_eq]
    rw [inv_eq_one_div]
    unfold P9Deriv P9
    field_simp [hx]
    ring

lemma P9_nonneg {u : ℝ} (hu : 0 ≤ u) : 0 ≤ P9 u := by
  unfold P9
  positivity

lemma hasDerivAt_logPowerTail {x : ℝ} (hx : x ≠ 0) :
    HasDerivAt logPowerTail
      (Real.log x ^ 8 * (9 - 2 * Real.log x) / x ^ 3) x := by
  have hnum := (Real.hasDerivAt_log hx).pow 9
  have hden := (hasDerivAt_id x).pow 2
  have hquot := hnum.div hden (pow_ne_zero 2 hx)
  apply (hquot.congr_deriv ?_).congr_of_eventuallyEq
  · exact Filter.Eventually.of_forall (fun y => rfl)
  · dsimp only [Function.comp_apply, id_eq, Pi.pow_apply]
    norm_num
    rw [inv_eq_one_div]
    field_simp [hx]

lemma logPowerTail_antitone :
    AntitoneOn logPowerTail (Set.Ici (10000 : ℝ)) := by
  apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ici (10000 : ℝ))
  · intro x hx
    simp only [Set.mem_Ici] at hx
    exact (hasDerivAt_logPowerTail (by linarith)).continuousAt.continuousWithinAt
  · rw [interior_Ici]
    intro x hx
    simp only [Set.mem_Ioi] at hx
    exact (hasDerivAt_logPowerTail (by linarith)).hasDerivWithinAt
  · rw [interior_Ici]
    intro x hx
    simp only [Set.mem_Ioi] at hx
    have hloglower : (9 / 2 : ℝ) < Real.log 10000 := by
      rw [show (10000 : ℝ) = 10 ^ 4 by norm_num, Real.log_pow,
        Real.log_ten_eq]
      nlinarith [Real.log_two_gt_d9, Real.log_five_gt_d9]
    have hlogmono : Real.log (10000 : ℝ) ≤ Real.log x := by
      exact Real.strictMonoOn_log.monotoneOn (Set.mem_Ioi.mpr (by norm_num))
        (Set.mem_Ioi.mpr (by linarith)) hx.le
    have hxpos : 0 < x := by linarith
    change Real.log x ^ 8 * (9 - 2 * Real.log x) / x ^ 3 ≤ 0
    exact div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos
      (by positivity) (by nlinarith)) (by positivity)

lemma invMulLog_antitone :
    AntitoneOn (fun x : ℝ => x⁻¹ / Real.log x) (Set.Ici (10000 : ℝ)) := by
  intro x hx y hy hxy
  simp only [Set.mem_Ici] at hx hy
  have hxpos : 0 < x := by linarith
  have hypos : 0 < y := by linarith
  have hlogx : 0 < Real.log x := Real.log_pos (by linarith)
  have hlogy : 0 < Real.log y := Real.log_pos (by linarith)
  have hinv : y⁻¹ ≤ x⁻¹ := by
    simpa [one_div] using one_div_le_one_div_of_le hxpos hxy
  have hlogmono : Real.log x ≤ Real.log y :=
    Real.strictMonoOn_log.monotoneOn hxpos hypos hxy
  have hloginv : (Real.log y)⁻¹ ≤ (Real.log x)⁻¹ := by
    simpa [one_div] using one_div_le_one_div_of_le hlogx hlogmono
  exact mul_le_mul hinv hloginv (by positivity) (by positivity)

theorem integral_logPowerTail {a b : ℝ} (ha : 1 < a) (hb : 1 < b) :
    (∫ x in a..b, logPowerTail x) = P9Quotient a - P9Quotient b := by
  have hderiv : ∀ x ∈ Set.uIcc a b,
      HasDerivAt (-P9Quotient) (logPowerTail x) x := by
    intro x hx
    have hxone : 1 < x := by grind [Set.mem_uIcc]
    simpa using (hasDerivAt_P9Quotient (by linarith : x ≠ 0)).neg
  have hint : IntervalIntegrable logPowerTail volume a b := by
    apply ContinuousOn.intervalIntegrable
    intro x hx
    have hxone : 1 < x := by grind [Set.mem_uIcc]
    exact (hasDerivAt_logPowerTail (by linarith)).continuousAt.continuousWithinAt
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
  change -P9Quotient b - -P9Quotient a = _
  ring

theorem logPowerTail_sum_le_P9 {n : ℕ} :
    (∑ j ∈ Finset.range n,
        logPowerTail ((10000 + j + 1 : ℕ) : ℝ)) ≤
      P9 (Real.log 10000) / 10000 := by
  have hanti : AntitoneOn logPowerTail
      (Set.Icc (10000 : ℝ) (10000 + n : ℝ)) :=
    logPowerTail_antitone.mono (by intro x hx; exact hx.1)
  have hsum := hanti.sum_le_integral
  have hInt : (∫ x in (10000 : ℝ)..(10000 + (n : ℝ)), logPowerTail x) =
      P9Quotient 10000 - P9Quotient (10000 + (n : ℝ)) := by
    apply integral_logPowerTail
    · norm_num
    · have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      linarith
  have hend : 0 ≤ P9Quotient (10000 + (n : ℝ)) := by
    dsimp [P9Quotient]
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have hbase : (1 : ℝ) ≤ 10000 + n := by linarith
    exact div_nonneg (P9_nonneg (Real.log_nonneg hbase)) (by linarith)
  rw [hInt] at hsum
  have hsum' : (∑ j ∈ Finset.range n,
        logPowerTail ((10000 + j + 1 : ℕ) : ℝ)) ≤
      P9Quotient 10000 - P9Quotient (10000 + (n : ℝ)) := by
    convert hsum using 1 <;> push_cast <;> ring_nf
  calc
    (∑ j ∈ Finset.range n,
        logPowerTail ((10000 + j + 1 : ℕ) : ℝ)) ≤
        P9Quotient 10000 - P9Quotient (10000 + (n : ℝ)) := hsum'
    _ ≤ P9Quotient 10000 := by linarith
    _ = P9 (Real.log 10000) / 10000 := rfl

theorem invMulLog_sum_le {n : ℕ} :
    (∑ j ∈ Finset.range n,
        (((10000 + j + 1 : ℕ) : ℝ)⁻¹ /
          Real.log (10000 + j + 1 : ℕ))) ≤
      Real.log (Real.log (10000 + n : ℕ)) - Real.log (Real.log 10000) := by
  have hanti : AntitoneOn (fun x : ℝ => x⁻¹ / Real.log x)
      (Set.Icc (10000 : ℝ) (10000 + n : ℝ)) :=
    invMulLog_antitone.mono (by intro x hx; exact hx.1)
  have hsum := hanti.sum_le_integral
  have hInt := integral_inv_div_log
    (a := (10000 : ℝ)) (b := (10000 + (n : ℝ))) (by norm_num)
      (by have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n; linarith)
  rw [hInt] at hsum
  convert hsum using 1 <;> push_cast <;> ring_nf

lemma primeAt_prime (r : ℕ) : Nat.Prime (primeAt r) := by
  exact Nat.prime_nth_prime _

lemma primeAt_pos (r : ℕ) : 0 < primeAt r :=
  (primeAt_prime r).pos

lemma primeAt_add_one_le (r : ℕ) (hr : 1 ≤ r) : r + 1 ≤ primeAt r := by
  rw [primeAt]
  have h := Nat.add_two_le_nth_prime (r - 1)
  omega

lemma primeCounting_primeAt (r : ℕ) (hr : 1 ≤ r) :
    Nat.primeCounting (primeAt r) = r := by
  rw [Nat.primeCounting, Nat.primeCounting', Nat.count_succ]
  rw [if_pos (primeAt_prime r)]
  have hcount : Nat.count Nat.Prime (primeAt r) = r - 1 := by
    simpa [Nat.primeCounting', primeAt] using Nat.primeCounting'_nth_eq (r - 1)
  omega

lemma log_four_lt_seven_fifths : Real.log 4 < (7 / 5 : ℝ) := by
  rw [Real.log_four_eq]
  nlinarith [Real.log_two_lt_d9]

lemma log_ten_thousand_lt_ten : Real.log 10000 < (10 : ℝ) := by
  rw [show (10000 : ℝ) = 10 ^ 4 by norm_num, Real.log_pow, Real.log_ten_eq]
  norm_num
  nlinarith [Real.log_two_lt_d9, Real.log_five_lt_d9]

lemma nine_twenty_one_hundredths_lt_log_ten_thousand :
    (921 / 100 : ℝ) < Real.log 10000 := by
  rw [show (10000 : ℝ) = 10 ^ 4 by norm_num, Real.log_pow, Real.log_ten_eq]
  nlinarith [Real.log_two_gt_d9, Real.log_five_gt_d9]

lemma log_ten_thousand_lt_four_sixty_one_fiftieths :
    Real.log 10000 < (461 / 50 : ℝ) := by
  rw [show (10000 : ℝ) = 10 ^ 4 by norm_num, Real.log_pow, Real.log_ten_eq]
  nlinarith [Real.log_two_lt_d9, Real.log_five_lt_d9]

lemma log_div_self_le_one_thousandth {r : ℕ} (hr : 10000 ≤ r) :
    Real.log (r : ℝ) / r ≤ (1 / 1000 : ℝ) := by
  have he : Real.exp 1 ≤ (10000 : ℝ) := by
    linarith [Real.exp_one_lt_three]
  have her : Real.exp 1 ≤ (r : ℝ) := by
    exact he.trans (by exact_mod_cast hr)
  have hmono := Real.log_div_self_antitoneOn he her (by exact_mod_cast hr)
  calc
    Real.log (r : ℝ) / r ≤ Real.log (10000 : ℝ) / 10000 := hmono
    _ ≤ 1 / 1000 := by
      have := log_ten_thousand_lt_ten
      norm_num at this ⊢
      linarith

/-- A fully explicit lower bound for the one-indexed `r`-th prime, obtained
from Mathlib's explicit Chebyshev estimate. -/
theorem primeAt_lower_bound {r : ℕ} (hr : 10000 ≤ r) :
    (7 / 20 : ℝ) * r * Real.log r ≤ primeAt r := by
  have hr1 : 1 ≤ r := by omega
  have hrpos : (0 : ℝ) < r := by positivity
  have hrone : (1 : ℝ) < r := by exact_mod_cast (lt_of_lt_of_le (by norm_num) hr)
  have hlogr : 0 < Real.log (r : ℝ) := Real.log_pos hrone
  have hpNat : r + 1 ≤ primeAt r := primeAt_add_one_le r hr1
  have hpone : (1 : ℝ) < primeAt r := by exact_mod_cast (lt_of_lt_of_le (by omega) hpNat)
  have hppos : (0 : ℝ) < primeAt r := by exact_mod_cast primeAt_pos r
  by_contra! hp
  have hlogmono : Real.log (r : ℝ) ≤ Real.log (primeAt r : ℝ) := by
    exact Real.strictMonoOn_log.monotoneOn (Set.mem_Ioi.mpr hrpos)
      (Set.mem_Ioi.mpr hppos)
      (by exact_mod_cast (le_trans (Nat.le_add_right r 1) hpNat))
  have hlogp : 0 < Real.log (primeAt r : ℝ) := Real.log_pos hpone
  have hcheb := Chebyshev.pi_le_log4_mul_div (x := (primeAt r : ℝ)) hpone
  have hcount : (Nat.primeCounting (primeAt r) : ℝ) = r := by
    norm_num [primeCounting_primeAt r hr1]
  have hsqrtlog : Real.log (Real.sqrt (primeAt r : ℝ)) =
      Real.log (primeAt r : ℝ) / 2 := by
    rw [Real.log_sqrt (le_of_lt hppos)]
  have hfirst :
      Real.log 4 * (primeAt r : ℝ) /
          Real.log (Real.sqrt (primeAt r : ℝ)) < (49 / 50 : ℝ) * r := by
    rw [hsqrtlog, div_lt_iff₀ (by positivity)]
    have hmul : Real.log 4 * (primeAt r : ℝ) <
        (49 / 100 : ℝ) * r * Real.log (r : ℝ) := by
      calc
        Real.log 4 * (primeAt r : ℝ) <
            (7 / 5 : ℝ) * (primeAt r : ℝ) := by
          exact mul_lt_mul_of_pos_right log_four_lt_seven_fifths hppos
        _ ≤ (7 / 5 : ℝ) * ((7 / 20 : ℝ) * r * Real.log r) := by
          exact mul_le_mul_of_nonneg_left hp.le (by norm_num)
        _ = (49 / 100 : ℝ) * r * Real.log r := by ring
    nlinarith
  have hrsq : (r : ℝ) * Real.log r ≤ r ^ 2 / 1000 := by
    have hratio := log_div_self_le_one_thousandth hr
    rw [div_le_iff₀ hrpos] at hratio
    nlinarith
  have hpsq : (primeAt r : ℝ) < (r / 50 : ℝ) ^ 2 := by
    calc
      (primeAt r : ℝ) < (7 / 20 : ℝ) * r * Real.log r := hp
      _ ≤ (7 / 20000 : ℝ) * r ^ 2 := by nlinarith
      _ < (r / 50 : ℝ) ^ 2 := by nlinarith
  have hsqrt : Real.sqrt (primeAt r : ℝ) < (r : ℝ) / 50 := by
    rw [Real.sqrt_lt' (by positivity)]
    exact hpsq
  have hcheb' : (r : ℝ) ≤
      Real.log 4 * (primeAt r : ℝ) /
          Real.log (Real.sqrt (primeAt r : ℝ)) +
        Real.sqrt (primeAt r : ℝ) := by
    simpa [Nat.floor_natCast, hcount] using hcheb
  linarith

theorem primeAt_sub_one_lower_bound {r : ℕ} (hr : 10000 ≤ r) :
    (349 / 1000 : ℝ) * r * Real.log r ≤ (primeAt r : ℝ) - 1 := by
  have hmain := primeAt_lower_bound hr
  have hloglower := nine_twenty_one_hundredths_lt_log_ten_thousand
  have hlogmono : Real.log (10000 : ℝ) ≤ Real.log (r : ℝ) := by
    exact Real.strictMonoOn_log.monotoneOn (Set.mem_Ioi.mpr (by norm_num))
      (Set.mem_Ioi.mpr (by positivity))
      (by exact_mod_cast hr)
  have hrpos : (0 : ℝ) < r := by positivity
  have hrge : (10000 : ℝ) ≤ r := by exact_mod_cast hr
  have hprod : 0 ≤ ((r : ℝ) - 10000) * (Real.log r - 921 / 100) :=
    mul_nonneg (by linarith) (by linarith)
  nlinarith

lemma tail_scale_pos {r : ℕ} (hr : 10000 ≤ r) :
    0 < (r : ℝ) * Real.log r := by
  have : (1 : ℝ) < r := by exact_mod_cast (lt_of_lt_of_le (by norm_num) hr)
  exact mul_pos (by positivity) (Real.log_pos this)

lemma tail_scale_ge_ninety {r : ℕ} (hr : 10000 ≤ r) :
    (90 : ℝ) ≤ (r : ℝ) * Real.log r := by
  have hloglower := nine_twenty_one_hundredths_lt_log_ten_thousand
  have hlogmono : Real.log (10000 : ℝ) ≤ Real.log (r : ℝ) := by
    exact Real.strictMonoOn_log.monotoneOn (Set.mem_Ioi.mpr (by norm_num))
      (Set.mem_Ioi.mpr (by positivity))
      (by exact_mod_cast hr)
  have hcast : (10000 : ℝ) ≤ r := by exact_mod_cast hr
  have hprod : 0 ≤ ((r : ℝ) - 10000) * (Real.log r - 921 / 100) :=
    mul_nonneg (by linarith) (by linarith)
  nlinarith

lemma qAt_ge_third_scale {r : ℕ} (hr : 10000 ≤ r) :
    (r : ℝ) * Real.log r / 3 < qAt r := by
  have h := primeAt_sub_one_lower_bound hr
  dsimp [qAt]
  have hs := tail_scale_pos hr
  nlinarith

lemma qAt_pos {r : ℕ} (hr : 10000 ≤ r) : 0 < qAt r := by
  have h := qAt_ge_third_scale hr
  have hs := tail_scale_pos hr
  nlinarith

lemma tailN_nonneg {r : ℕ} (hr : 10000 ≤ r) : 0 ≤ tailN r := by
  dsimp [tailN, numeratorFactor]
  have := qAt_pos hr
  positivity

lemma tailC_nonneg {r : ℕ} (hr : 10000 ≤ r) : 0 ≤ tailC r := by
  dsimp [tailC, denominatorCoeff]
  have := qAt_pos hr
  positivity

theorem tailN_le_exp {r : ℕ} (hr : 10000 ≤ r) :
    tailN r ≤ Real.exp (11 / ((r : ℝ) * Real.log r)) := by
  let t : ℝ := (r : ℝ) * Real.log r
  have ht : 0 < t := tail_scale_pos hr
  have ht90 : 90 ≤ t := by simpa [t] using tail_scale_ge_ninety hr
  have hq : t / 3 < qAt r := by simpa [t] using qAt_ge_third_scale hr
  have hqpos : 0 < qAt r := qAt_pos hr
  have hfirst : 15 / (4 * qAt r) ≤ 43 / (4 * t) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have hsharp := primeAt_sub_one_lower_bound hr
    change (349 / 1000 : ℝ) * r * Real.log r ≤ qAt r at hsharp
    have htdef : (r : ℝ) * Real.log r = t := rfl
    nlinarith
  have hsecond : 5 / (2 * qAt r ^ 2) ≤ 1 / (4 * t) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have hqsq : t ^ 2 / 9 < qAt r ^ 2 := by nlinarith
    nlinarith
  have hlinear : tailN r ≤ 1 + 11 / t := by
    dsimp [tailN, numeratorFactor]
    calc
      1 + 15 / (4 * qAt r) + 5 / (2 * qAt r ^ 2)
          ≤ 1 + 43 / (4 * t) + 1 / (4 * t) := by gcongr
      _ = 1 + 11 / t := by ring
  calc
    tailN r ≤ 1 + 11 / t := hlinear
    _ ≤ Real.exp (11 / t) := by
      simpa [add_comm] using Real.add_one_le_exp (11 / t)
    _ = Real.exp (11 / ((r : ℝ) * Real.log r)) := by rfl

theorem tailC_le {r : ℕ} (hr : 10000 ≤ r) :
    tailC r ≤ 13 / ((r : ℝ) ^ 2 * Real.log r ^ 2) := by
  have ht : 0 < (r : ℝ) * Real.log r := tail_scale_pos hr
  have hq := primeAt_sub_one_lower_bound hr
  have hqpos := qAt_pos hr
  have hlog : 0 < Real.log (r : ℝ) := by
    have : (1 : ℝ) < r := by exact_mod_cast (lt_of_lt_of_le (by norm_num) hr)
    exact Real.log_pos this
  dsimp [tailC, denominatorCoeff, qAt]
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have hsq : ((349 / 1000 : ℝ) * r * Real.log r) ^ 2 ≤
      ((primeAt r : ℝ) - 1) ^ 2 := by nlinarith
  nlinarith

/-- Product of the numerator factors in the next `n` stages after `K`. -/
def prefixProduct (N : ℕ → ℝ) (K : ℕ) : ℕ → ℝ
  | 0 => 1
  | n + 1 => prefixProduct N K n * N (K + n + 1)

/-- Accumulated denominator loss in the reciprocal recurrence. -/
def prefixCost (N C : ℕ → ℝ) (K : ℕ) : ℕ → ℝ
  | 0 => 0
  | n + 1 => prefixCost N C K n + C (K + n + 1) * prefixProduct N K n

lemma prefixProduct_nonneg {N : ℕ → ℝ} {K n : ℕ}
    (hN : ∀ j < n, 0 ≤ N (K + j + 1)) : 0 ≤ prefixProduct N K n := by
  induction n with
  | zero => simp [prefixProduct]
  | succ n ih =>
      rw [prefixProduct]
      exact mul_nonneg (ih fun j hj => hN j (by omega)) (hN n (by omega))

lemma prefixCost_nonneg {N C : ℕ → ℝ} {K n : ℕ}
    (hN : ∀ j < n, 0 ≤ N (K + j + 1))
    (hC : ∀ j < n, 0 ≤ C (K + j + 1)) :
    0 ≤ prefixCost N C K n := by
  induction n with
  | zero => simp [prefixCost]
  | succ n ih =>
      rw [prefixCost]
      exact add_nonneg (ih (fun j hj => hN j (by omega)) (fun j hj => hC j (by omega)))
        (mul_nonneg (hC n (by omega))
          (prefixProduct_nonneg fun j hj => hN j (by omega)))

theorem prefixProduct_tail_le_exp_sum (n : ℕ) :
    prefixProduct tailN 10000 n ≤
      Real.exp (∑ j ∈ Finset.range n,
        11 / (((10000 + j + 1 : ℕ) : ℝ) *
          Real.log (10000 + j + 1 : ℕ))) := by
  induction n with
  | zero => simp [prefixProduct]
  | succ n ih =>
      rw [prefixProduct, Finset.sum_range_succ, Real.exp_add]
      apply mul_le_mul ih
      · simpa only [Nat.cast_add, Nat.cast_one] using
          tailN_le_exp (r := 10000 + n + 1) (by omega)
      · exact tailN_nonneg (by omega)
      · positivity

theorem prefixProduct_tail_le_log_ratio (n : ℕ) :
    prefixProduct tailN 10000 n ≤
      (Real.log (10000 + n : ℕ) / Real.log 10000) ^ 11 := by
  have hsum0 := invMulLog_sum_le (n := n)
  have hsum :
      (∑ j ∈ Finset.range n,
        11 / (((10000 + j + 1 : ℕ) : ℝ) *
          Real.log (10000 + j + 1 : ℕ))) ≤
        11 * (Real.log (Real.log (10000 + n : ℕ)) -
          Real.log (Real.log 10000)) := by
    calc
      (∑ j ∈ Finset.range n,
          11 / (((10000 + j + 1 : ℕ) : ℝ) *
            Real.log (10000 + j + 1 : ℕ))) =
          11 * ∑ j ∈ Finset.range n,
            (((10000 + j + 1 : ℕ) : ℝ)⁻¹ /
              Real.log (10000 + j + 1 : ℕ)) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j hj
        field_simp
      _ ≤ 11 * (Real.log (Real.log (10000 + n : ℕ)) -
          Real.log (Real.log 10000)) := by gcongr
  have hlogK : 0 < Real.log (10000 : ℝ) := Real.log_pos (by norm_num)
  have harg : (1 : ℝ) < ((10000 + n : ℕ) : ℝ) := by exact_mod_cast (by omega)
  have hlogn : 0 < Real.log ((10000 + n : ℕ) : ℝ) := Real.log_pos harg
  calc
    prefixProduct tailN 10000 n ≤
        Real.exp (∑ j ∈ Finset.range n,
          11 / (((10000 + j + 1 : ℕ) : ℝ) *
            Real.log (10000 + j + 1 : ℕ))) := prefixProduct_tail_le_exp_sum n
    _ ≤ Real.exp (11 * (Real.log (Real.log (10000 + n : ℕ)) -
        Real.log (Real.log 10000))) := Real.exp_le_exp.mpr hsum
    _ = (Real.log (10000 + n : ℕ) / Real.log 10000) ^ 11 := by
      rw [mul_sub, Real.exp_sub]
      rw [show (11 : ℝ) * Real.log (Real.log ((10000 + n : ℕ) : ℝ)) =
          (11 : ℕ) * Real.log (Real.log ((10000 + n : ℕ) : ℝ)) by norm_num,
        show (11 : ℝ) * Real.log (Real.log 10000) =
          (11 : ℕ) * Real.log (Real.log 10000) by norm_num,
        Real.exp_nat_mul, Real.exp_nat_mul, Real.exp_log hlogn,
        Real.exp_log hlogK, div_pow]

lemma prefixCost_eq_sum (N C : ℕ → ℝ) (K n : ℕ) :
    prefixCost N C K n =
      ∑ j ∈ Finset.range n, C (K + j + 1) * prefixProduct N K j := by
  induction n with
  | zero => simp [prefixCost]
  | succ n ih => simp [prefixCost, ih, Finset.sum_range_succ]

lemma P9_mono {u v : ℝ} (hu : 0 ≤ u) (huv : u ≤ v) : P9 u ≤ P9 v := by
  unfold P9
  gcongr

lemma tailCost_term_le (j : ℕ) :
    tailC (10000 + j + 1) * prefixProduct tailN 10000 j ≤
      (13 / Real.log (10000 : ℝ) ^ 11) *
        logPowerTail ((10000 + j + 1 : ℕ) : ℝ) := by
  let r : ℕ := 10000 + j + 1
  have hr : 10000 ≤ r := by omega
  have hrpos : (0 : ℝ) < r := by positivity
  have hrone : (1 : ℝ) < r := by exact_mod_cast (by dsimp [r]; omega)
  have hlogr : 0 < Real.log (r : ℝ) := Real.log_pos hrone
  have hlogK : 0 < Real.log (10000 : ℝ) := Real.log_pos (by norm_num)
  have hC := tailC_le hr
  have hP0 := prefixProduct_tail_le_log_ratio j
  have hlogmono : Real.log ((10000 + j : ℕ) : ℝ) ≤ Real.log (r : ℝ) := by
    apply Real.strictMonoOn_log.monotoneOn
    · exact Set.mem_Ioi.mpr (by exact_mod_cast (show 0 < 10000 + j by omega))
    · exact Set.mem_Ioi.mpr hrpos
    · exact_mod_cast (show 10000 + j ≤ r by dsimp [r]; omega)
  have hP : prefixProduct tailN 10000 j ≤
      (Real.log (r : ℝ) / Real.log 10000) ^ 11 := by
    exact hP0.trans (by gcongr)
  have hmul := mul_le_mul hC hP
    (prefixProduct_nonneg fun k hk => tailN_nonneg (by omega))
    (by positivity : 0 ≤ 13 / ((r : ℝ) ^ 2 * Real.log r ^ 2))
  calc
    tailC (10000 + j + 1) * prefixProduct tailN 10000 j =
        tailC r * prefixProduct tailN 10000 j := by rfl
    _ ≤ (13 / ((r : ℝ) ^ 2 * Real.log r ^ 2)) *
        (Real.log r / Real.log 10000) ^ 11 := hmul
    _ = (13 / Real.log (10000 : ℝ) ^ 11) * logPowerTail (r : ℝ) := by
      unfold logPowerTail
      field_simp

theorem prefixCost_tail_le (n : ℕ) :
    prefixCost tailN tailC 10000 n ≤
      (13 / Real.log (10000 : ℝ) ^ 11) *
        (P9 (Real.log 10000) / 10000) := by
  rw [prefixCost_eq_sum]
  calc
    (∑ j ∈ Finset.range n,
        tailC (10000 + j + 1) * prefixProduct tailN 10000 j) ≤
        ∑ j ∈ Finset.range n,
          (13 / Real.log (10000 : ℝ) ^ 11) *
            logPowerTail ((10000 + j + 1 : ℕ) : ℝ) := by
      exact Finset.sum_le_sum fun j hj => tailCost_term_le j
    _ = (13 / Real.log (10000 : ℝ) ^ 11) *
        ∑ j ∈ Finset.range n,
          logPowerTail ((10000 + j + 1 : ℕ) : ℝ) := by
      rw [Finset.mul_sum]
    _ ≤ (13 / Real.log (10000 : ℝ) ^ 11) *
        (P9 (Real.log 10000) / 10000) := by
      gcongr
      exact logPowerTail_sum_le_P9

theorem terminal_rational_comparison :
    (13000 : ℝ) * (13 / Real.log (10000 : ℝ) ^ 11) *
        (P9 (Real.log 10000) / 10000) < 1 := by
  have hlo := nine_twenty_one_hundredths_lt_log_ten_thousand
  have hhi := log_ten_thousand_lt_four_sixty_one_fiftieths
  have hP : P9 (Real.log 10000) ≤ P9 (461 / 50 : ℝ) :=
    P9_mono (Real.log_nonneg (by norm_num)) hhi.le
  have hpow : (921 / 100 : ℝ) ^ 11 ≤ Real.log 10000 ^ 11 := by gcongr
  have hlogpos : 0 < Real.log (10000 : ℝ) := Real.log_pos (by norm_num)
  calc
    (13000 : ℝ) * (13 / Real.log (10000 : ℝ) ^ 11) *
        (P9 (Real.log 10000) / 10000) =
      (13 * 13000 / 10000 : ℝ) * P9 (Real.log 10000) /
        Real.log 10000 ^ 11 := by ring
    _ ≤ (13 * 13000 / 10000 : ℝ) * P9 (461 / 50 : ℝ) /
        Real.log 10000 ^ 11 := by
      gcongr
    _ ≤ (13 * 13000 / 10000 : ℝ) * P9 (461 / 50 : ℝ) /
        (921 / 100 : ℝ) ^ 11 := by
      exact div_le_div_of_nonneg_left
        (mul_nonneg (by norm_num) (P9_nonneg (by norm_num))) (by positivity) hpow
    _ < 1 := by
      unfold P9
      norm_num

theorem tail_budget (n : ℕ) :
    (13000 : ℝ) * prefixCost tailN tailC 10000 n < 1 := by
  calc
    (13000 : ℝ) * prefixCost tailN tailC 10000 n ≤
        13000 * ((13 / Real.log (10000 : ℝ) ^ 11) *
          (P9 (Real.log 10000) / 10000)) := by
      gcongr
      exact prefixCost_tail_le n
    _ = 13000 * (13 / Real.log (10000 : ℝ) ^ 11) *
        (P9 (Real.log 10000) / 10000) := by ring
    _ < 1 := terminal_rational_comparison

lemma recurrenceMap_mono {c a x y : ℝ}
    (hc : 0 ≤ c) (ha : 0 ≤ a) (hx : 0 ≤ x) (hxy : x ≤ y)
    (hcy : c * y < 1) :
    x * a / (1 - c * x) ≤ y * a / (1 - c * y) := by
  have hcx : c * x < 1 := lt_of_le_of_lt (mul_le_mul_of_nonneg_left hxy hc) hcy
  rw [div_le_div_iff₀ (by linarith) (by linarith)]
  nlinarith [mul_nonneg (sub_nonneg.mpr hxy) ha]

/-- Reciprocal envelope for a finite stretch of the fixed-shape recurrence.
The hypotheses are deliberately independent of primes; the analytic theorem
below supplies `N`, `C`, and the budget bound. -/
theorem reciprocal_envelope
    {K n : ℕ} {f N C : ℕ → ℝ} {F : ℝ}
    (hF : 0 < F)
    (hf0 : 0 ≤ f K) (hfK : f K ≤ F)
    (hN : ∀ j < n, 0 ≤ N (K + j + 1))
    (hC : ∀ j < n, 0 ≤ C (K + j + 1))
    (hf_nonneg : ∀ j ≤ n, 0 ≤ f (K + j))
    (hbudget : ∀ j ≤ n, F * prefixCost N C K j < 1)
    (hrec : ∀ j < n, 0 < 1 - C (K + j + 1) * f (K + j) →
      f (K + j + 1) ≤
        f (K + j) * N (K + j + 1) /
          (1 - C (K + j + 1) * f (K + j))) :
    f (K + n) ≤
      F * prefixProduct N K n / (1 - F * prefixCost N C K n) := by
  induction n with
  | zero => simpa [prefixProduct, prefixCost] using hfK
  | succ n ih =>
      have hNn : 0 ≤ N (K + n + 1) := hN n (by omega)
      have hCn : 0 ≤ C (K + n + 1) := hC n (by omega)
      have hPn : 0 ≤ prefixProduct N K n :=
        prefixProduct_nonneg fun j hj => hN j (by omega)
      have hSn : 0 ≤ prefixCost N C K n :=
        prefixCost_nonneg (fun j hj => hN j (by omega))
          (fun j hj => hC j (by omega))
      have hb_n : F * prefixCost N C K n < 1 := hbudget n (by omega)
      have hb_succ : F * prefixCost N C K (n + 1) < 1 := hbudget (n + 1) le_rfl
      have hD : 0 < 1 - F * prefixCost N C K n := by linarith
      have hih : f (K + n) ≤
          F * prefixProduct N K n / (1 - F * prefixCost N C K n) := by
        apply ih
        · exact fun j hj => hN j (by omega)
        · exact fun j hj => hC j (by omega)
        · exact fun j hj => hf_nonneg j (by omega)
        · exact fun j hj => hbudget j (by omega)
        · exact fun j hj => hrec j (by omega)
      let B := F * prefixProduct N K n / (1 - F * prefixCost N C K n)
      have hB : 0 ≤ B := by
        dsimp [B]
        positivity
      have hcB : C (K + n + 1) * B < 1 := by
        change C (K + n + 1) *
          (F * prefixProduct N K n / (1 - F * prefixCost N C K n)) < 1
        calc
          C (K + n + 1) *
              (F * prefixProduct N K n / (1 - F * prefixCost N C K n)) =
            (C (K + n + 1) * F * prefixProduct N K n) /
              (1 - F * prefixCost N C K n) := by ring
          _ < 1 := (div_lt_iff₀ hD).2 (by
            rw [prefixCost] at hb_succ
            nlinarith)
      have hcf : C (K + n + 1) * f (K + n) < 1 :=
        lt_of_le_of_lt (mul_le_mul_of_nonneg_left hih hCn) hcB
      have hstep := hrec n (by omega) (by linarith)
      have hmap :
          f (K + n) * N (K + n + 1) /
              (1 - C (K + n + 1) * f (K + n)) ≤
            B * N (K + n + 1) /
              (1 - C (K + n + 1) * B) :=
        recurrenceMap_mono hCn hNn (hf_nonneg n (by omega)) hih hcB
      calc
        f (K + (n + 1)) = f (K + n + 1) := by congr 1 <;> omega
        _ ≤ f (K + n) * N (K + n + 1) /
            (1 - C (K + n + 1) * f (K + n)) := hstep
        _ ≤ B * N (K + n + 1) /
            (1 - C (K + n + 1) * B) := hmap
        _ = F * prefixProduct N K (n + 1) /
            (1 - F * prefixCost N C K (n + 1)) := by
          dsimp [B]
          rw [prefixProduct, prefixCost]
          field_simp
          ring

/-- The packaged continuation theorem used by the covering-system sieve.
Starting with the certified bound at stage `10000`, every denominator in the
fixed-`1/5` recurrence remains positive, and the reciprocal envelope bounds
the value at an arbitrary finite later horizon. -/
theorem survival_after_ten_thousand
    {n : ℕ} {f : ℕ → ℝ}
    (hf0 : 0 ≤ f 10000) (hfK : f 10000 ≤ 13000)
    (hf_nonneg : ∀ j ≤ n, 0 ≤ f (10000 + j))
    (hrec : ∀ j < n,
      0 < 1 - tailC (10000 + j + 1) * f (10000 + j) →
      f (10000 + j + 1) ≤
        f (10000 + j) * tailN (10000 + j + 1) /
          (1 - tailC (10000 + j + 1) * f (10000 + j))) :
    (∀ j < n, 0 < 1 - tailC (10000 + j + 1) * f (10000 + j)) ∧
      f (10000 + n) ≤
        13000 * prefixProduct tailN 10000 n /
          (1 - 13000 * prefixCost tailN tailC 10000 n) := by
  have hN : ∀ j < n, 0 ≤ tailN (10000 + j + 1) :=
    fun j hj => tailN_nonneg (by omega)
  have hC : ∀ j < n, 0 ≤ tailC (10000 + j + 1) :=
    fun j hj => tailC_nonneg (by omega)
  have hbudget : ∀ j ≤ n,
      (13000 : ℝ) * prefixCost tailN tailC 10000 j < 1 :=
    fun j hj => tail_budget j
  have henvelope (j : ℕ) (hj : j ≤ n) :
      f (10000 + j) ≤
        13000 * prefixProduct tailN 10000 j /
          (1 - 13000 * prefixCost tailN tailC 10000 j) := by
    apply reciprocal_envelope (K := 10000) (n := j) (F := 13000)
      (f := f) (N := tailN) (C := tailC)
    · norm_num
    · exact hf0
    · exact hfK
    · exact fun k hk => hN k (by omega)
    · exact fun k hk => hC k (by omega)
    · exact fun k hk => hf_nonneg k (by omega)
    · exact fun k hk => hbudget k (by omega)
    · exact fun k hk => hrec k (by omega)
  constructor
  · intro j hj
    have hD : 0 < 1 - (13000 : ℝ) * prefixCost tailN tailC 10000 j := by
      linarith [tail_budget j]
    have hbnext := tail_budget (j + 1)
    have hcB : tailC (10000 + j + 1) *
        (13000 * prefixProduct tailN 10000 j /
          (1 - 13000 * prefixCost tailN tailC 10000 j)) < 1 := by
      calc
        tailC (10000 + j + 1) *
            (13000 * prefixProduct tailN 10000 j /
              (1 - 13000 * prefixCost tailN tailC 10000 j)) =
          (tailC (10000 + j + 1) * 13000 *
            prefixProduct tailN 10000 j) /
              (1 - 13000 * prefixCost tailN tailC 10000 j) := by ring
        _ < 1 := (div_lt_iff₀ hD).2 (by
          rw [prefixCost] at hbnext
          nlinarith)
    have hcf : tailC (10000 + j + 1) * f (10000 + j) < 1 :=
      lt_of_le_of_lt
        (mul_le_mul_of_nonneg_left (henvelope j (by omega))
          (tailC_nonneg (by omega))) hcB
    linarith
  · exact henvelope n le_rfl

end Erdos586.Tail
