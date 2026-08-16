import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Algebra.Order.Floor.Semifield

/-!
# Numerical absorption for the projective marked-tree estimate

The marked-tree argument produces

`2^m * (4 * q^(2*t-1))^w * (A * q^t)^(m-w)`

with `w = A*q*ceil(log q)`.  This file proves, with completely explicit
constants, that the first two factors can be absorbed into the base of the
last power as soon as `m` is at least a constant times `q*(log q)^2`.

Everything is stated over `ℝ`, which is the form in which the tuple-count
estimate is consumed by the construction.
-/

namespace Erdos920.NumericAbsorption

noncomputable section

/-- The number of unmarked levels supplied by the container argument. -/
def unmarkedBudget (A q : ℕ) : ℕ :=
  A * q * Nat.ceil (Real.log (q : ℝ))

/-- One explicit constant which works simultaneously in the lower bound on
`m` and in the final exponential base. -/
def absorptionConstant (t A : ℕ) : ℕ :=
  8 * t * A

/-- An explicit lower threshold for `q`; no primality is used here. -/
def absorptionThreshold : ℕ := 4

theorem absorptionConstant_pos {t A : ℕ} (ht : 1 ≤ t) (hA : 1 ≤ A) :
    0 < absorptionConstant t A := by
  exact Nat.mul_pos (Nat.mul_pos (by norm_num) (Nat.zero_lt_of_lt ht))
    (Nat.zero_lt_of_lt hA)

private theorem half_le_log_of_four_le {q : ℕ} (hq : 4 ≤ q) :
    (1 / 2 : ℝ) ≤ Real.log (q : ℝ) := by
  have hfour : (4 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have hlog_mono : Real.log (4 : ℝ) ≤ Real.log (q : ℝ) :=
    Real.log_le_log (by norm_num) hfour
  have hhalf_two : (1 / 2 : ℝ) ≤ Real.log 2 :=
    Real.log_two_gt_d9.le.trans' (by norm_num)
  have hlog_four : Real.log (4 : ℝ) = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    norm_num
  rw [hlog_four] at hlog_mono
  linarith

private theorem one_le_log_of_four_le {q : ℕ} (hq : 4 ≤ q) :
    (1 : ℝ) ≤ Real.log (q : ℝ) := by
  have hfour : (4 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have hlog_mono : Real.log (4 : ℝ) ≤ Real.log (q : ℝ) :=
    Real.log_le_log (by norm_num) hfour
  have hhalf_two : (1 / 2 : ℝ) ≤ Real.log 2 :=
    Real.log_two_gt_d9.le.trans' (by norm_num)
  have hlog_four : Real.log (4 : ℝ) = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    norm_num
  rw [hlog_four] at hlog_mono
  linarith

/-- The ceiling in `unmarkedBudget` costs at most a factor of two. -/
theorem unmarkedBudget_cast_le {A q : ℕ} (hq : 4 ≤ q) :
    (unmarkedBudget A q : ℝ) ≤
      2 * (A : ℝ) * (q : ℝ) * Real.log (q : ℝ) := by
  have hceil : (Nat.ceil (Real.log (q : ℝ)) : ℝ) ≤
      2 * Real.log (q : ℝ) := by
    exact Nat.ceil_le_two_mul (by
      simpa only [one_div] using half_le_log_of_four_le hq)
  simp only [unmarkedBudget, Nat.cast_mul]
  have hA0 : (0 : ℝ) ≤ A := by positivity
  have hq0 : (0 : ℝ) ≤ q := by positivity
  calc
    (A : ℝ) * q * Nat.ceil (Real.log (q : ℝ)) ≤
        (A : ℝ) * q * (2 * Real.log (q : ℝ)) := by gcongr
    _ = 2 * (A : ℝ) * q * Real.log (q : ℝ) := by ring

/-- The assumed `q*(log q)^2` budget in particular makes the unmarked-level
parameter no larger than the path length. -/
theorem unmarkedBudget_le {t A q m : ℕ}
    (ht : 1 ≤ t) (hA : 1 ≤ A) (hq : 4 ≤ q)
    (hm : (absorptionConstant t A : ℝ) * (q : ℝ) *
        Real.log (q : ℝ) ^ 2 ≤ (m : ℝ)) :
    unmarkedBudget A q ≤ m := by
  have hA0 : (0 : ℝ) ≤ A := by positivity
  have hq0 : (0 : ℝ) ≤ q := by positivity
  have hlog1 := one_le_log_of_four_le hq
  have hlog0 : 0 ≤ Real.log (q : ℝ) := zero_le_one.trans hlog1
  have hceil := unmarkedBudget_cast_le (A := A) hq
  have hconst : (2 : ℝ) * A ≤ absorptionConstant t A := by
    simp only [absorptionConstant, Nat.cast_mul, Nat.cast_ofNat]
    nlinarith [show (1 : ℝ) ≤ t by exact_mod_cast ht]
  have hsquare : Real.log (q : ℝ) ≤ Real.log (q : ℝ) ^ 2 := by
    nlinarith
  have hreal : (unmarkedBudget A q : ℝ) ≤ (m : ℝ) := by
    calc
      (unmarkedBudget A q : ℝ) ≤ 2 * A * q * Real.log (q : ℝ) := hceil
      _ ≤ (absorptionConstant t A : ℝ) * q * Real.log (q : ℝ) ^ 2 := by
        gcongr
      _ ≤ (m : ℝ) := hm
  exact_mod_cast hreal

/-- The polynomial loss from the unmarked levels is bounded by a second
copy of `2^m`.  This is the analytic heart of the absorption. -/
theorem q_pow_unmarked_loss_le {t A q m : ℕ}
    (ht : 1 ≤ t) (hA : 1 ≤ A) (hq : 4 ≤ q)
    (hm : (absorptionConstant t A : ℝ) * (q : ℝ) *
        Real.log (q : ℝ) ^ 2 ≤ (m : ℝ)) :
    (q : ℝ) ^ (2 * t * unmarkedBudget A q) ≤ (2 : ℝ) ^ m := by
  have hA0 : (0 : ℝ) ≤ A := by
    exact_mod_cast (Nat.zero_lt_of_lt hA).le
  have hqpos : (0 : ℝ) < q := by positivity
  have hlog0 : 0 ≤ Real.log (q : ℝ) :=
    (zero_le_one.trans (one_le_log_of_four_le hq))
  have hw := unmarkedBudget_cast_le (A := A) hq
  have hlog_two_half : (1 / 2 : ℝ) ≤ Real.log 2 :=
    Real.log_two_gt_d9.le.trans' (by norm_num)
  have hexponent :
      ((2 * t * unmarkedBudget A q : ℕ) : ℝ) * Real.log (q : ℝ) ≤
        (m : ℝ) * Real.log 2 := by
    have hleft :
        ((2 * t * unmarkedBudget A q : ℕ) : ℝ) * Real.log (q : ℝ) ≤
          4 * (t : ℝ) * A * q * Real.log (q : ℝ) ^ 2 := by
      simp only [Nat.cast_mul, Nat.cast_ofNat]
      calc
        (2 * (t : ℝ) * (unmarkedBudget A q : ℝ)) * Real.log (q : ℝ) ≤
            (2 * (t : ℝ) * (2 * A * q * Real.log (q : ℝ))) *
              Real.log (q : ℝ) := by gcongr
        _ = 4 * (t : ℝ) * A * q * Real.log (q : ℝ) ^ 2 := by ring
    have hbudget :
        4 * (t : ℝ) * A * q * Real.log (q : ℝ) ^ 2 ≤ (m : ℝ) / 2 := by
      have hm' := hm
      simp only [absorptionConstant, Nat.cast_mul, Nat.cast_ofNat] at hm'
      linarith
    have hm0 : (0 : ℝ) ≤ m := by positivity
    calc
      ((2 * t * unmarkedBudget A q : ℕ) : ℝ) * Real.log (q : ℝ) ≤
          4 * (t : ℝ) * A * q * Real.log (q : ℝ) ^ 2 := hleft
      _ ≤ (m : ℝ) / 2 := hbudget
      _ ≤ (m : ℝ) * Real.log 2 := by nlinarith
  rw [← Real.log_le_log_iff (pow_pos hqpos _) (by positivity),
    Real.log_pow, Real.log_pow]
  simpa [mul_comm] using hexponent

/-- Explicit numerical absorption of the marked-tree loss.

No primality assumption on `q` is needed; `4 ≤ q` is the only threshold.
The same explicit constant `8*t*A` occurs in the lower bound on `m` and in
the final base. -/
theorem markedTree_numeric_absorption {t A q m : ℕ}
    (ht : 1 ≤ t) (hA : 1 ≤ A) (hq : 4 ≤ q)
    (hm : (absorptionConstant t A : ℝ) * (q : ℝ) *
        Real.log (q : ℝ) ^ 2 ≤ (m : ℝ)) :
    (2 : ℝ) ^ m *
          (4 * (q : ℝ) ^ (2 * t - 1)) ^ unmarkedBudget A q *
          ((A : ℝ) * (q : ℝ) ^ t) ^ (m - unmarkedBudget A q) ≤
      ((absorptionConstant t A : ℝ) * (q : ℝ) ^ t) ^ m := by
  let w := unmarkedBudget A q
  have hw : w ≤ m := unmarkedBudget_le ht hA hq hm
  have hq0 : (0 : ℝ) ≤ q := by positivity
  have hdelta :
      (4 : ℝ) * (q : ℝ) ^ (2 * t - 1) ≤ (q : ℝ) ^ (2 * t) := by
    calc
      (4 : ℝ) * (q : ℝ) ^ (2 * t - 1) ≤
          (q : ℝ) * (q : ℝ) ^ (2 * t - 1) := by
        gcongr
        exact_mod_cast hq
      _ = (q : ℝ) ^ (2 * t) := by
        rw [← pow_succ']
        congr 1
        omega
  have hdelta_pow :
      ((4 : ℝ) * (q : ℝ) ^ (2 * t - 1)) ^ w ≤ (2 : ℝ) ^ m := by
    calc
      ((4 : ℝ) * (q : ℝ) ^ (2 * t - 1)) ^ w ≤
          ((q : ℝ) ^ (2 * t)) ^ w := by gcongr
      _ = (q : ℝ) ^ (2 * t * w) := by rw [← pow_mul]
      _ ≤ (2 : ℝ) ^ m := q_pow_unmarked_loss_le ht hA hq hm
  have hbase : (1 : ℝ) ≤ (A : ℝ) * (q : ℝ) ^ t := by
    have hAreal : (1 : ℝ) ≤ A := by exact_mod_cast hA
    have hqreal : (1 : ℝ) ≤ q := by exact_mod_cast (le_trans (by omega : 1 ≤ 4) hq)
    nlinarith [show (1 : ℝ) ≤ (q : ℝ) ^ t from one_le_pow₀ hqreal]
  have hlast :
      ((A : ℝ) * (q : ℝ) ^ t) ^ (m - w) ≤
        ((A : ℝ) * (q : ℝ) ^ t) ^ m := by
    exact pow_le_pow_right₀ hbase (Nat.sub_le m w)
  have hCbase :
      (4 : ℝ) * ((A : ℝ) * (q : ℝ) ^ t) ≤
        (absorptionConstant t A : ℝ) * (q : ℝ) ^ t := by
    have htR : (1 : ℝ) ≤ t := by exact_mod_cast ht
    simp only [absorptionConstant, Nat.cast_mul, Nat.cast_ofNat]
    have hqt0 : (0 : ℝ) ≤ (q : ℝ) ^ t := by positivity
    nlinarith
  change (2 : ℝ) ^ m *
      (4 * (q : ℝ) ^ (2 * t - 1)) ^ w *
      ((A : ℝ) * (q : ℝ) ^ t) ^ (m - w) ≤ _
  calc
    (2 : ℝ) ^ m *
          (4 * (q : ℝ) ^ (2 * t - 1)) ^ w *
          ((A : ℝ) * (q : ℝ) ^ t) ^ (m - w) ≤
        (2 : ℝ) ^ m * (2 : ℝ) ^ m *
          ((A : ℝ) * (q : ℝ) ^ t) ^ m := by gcongr
    _ = ((4 : ℝ) * ((A : ℝ) * (q : ℝ) ^ t)) ^ m := by
      rw [← mul_pow, ← mul_pow]
      ring_nf
    _ ≤ ((absorptionConstant t A : ℝ) * (q : ℝ) ^ t) ^ m := by
      gcongr

end

end Erdos920.NumericAbsorption
