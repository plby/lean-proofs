import Arxiv.Arxiv2411_18291.PaperSizeParameters
import Mathlib.Analysis.Asymptotics.Defs

/-!
# Exact logarithm and growth of the printed threshold

The bound keeps the factor `2^r` explicit. The big-O formulation lets q
vary with r fixed, so its constant is not asserted to be uniform in r.
-/

open Filter

namespace Arxiv2411_18291

theorem log_paperSizeThreshold (q r : ℕ) :
    Real.log (paperSizeThreshold q r : ℝ) =
      (90 * q * paperInverseAlpha q r : ℝ) * Real.log (4 * q : ℝ) := by
  simp only [paperSizeThreshold, Nat.cast_pow, Nat.cast_mul, Nat.cast_ofNat, Real.log_pow]

theorem log_paperSizeThreshold_expanded (q r : ℕ) :
    Real.log (paperSizeThreshold q r : ℝ) =
      3240 * (2 : ℝ) ^ r * (q : ℝ) ^ (r + 1) * (q.choose r : ℝ) ^ 2 *
        Real.log (4 * q : ℝ) := by
  rw [log_paperSizeThreshold, paperInverseAlpha]
  push_cast
  rw [mul_pow, pow_succ (q : ℝ) r]
  ring

theorem log_four_mul_le_three_log {q : ℕ} (hq : 2 ≤ q) :
    Real.log (4 * q : ℝ) ≤ 3 * Real.log (q : ℝ) := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hlog : Real.log 2 ≤ Real.log (q : ℝ) :=
    Real.log_le_log (by norm_num) (by exact_mod_cast hq)
  have hfour : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    norm_num
  rw [Real.log_mul (by norm_num) hq0.ne', hfour]
  linarith only [hlog]

theorem log_paperSizeThreshold_le {q : ℕ} (hq : 2 ≤ q) (r : ℕ) :
    Real.log (paperSizeThreshold q r : ℝ) ≤
      (9720 * (2 : ℝ) ^ r) *
        ((q.choose r : ℝ) ^ 2 * (q : ℝ) ^ (r + 1) * Real.log (q : ℝ)) := by
  rw [log_paperSizeThreshold_expanded]
  calc
    _ ≤ (3240 * (2 : ℝ) ^ r * (q : ℝ) ^ (r + 1) * (q.choose r : ℝ) ^ 2) *
        (3 * Real.log (q : ℝ)) :=
      mul_le_mul_of_nonneg_left (log_four_mul_le_three_log hq) (by positivity)
    _ = _ := by ring

theorem log_paperSizeThreshold_isBigO (r : ℕ) :
    Asymptotics.IsBigO atTop (fun q : ℕ => Real.log (paperSizeThreshold q r : ℝ))
      (fun q : ℕ => (q.choose r : ℝ) ^ 2 * (q : ℝ) ^ (r + 1) * Real.log (q : ℝ)) := by
  apply Asymptotics.IsBigO.of_bound (9720 * (2 : ℝ) ^ r)
  filter_upwards [eventually_ge_atTop (2 : ℕ)] with q hq
  have hsize : (1 : ℝ) ≤ paperSizeThreshold q r := by
    have hn : 1 ≤ paperSizeThreshold q r := one_le_pow₀ (by omega : 1 ≤ 4 * q)
    exact_mod_cast hn
  have hf : 0 ≤ Real.log (paperSizeThreshold q r : ℝ) := Real.log_nonneg hsize
  have hlog : 0 ≤ Real.log (q : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ q by omega))
  have hg : 0 ≤ (q.choose r : ℝ) ^ 2 * (q : ℝ) ^ (r + 1) * Real.log (q : ℝ) := by positivity
  simpa only [Real.norm_eq_abs, abs_of_nonneg hf, abs_of_nonneg hg] using
    log_paperSizeThreshold_le hq r

end Arxiv2411_18291
