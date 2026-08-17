import Mathlib

/-!
# Analytic estimates for Erdős Problem 877

This file isolates the elementary asymptotic step used after the combinatorial
counting argument.  Any eventual exponential bound with base strictly smaller
than `√2` is little-o of `2 ^ (n / 2)`.
-/

open Filter
open scoped Topology

namespace Erdos877

/-- The benchmark appearing in Erdős Problem 877, written using real powers. -/
noncomputable def benchmark (n : ℕ) : ℝ := Real.rpow 2 ((n : ℝ) / 2)

/-- The real-power benchmark `2 ^ (n / 2)` is exactly `(√2) ^ n`. -/
@[simp] theorem benchmark_eq_sqrt_pow (n : ℕ) :
    benchmark n = (Real.sqrt 2) ^ n := by
  simpa only [benchmark, Real.rpow_eq_pow, Real.rpow_natCast] using
    (Real.rpow_div_two_eq_sqrt (x := (2 : ℝ)) (n : ℝ) (by norm_num))

/-- An eventual exponential upper bound with base below `√2` is little-o of
the Erdős 877 benchmark. -/
theorem isLittleO_benchmark_of_eventually_norm_le_pow
    {f : ℕ → ℝ} {a : ℝ} (ha0 : 0 ≤ a) (ha : a < Real.sqrt 2)
    (hf : ∀ᶠ n in atTop, ‖f n‖ ≤ a ^ n) :
    f =o[atTop] benchmark := by
  have hfO : f =O[atTop] (fun n : ℕ ↦ a ^ n) := by
    apply Asymptotics.IsBigO.of_bound'
    filter_upwards [hf] with n hn
    simpa only [norm_pow, Real.norm_eq_abs, abs_of_nonneg ha0] using hn
  exact hfO.trans_isLittleO
    ((isLittleO_pow_pow_of_lt_left ha0 ha).congr' EventuallyEq.rfl
      (Eventually.of_forall fun n ↦ (benchmark_eq_sqrt_pow n).symm))

/-- A uniform saving in the exponent of `2` implies little-o of the benchmark.
This is the form naturally produced by estimates of the shape
`2 ^ ((1 / 2 - δ) n)` with `δ > 0`. -/
theorem isLittleO_benchmark_of_eventually_norm_le_rpow
    {f : ℕ → ℝ} {δ : ℝ} (hδ : 0 < δ)
    (hf : ∀ᶠ n in atTop,
      ‖f n‖ ≤ Real.rpow 2 (((1 / 2 : ℝ) - δ) * (n : ℝ))) :
    f =o[atTop] benchmark := by
  let a : ℝ := Real.rpow 2 ((1 / 2 : ℝ) - δ)
  have ha0 : 0 ≤ a := Real.rpow_nonneg (by norm_num) _
  have ha : a < Real.sqrt 2 := by
    rw [Real.sqrt_eq_rpow]
    exact Real.rpow_lt_rpow_of_exponent_lt (by norm_num) (by linarith)
  apply isLittleO_benchmark_of_eventually_norm_le_pow ha0 ha
  filter_upwards [hf] with n hn
  refine hn.trans_eq ?_
  symm
  dsimp [a]
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]

end Erdos877
