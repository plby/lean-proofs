/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos851.Scales

/-!
# Exponential absorption of interval-sieve errors

The one- and two-shift endpoint errors are polynomial in the logarithmic
number of shifts and at most quadratic in the divisor level.  These elementary
integer estimates make their decay against the shell length explicit.
-/

namespace Erdos851

/-- A deliberately coarse polynomial-versus-exponential estimate. -/
theorem eight_mul_add_seven_sq_le_two_pow {q : ℕ} (hq : 24 ≤ q) :
    (8 * q + 7) ^ 2 ≤ 2 ^ q := by
  induction q, hq using Nat.le_induction with
  | base => norm_num
  | succ q hq ih =>
      have hstep : (8 * (q + 1) + 7) ^ 2 ≤ 2 * (8 * q + 7) ^ 2 := by
        nlinarith
      calc
        (8 * (q + 1) + 7) ^ 2 ≤ 2 * (8 * q + 7) ^ 2 := hstep
        _ ≤ 2 * 2 ^ q := Nat.mul_le_mul_left 2 ih
        _ = 2 ^ (q + 1) := by rw [pow_succ]; ring

/-- Once `J ≥ 192`, its square is absorbed by `2^(J/8)`. -/
theorem sq_le_two_pow_div_eight {J : ℕ} (hJ : 192 ≤ J) :
    J ^ 2 ≤ 2 ^ (J / 8) := by
  let q := J / 8
  have hq : 24 ≤ q := by
    dsimp [q]
    omega
  have hJq : J ≤ 8 * q + 7 := by
    dsimp [q]
    omega
  exact (Nat.pow_le_pow_left hJq 2).trans
    (eight_mul_add_seven_sq_le_two_pow hq)

/-- After multiplying by an arbitrary fixed power `2^N`, the total pair
endpoint error still lies below the dyadic shell scale. -/
theorem pow_mul_sq_mul_distributionLevel_sq_le
    {N J : ℕ} (hJlarge : 192 ≤ J) (hJN : 8 * N ≤ J) :
    2 ^ N * (J ^ 2 * distributionLevel J ^ 2) ≤ 2 ^ J := by
  have hpoly := sq_le_two_pow_div_eight hJlarge
  have hlevel := distributionLevel_sq_le J
  have hexp : N + J / 8 + J / 2 ≤ J := by omega
  calc
    2 ^ N * (J ^ 2 * distributionLevel J ^ 2) ≤
        2 ^ N * (2 ^ (J / 8) * 2 ^ (J / 2)) := by
      gcongr
    _ = 2 ^ (N + J / 8 + J / 2) := by
      rw [← pow_add, ← pow_add]
      congr 1
      omega
    _ ≤ 2 ^ J := Nat.pow_le_pow_right (by norm_num) hexp

/-- The same explicit error bound relative to an arbitrary shell endpoint
whose preceding dyadic scale is `2^J`. -/
theorem pow_mul_sq_mul_distributionLevel_sq_le_scale
    {N J X : ℕ} (hJlarge : 192 ≤ J) (hJN : 8 * N ≤ J)
    (hscale : 2 ^ J ≤ X) :
    2 ^ N * (J ^ 2 * distributionLevel J ^ 2) ≤ X :=
  (pow_mul_sq_mul_distributionLevel_sq_le hJlarge hJN).trans hscale

/-- The logarithmic scale tends to infinity with the interval endpoint. -/
theorem tendsto_logIndex_atTop :
    Filter.Tendsto logIndex Filter.atTop Filter.atTop := by
  rw [Filter.tendsto_atTop_atTop]
  intro J
  refine ⟨2 ^ J, ?_⟩
  intro X hX
  exact Nat.le_log_of_pow_le (by norm_num : 1 < 2) hX

end Erdos851
