/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos822.SlowCutoffLog
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Polynomial logarithms are negligible at the slow cutoff

The cutoff `y = floor (N^(1/(4*S)))` still grows polynomially in `N`.
Consequently every fixed power of `log N`, divided by `y`, tends to zero.
The explicit eventual bound below is the form needed by the B4 deletion.
-/

namespace Erdos822

open Filter

/-- A fixed multiple of a logarithmic power is eventually at most its
argument.  This is the natural-number specialization of Mathlib's standard
`log^k=o(x)` estimate. -/
theorem eventually_const_mul_log_pow_div_natCast_le_one
    (C : ℝ) (k : ℕ) :
    ∀ᶠ n : ℕ in atTop,
      C * Real.log (n : ℝ) ^ k / (n : ℝ) ≤ 1 := by
  by_cases hC : C ≤ 0
  · filter_upwards [eventually_ge_atTop 1] with n hn
    have hlog : 0 ≤ Real.log (n : ℝ) :=
      Real.log_nonneg (by exact_mod_cast hn)
    have hn0 : (0 : ℝ) ≤ n := by positivity
    have hnum : C * Real.log (n : ℝ) ^ k ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg hC (pow_nonneg hlog k)
    exact (div_nonpos_of_nonpos_of_nonneg hnum hn0).trans zero_le_one
  · have hCpos : 0 < C := lt_of_not_ge hC
    have hsmall :=
      (Real.isLittleO_pow_log_id_atTop (n := k)).bound (inv_pos.mpr hCpos)
    have hsmallNat := tendsto_natCast_atTop_atTop.eventually hsmall
    filter_upwards [hsmallNat, eventually_ge_atTop 1] with n hnsmall hn
    have hlog : 0 ≤ Real.log (n : ℝ) :=
      Real.log_nonneg (by exact_mod_cast hn)
    have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    have hpow : Real.log (n : ℝ) ^ k ≤ C⁻¹ * (n : ℝ) := by
      simpa only [Real.norm_eq_abs, id_eq,
        abs_of_nonneg (pow_nonneg hlog k), abs_of_nonneg hnR.le] using hnsmall
    apply (div_le_iff₀ hnR).2
    calc
      C * Real.log (n : ℝ) ^ k ≤ C * (C⁻¹ * (n : ℝ)) := by
        exact mul_le_mul_of_nonneg_left hpow hCpos.le
      _ = (n : ℝ) := by field_simp
      _ = 1 * (n : ℝ) := by ring

/-- The cubic logarithmic envelope used in all four slow-B4 channels is
eventually dominated by the cutoff itself. -/
theorem eventually_slowCutoff_log_cube_div_le_one
    {S : ℕ} (hS : 0 < S) :
    ∀ᶠ N : ℕ in atTop,
      let y := Nat.nthRoot (4 * S) N
      (1 + Real.log (N : ℝ)) ^ 3 / (y : ℝ) ≤ 1 := by
  let C : ℝ := (1 + 8 * (S : ℝ)) ^ 3
  obtain ⟨T, hT⟩ := Filter.eventually_atTop.mp
    (eventually_const_mul_log_pow_div_natCast_le_one C 3)
  filter_upwards [eventually_nthRoot_ge (4 * S) (max 4 T) (by omega)] with N hroot
  let y := Nat.nthRoot (4 * S) N
  have hy4 : 4 ≤ y := le_trans (le_max_left 4 T) hroot
  have hyT : T ≤ y := le_trans (le_max_right 4 T) hroot
  have hlogy0 : 0 ≤ Real.log (y : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ y by omega))
  have hlogy1 : 1 ≤ Real.log (y : ℝ) := by
    have h4y : Real.log (4 : ℝ) ≤ Real.log (y : ℝ) :=
      Real.strictMonoOn_log.monotoneOn
        (by simp only [Set.mem_Ioi]; norm_num)
        (by simp only [Set.mem_Ioi]; positivity)
        (by exact_mod_cast hy4)
    have hlog4 : (1 : ℝ) < Real.log 4 := by
      rw [show (4 : ℝ) = 2 * 2 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
      nlinarith [Real.log_two_gt_d9]
    exact hlog4.le.trans h4y
  have hlogratio := log_div_log_slowSieveCutoff_le hS
    (show 2 ≤ Nat.nthRoot (4 * S) N by simpa [y] using (show 2 ≤ y by omega))
  have hlogN : Real.log (N : ℝ) ≤
      8 * (S : ℝ) * Real.log (y : ℝ) := by
    have hlogypos : 0 < Real.log (y : ℝ) := zero_lt_one.trans_le hlogy1
    exact (div_le_iff₀ hlogypos).mp (by simpa [y] using hlogratio)
  have hbase :
      1 + Real.log (N : ℝ) ≤
        (1 + 8 * (S : ℝ)) * Real.log (y : ℝ) := by
    nlinarith
  have hbase0 : 0 ≤ 1 + Real.log (N : ℝ) := by
    have hN1 : 1 ≤ N := by
      have hyN : y ≤ N := by
        dsimp [y]
        exact nthRoot_le_self_of_pos (by omega)
      omega
    have hN1R : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN1
    exact add_nonneg zero_le_one (Real.log_nonneg hN1R)
  have hCbound := hT y hyT
  dsimp [C] at hCbound
  calc
    (1 + Real.log (N : ℝ)) ^ 3 / (y : ℝ) ≤
        ((1 + 8 * (S : ℝ)) * Real.log (y : ℝ)) ^ 3 / (y : ℝ) := by
      gcongr
    _ = (1 + 8 * (S : ℝ)) ^ 3 * Real.log (y : ℝ) ^ 3 /
          (y : ℝ) := by ring
    _ ≤ 1 := hCbound

end Erdos822
