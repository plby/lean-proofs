/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos822.NthRootScale
import Mathlib.NumberTheory.Harmonic.Bounds

/-!
# Logarithmic size of the slow sieve cutoff

For y = floor(N^(1/(4S))), the elementary nth-root upper approximation
gives N <= 2^(4S) y^(4S).  Once y >= 2 this implies
log N / log y <= 8S, and hence H_N / log y is uniformly bounded.
-/

namespace Erdos822

/-- The logarithm ratio attached to the slow cutoff is bounded by 8S. -/
theorem log_div_log_slowSieveCutoff_le
    {N S : ℕ} (hS : 0 < S)
    (hy : 2 ≤ Nat.nthRoot (4 * S) N) :
    Real.log (N : ℝ) /
        Real.log (Nat.nthRoot (4 * S) N : ℝ) ≤
      8 * (S : ℝ) := by
  let y := Nat.nthRoot (4 * S) N
  have hy2 : 2 ≤ y := by simpa [y] using hy
  have hypos : (0 : ℝ) < y := by exact_mod_cast (by omega : 0 < y)
  have hlogy : 0 < Real.log (y : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < y by omega))
  have hlog2 : 0 < Real.log (2 : ℝ) :=
    Real.log_pos (by norm_num)
  have hNat :
      N ≤ 2 ^ (4 * S) * y ^ (4 * S) := by
    dsimp [y]
    exact le_two_pow_mul_nthRoot_pow (by omega) (by omega)
  have hR : (0 : ℝ) < N := by
    have hNy : 0 < N := by
      by_contra hzero
      have : N = 0 := by omega
      rw [this, Nat.nthRoot_zero_right (by omega)] at hy
      omega
    exact_mod_cast hNy
  have hprodR :
      (0 : ℝ) < ((2 ^ (4 * S) * y ^ (4 * S) : ℕ) : ℝ) := by
    exact_mod_cast (by positivity : 0 < 2 ^ (4 * S) * y ^ (4 * S))
  have hlogmono :
      Real.log (N : ℝ) ≤
        Real.log (((2 ^ (4 * S) * y ^ (4 * S) : ℕ) : ℝ)) :=
    Real.strictMonoOn_log.monotoneOn
      (by simp only [Set.mem_Ioi]; exact hR)
      (by simp only [Set.mem_Ioi]; exact hprodR)
      (by exact_mod_cast hNat)
  have hlogprod :
      Real.log (((2 ^ (4 * S) * y ^ (4 * S) : ℕ) : ℝ)) =
        (4 * (S : ℝ)) *
          (Real.log (2 : ℝ) + Real.log (y : ℝ)) := by
    push_cast
    rw [Real.log_mul (by positivity) (by positivity),
      Real.log_pow, Real.log_pow]
    push_cast
    ring
  have hlog2le : Real.log (2 : ℝ) ≤ Real.log (y : ℝ) := by
    exact Real.strictMonoOn_log.monotoneOn
      (by simp only [Set.mem_Ioi]; norm_num)
      (by simp only [Set.mem_Ioi]; exact hypos)
      (by exact_mod_cast hy2)
  have htop :
      Real.log (N : ℝ) ≤
        (8 * (S : ℝ)) * Real.log (y : ℝ) := by
    calc
      Real.log (N : ℝ) ≤
          Real.log (((2 ^ (4 * S) * y ^ (4 * S) : ℕ) : ℝ)) :=
        hlogmono
      _ = (4 * (S : ℝ)) *
          (Real.log (2 : ℝ) + Real.log (y : ℝ)) := hlogprod
      _ ≤ (8 * (S : ℝ)) * Real.log (y : ℝ) := by
        have hS0 : (0 : ℝ) ≤ S := by positivity
        nlinarith
  simpa [y] using (div_le_iff₀ hlogy).2 htop

/-- The harmonic factor divided by the slow-cutoff logarithm is uniformly
bounded in terms of S alone. -/
theorem harmonic_div_log_slowSieveCutoff_le
    {N S : ℕ} (hS : 0 < S)
    (hy : 2 ≤ Nat.nthRoot (4 * S) N) :
    (harmonic N : ℝ) /
        Real.log (Nat.nthRoot (4 * S) N : ℝ) ≤
      (1 : ℝ) / Real.log 2 + 8 * (S : ℝ) := by
  let y := Nat.nthRoot (4 * S) N
  have hy2 : 2 ≤ y := by simpa [y] using hy
  have hlogy : 0 < Real.log (y : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < y by omega))
  have hlog2 : 0 < Real.log (2 : ℝ) :=
    Real.log_pos (by norm_num)
  have hlog2le : Real.log (2 : ℝ) ≤ Real.log (y : ℝ) := by
    apply Real.strictMonoOn_log.monotoneOn
    · simp only [Set.mem_Ioi]
      norm_num
    · simp only [Set.mem_Ioi]
      exact_mod_cast (show 0 < y by omega)
    · exact_mod_cast hy2
  have hH : (harmonic N : ℝ) ≤ 1 + Real.log (N : ℝ) :=
    harmonic_le_one_add_log N
  have hratio :
      Real.log (N : ℝ) / Real.log (y : ℝ) ≤ 8 * (S : ℝ) := by
    simpa [y] using log_div_log_slowSieveCutoff_le hS hy
  calc
    (harmonic N : ℝ) / Real.log (y : ℝ) ≤
        (1 + Real.log (N : ℝ)) / Real.log (y : ℝ) :=
      div_le_div_of_nonneg_right hH hlogy.le
    _ = (1 : ℝ) / Real.log (y : ℝ) +
        Real.log (N : ℝ) / Real.log (y : ℝ) := by ring
    _ ≤ (1 : ℝ) / Real.log 2 + 8 * (S : ℝ) := by
      apply add_le_add
      · exact one_div_le_one_div_of_le hlog2 hlog2le
      · exact hratio

end Erdos822
