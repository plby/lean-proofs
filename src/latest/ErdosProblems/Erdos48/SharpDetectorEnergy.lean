/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos48.DyadicDetectorShell
import Mathlib.NumberTheory.Chebyshev

/-!
# Sharp von Mangoldt energy on a detector shell

The pointwise estimate `Lambda(n) <= log n` loses two logarithms after
squaring.  Summing one copy of `Lambda` first and using Chebyshev's global
bound loses only one.  This is the factor which cancels the vertical packing
radius in the log-free density argument.
-/

namespace Erdos48

open Complex
open scoped BigOperators
open BoundedGaps.Maynard

noncomputable section

/-- Chebyshev's estimate gives the sharp square energy
`sum Lambda(n)^2 << A log(2A)` on every detector shell contained in
`(A,2A]`. -/
theorem sum_detectorDyadicShell_vonMangoldt_sq_le
    (Y N a : ℕ) (hY : 1 ≤ Y) :
    (∑ n ∈ detectorDyadicShell Y N a,
        ArithmeticFunction.vonMangoldt n ^ 2) ≤
      2 * (Real.log 4 + 4) * (2 ^ a : ℕ) *
        (((a + 1 : ℕ) : ℝ) * Real.log 2) := by
  let A : ℕ := 2 ^ a
  let P : ℝ := ((a + 1 : ℕ) : ℝ) * Real.log 2
  have hA : 0 < A := by dsimp [A]; positivity
  have hP : 0 ≤ P := by dsimp [P]; positivity
  have hsupport (n : ℕ) (hn : n ∈ detectorDyadicShell Y N a) :
      0 < n ∧ n ≤ 2 * A := by
    have hnBounds := Finset.mem_Ioc.mp
      (detectorDyadicShell_subset Y N a hY hn)
    refine ⟨hA.trans hnBounds.1, ?_⟩
    simpa only [A, pow_succ, Nat.mul_comm] using hnBounds.2
  have hlogLe (n : ℕ) (hn : n ∈ detectorDyadicShell Y N a) :
      ArithmeticFunction.vonMangoldt n ≤ P := by
    have hnData := hsupport n hn
    have hnPos : (0 : ℝ) < n := by exact_mod_cast hnData.1
    have hnUpper : (n : ℝ) ≤ 2 * (A : ℝ) := by exact_mod_cast hnData.2
    calc
      ArithmeticFunction.vonMangoldt n ≤ Real.log n :=
        ArithmeticFunction.vonMangoldt_le_log
      _ ≤ Real.log (2 * (A : ℝ)) :=
        Real.log_le_log hnPos hnUpper
      _ = P := by
        dsimp [A, P]
        rw [show (2 : ℝ) * (2 ^ a : ℕ) = (2 : ℝ) ^ (a + 1) by
          push_cast
          rw [pow_succ]
          ring]
        rw [Real.log_pow]
  have hpoint (n : ℕ) (hn : n ∈ detectorDyadicShell Y N a) :
      ArithmeticFunction.vonMangoldt n ^ 2 ≤
        ArithmeticFunction.vonMangoldt n * P := by
    rw [pow_two]
    exact mul_le_mul_of_nonneg_left (hlogLe n hn)
      ArithmeticFunction.vonMangoldt_nonneg
  have hprefix :
      (∑ n ∈ detectorDyadicShell Y N a,
          ArithmeticFunction.vonMangoldt n) ≤
        Chebyshev.psi ((2 * A : ℕ) : ℝ) := by
    rw [Chebyshev.psi, Nat.floor_natCast]
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro n hn
      exact Finset.mem_Ioc.mpr (hsupport n hn)
    · intro n hn hnot
      exact ArithmeticFunction.vonMangoldt_nonneg
  calc
    (∑ n ∈ detectorDyadicShell Y N a,
        ArithmeticFunction.vonMangoldt n ^ 2) ≤
        ∑ n ∈ detectorDyadicShell Y N a,
          ArithmeticFunction.vonMangoldt n * P := by
      exact Finset.sum_le_sum fun n hn ↦ hpoint n hn
    _ = (∑ n ∈ detectorDyadicShell Y N a,
          ArithmeticFunction.vonMangoldt n) * P := by
      rw [Finset.sum_mul]
    _ ≤ Chebyshev.psi ((2 * A : ℕ) : ℝ) * P :=
      mul_le_mul_of_nonneg_right hprefix hP
    _ ≤ ((Real.log 4 + 4) * ((2 * A : ℕ) : ℝ)) * P := by
      apply mul_le_mul_of_nonneg_right _ hP
      exact Chebyshev.psi_le_const_mul_self (by positivity)
    _ = 2 * (Real.log 4 + 4) * (A : ℝ) * P := by
      push_cast
      ring
    _ = _ := rfl

/-- Sharp coefficient energy for an order-`k` logarithmic detector.  The
power of the shell logarithm is `2k+1`, rather than the crude `2(k+1)`. -/
theorem sum_detectorDyadicShell_weighted_energy_sharp_le
    (Y N a k : ℕ) (hY : 1 ≤ Y) (eta : ℝ) (heta : 0 ≤ eta) :
    (∑ n ∈ detectorDyadicShell Y N a,
        ‖(weightedVonMangoldtMajorant eta k n : ℂ)‖ ^ 2) ≤
      2 * (Real.log 4 + 4) *
        ((((a + 1 : ℕ) : ℝ) * Real.log 2) ^ (2 * k + 1)) *
          (2 ^ a : ℕ) ^ (-(1 + 2 * eta)) := by
  let A : ℕ := 2 ^ a
  let P : ℝ := ((a + 1 : ℕ) : ℝ) * Real.log 2
  have hA : 0 < A := by dsimp [A]; positivity
  have hP : 0 ≤ P := by dsimp [P]; positivity
  have henergy := sum_detectorDyadicShell_vonMangoldt_sq_le Y N a hY
  have hpoint (n : ℕ) (hn : n ∈ detectorDyadicShell Y N a) :
      ‖(weightedVonMangoldtMajorant eta k n : ℂ)‖ ^ 2 ≤
        P ^ (2 * k) * ArithmeticFunction.vonMangoldt n ^ 2 *
          (A : ℝ) ^ (-(2 + 2 * eta)) := by
    have hnBounds := Finset.mem_Ioc.mp
      (detectorDyadicShell_subset Y N a hY hn)
    have hnPos : (0 : ℝ) < n := by exact_mod_cast (hA.trans hnBounds.1)
    have hnOne : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
    have hlog0 : 0 ≤ Real.log n := Real.log_nonneg hnOne
    have hlogLe : Real.log n ≤ P := by
      have hnUpper : (n : ℝ) ≤ 2 * (A : ℝ) := by
        exact_mod_cast (show n ≤ 2 * A by
          simpa only [A, pow_succ, Nat.mul_comm] using hnBounds.2)
      calc
        Real.log n ≤ Real.log (2 * (A : ℝ)) :=
          Real.log_le_log hnPos hnUpper
        _ = P := by
          dsimp [A, P]
          rw [show (2 : ℝ) * (2 ^ a : ℕ) = (2 : ℝ) ^ (a + 1) by
            push_cast
            rw [pow_succ]
            ring]
          rw [Real.log_pow]
    have hlogPow : Real.log n ^ (2 * k) ≤ P ^ (2 * k) :=
      pow_le_pow_left₀ hlog0 hlogLe (2 * k)
    have hrpow : (n : ℝ) ^ (-(2 + 2 * eta)) ≤
        (A : ℝ) ^ (-(2 + 2 * eta)) := by
      apply Real.rpow_le_rpow_of_nonpos
      · exact_mod_cast (show 1 ≤ A by omega)
      · exact_mod_cast hnBounds.1.le
      · linarith
    unfold weightedVonMangoldtMajorant
    rw [Complex.norm_real, Real.norm_of_nonneg (by positivity), mul_pow]
    have hsq : ((n : ℝ) ^ (-(1 + eta))) ^ 2 =
        (n : ℝ) ^ (-(2 + 2 * eta)) := by
      calc
        ((n : ℝ) ^ (-(1 + eta))) ^ 2 =
            ((n : ℝ) ^ (-(1 + eta))) ^ (2 : ℝ) :=
          (Real.rpow_natCast _ 2).symm
        _ = (n : ℝ) ^ (-(1 + eta) * 2) :=
          (Real.rpow_mul hnPos.le _ _).symm
        _ = _ := by congr 1 <;> ring
    rw [hsq]
    have hlogMul : (Real.log n ^ k) ^ 2 = Real.log n ^ (2 * k) := by
      rw [← pow_mul]
      congr 1
      omega
    rw [mul_pow, hlogMul]
    exact mul_le_mul (mul_le_mul hlogPow le_rfl (by positivity) (by positivity))
      hrpow (by positivity) (by positivity)
  calc
    (∑ n ∈ detectorDyadicShell Y N a,
        ‖(weightedVonMangoldtMajorant eta k n : ℂ)‖ ^ 2) ≤
        ∑ n ∈ detectorDyadicShell Y N a,
          P ^ (2 * k) * ArithmeticFunction.vonMangoldt n ^ 2 *
            (A : ℝ) ^ (-(2 + 2 * eta)) := by
      exact Finset.sum_le_sum fun n hn ↦ hpoint n hn
    _ = P ^ (2 * k) *
        (∑ n ∈ detectorDyadicShell Y N a,
          ArithmeticFunction.vonMangoldt n ^ 2) *
            (A : ℝ) ^ (-(2 + 2 * eta)) := by
      simp_rw [Finset.mul_sum, Finset.sum_mul]
    _ ≤ P ^ (2 * k) *
        (2 * (Real.log 4 + 4) * (A : ℝ) * P) *
          (A : ℝ) ^ (-(2 + 2 * eta)) := by
      gcongr
    _ = 2 * (Real.log 4 + 4) * P ^ (2 * k + 1) *
          (A : ℝ) ^ (-(1 + 2 * eta)) := by
      have hAreal : (0 : ℝ) < A := by exact_mod_cast hA
      have hpowA : (A : ℝ) * (A : ℝ) ^ (-(2 + 2 * eta)) =
          (A : ℝ) ^ (-(1 + 2 * eta)) := by
        calc
          (A : ℝ) * (A : ℝ) ^ (-(2 + 2 * eta)) =
              (A : ℝ) ^ (1 : ℝ) *
                (A : ℝ) ^ (-(2 + 2 * eta)) := by rw [Real.rpow_one]
          _ = (A : ℝ) ^ ((1 : ℝ) + -(2 + 2 * eta)) := by
            rw [Real.rpow_add hAreal]
          _ = _ := by congr 1 <;> ring
      rw [show P ^ (2 * k + 1) = P ^ (2 * k) * P by rw [pow_succ]]
      rw [← hpowA]
      ring
    _ = _ := rfl

end

end Erdos48
