/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos48.GallagherRawDensity

/-!
# Decay of the higher-prime-power shell tail

The higher-prime-power remainder has square-root decay in the lower endpoint.
This finite estimate is what makes it harmless at the Page scale.
-/

open scoped BigOperators

noncomputable section

namespace Erdos48

theorem sqrt_mul_inv_le_two_mul_sqrt_inv
    {Y A : ℕ} (hY : 0 < Y) (hA : 0 < A) (hYA : Y ≤ 2 * A) :
    Real.sqrt (2 * (A : ℝ)) * (A : ℝ)⁻¹ ≤
      2 * (Real.sqrt (Y : ℝ))⁻¹ := by
  have hAR : (0 : ℝ) < A := by exact_mod_cast hA
  have hYR : (0 : ℝ) < Y := by exact_mod_cast hY
  have hx0 : 0 ≤ Real.sqrt (2 * (A : ℝ)) * (A : ℝ)⁻¹ := by positivity
  have hy0 : 0 ≤ 2 * (Real.sqrt (Y : ℝ))⁻¹ := by positivity
  apply (sq_le_sq₀ hx0 hy0).mp
  rw [mul_pow, Real.sq_sqrt (by positivity), mul_pow,
    inv_pow, inv_pow, Real.sq_sqrt hYR.le]
  have hcast : (Y : ℝ) ≤ 2 * (A : ℝ) := by exact_mod_cast hYA
  field_simp
  nlinarith

theorem activeShell_sqrt_ratio_le
    {Y N a : ℕ} (hY : 1 ≤ Y) (ha : a ∈ detectorActiveShells Y N) :
    Real.sqrt (2 * (2 ^ a : ℕ)) * ((2 ^ a : ℕ) : ℝ)⁻¹ ≤
      2 * (Real.sqrt (Y : ℝ))⁻¹ := by
  obtain ⟨n, hn⟩ := (Finset.mem_filter.mp ha).2
  have hnBand := Finset.mem_Ioc.mp (Finset.mem_filter.mp hn).1
  have hnBounds := Finset.mem_Ioc.mp
    (detectorDyadicShell_subset Y N a hY hn)
  have hYA : Y ≤ 2 * 2 ^ a := hnBand.1.le.trans hnBounds.2
  exact sqrt_mul_inv_le_two_mul_sqrt_inv (by omega) (by positivity) hYA

/-- Explicit square-root decay of the complete higher-prime-power tail. -/
theorem gallagherHigherPrimePowerShellTail_le
    (Y N : ℕ) (hY : 1 ≤ Y) :
    gallagherHigherPrimePowerShellTail Y N ≤
      2 * (((Nat.log 2 (N - 1) + 1 : ℕ) : ℝ) ^ 3 *
        Real.log 2 ^ 2) * (Real.sqrt (Y : ℝ))⁻¹ := by
  let M : ℕ := Nat.log 2 (N - 1) + 1
  let C : ℝ := (((M : ℝ) * Real.log 2) ^ 2) *
    (2 * (Real.sqrt (Y : ℝ))⁻¹)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hterm : ∀ a ∈ detectorActiveShells Y N,
      ((((a + 1 : ℕ) : ℝ) * Real.log 2) ^ 2 *
          Real.sqrt (2 * (2 ^ a : ℕ)) *
            ((2 ^ a : ℕ) : ℝ)⁻¹) ≤ C := by
    intro a ha
    have haRange := Finset.mem_range.mp ((detectorActiveShells_subset Y N) ha)
    have haM : a + 1 ≤ M := by dsimp [M]; omega
    have hlog : ((a + 1 : ℕ) : ℝ) * Real.log 2 ≤
        (M : ℝ) * Real.log 2 :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast haM)
        (Real.log_nonneg (by norm_num))
    have hlogSq := pow_le_pow_left₀ (by positivity) hlog 2
    have hratio := activeShell_sqrt_ratio_le hY ha
    dsimp [C]
    calc
      ((((a + 1 : ℕ) : ℝ) * Real.log 2) ^ 2 *
          Real.sqrt (2 * (2 ^ a : ℕ)) *
            ((2 ^ a : ℕ) : ℝ)⁻¹) =
        (((a + 1 : ℕ) : ℝ) * Real.log 2) ^ 2 *
          (Real.sqrt (2 * (2 ^ a : ℕ)) *
            ((2 ^ a : ℕ) : ℝ)⁻¹) := by ring
      _ ≤ ((M : ℝ) * Real.log 2) ^ 2 *
          (2 * (Real.sqrt (Y : ℝ))⁻¹) :=
        mul_le_mul hlogSq hratio (by positivity) (by positivity)
  unfold gallagherHigherPrimePowerShellTail
  calc
    (∑ a ∈ detectorActiveShells Y N,
        ((((a + 1 : ℕ) : ℝ) * Real.log 2) ^ 2 *
          Real.sqrt (2 * (2 ^ a : ℕ)) *
            ((2 ^ a : ℕ) : ℝ)⁻¹)) ≤
      ∑ _a ∈ detectorActiveShells Y N, C := Finset.sum_le_sum hterm
    _ = ((detectorActiveShells Y N).card : ℝ) * C := by simp
    _ ≤ (M : ℝ) * C := by
      apply mul_le_mul_of_nonneg_right _ hC
      exact_mod_cast detectorActiveShells_card_le Y N
    _ = 2 * (((Nat.log 2 (N - 1) + 1 : ℕ) : ℝ) ^ 3 *
        Real.log 2 ^ 2) * (Real.sqrt (Y : ℝ))⁻¹ := by
      dsimp [M, C]
      ring

end Erdos48

end
