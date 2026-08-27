/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.InitialNeighborMargins
import ErdosProblems.Erdos207.KSSSLocalizedTwoAwayTail

/-! # Localized pattern size and bank budgets for the actual power-vortex package -/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

theorem InitialPowerVortexPackage.inner_separated
    {q h n ell t rootPower step : ℕ}
    (P : InitialPowerVortexPackage q h n ell t rootPower step)
    (i : Fin (ell + 1)) (hi : i ≠ 0) : AbsorberSeparatedLevel P.H P.X P.B (P.W.U i) := by
  rw [P.vortex_eq]
  exact separatedCardinalVortex_separated _ _ _ _ _ hi

theorem InitialPowerVortexPackage.pair_bank_coefficient_le_power
    {q h n ell t rootPower step : ℕ}
    (P : InitialPowerVortexPackage q h n ell t rootPower step)
    (hcoeff : powerAbsorberCrudeCoefficient q ≤ t) :
    (pairExactBankExtensionCoefficient q P.B : ℝ≥0) ≤ (t : ℝ≥0) ^ powerAbsorberCrudeExponent q rootPower := by
  have hone : (1 : ℝ≥0) ≤ 2 ^ q := one_le_pow₀ (by norm_num)
  have hweak : (pairExactBankExtensionCoefficient q P.B : ℝ≥0) ≤
      2 ^ q * pairExactBankExtensionCoefficient q P.B := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hone
      (bot_le : (0 : ℝ≥0) ≤ pairExactBankExtensionCoefficient q P.B)
  exact hweak.trans (P.crude_coefficients_le_power hcoeff).1

theorem InitialPowerVortexPackage.localized_pattern_budgets
    {q h n ell t rootPower step : ℕ}
    (P : InitialPowerVortexPackage q h n ell t rootPower step) (b r R : ℕ)
    (hcoeff : powerAbsorberCrudeCoefficient q ≤ t) (hrootCoeff : 45 * (q + 1) + 28 ≤ t)
    (hroot : r + q * (5 * b + 3) + 2 ≤ rootPower)
    (hgap : powerAbsorberCrudeExponent q rootPower + (r + q * (5 * b + 3) + 1) ≤ R)
    (hscale : t ^ R ≤ n) :
    (∀ i : Fin (ell + 1), (45 * (q + 1) + 28 : ℕ) * (t : ℝ≥0) ^ (r + q * (5 * b + 3) + 1) ≤
        ((P.W.U i).card : ℝ≥0)) ∧
      pairExactBankExtensionCoefficient q P.B * (t : ℝ≥0) ^ (r + q * (5 * b + 3) + 1) ≤ (n + 1 : ℝ≥0) := by
  have ht : (1 : ℝ≥0) ≤ t := by exact_mod_cast P.base_ge_one
  constructor
  · intro i
    have hnat : (45 * (q + 1) + 28) * t ^ (r + q * (5 * b + 3) + 1) ≤ (P.W.U i).card := by
      calc
        _ ≤ t * t ^ (r + q * (5 * b + 3) + 1) := Nat.mul_le_mul_right _ hrootCoeff
        _ = t ^ (r + q * (5 * b + 3) + 2) := by rw [show r + q * (5 * b + 3) + 2 = (r + q * (5 * b + 3) + 1) + 1 by omega, pow_succ]; ring
        _ ≤ t ^ rootPower := Nat.pow_le_pow_right (by omega : 0 < t) hroot
        _ ≤ _ := P.level_card_lower i
    exact_mod_cast hnat
  · calc
      _ ≤ (t : ℝ≥0) ^ powerAbsorberCrudeExponent q rootPower * (t : ℝ≥0) ^ (r + q * (5 * b + 3) + 1) :=
        mul_le_mul_of_nonneg_right (P.pair_bank_coefficient_le_power hcoeff)
          (bot_le : (0 : ℝ≥0) ≤ (t : ℝ≥0) ^ (r + q * (5 * b + 3) + 1))
      _ = (t : ℝ≥0) ^ (powerAbsorberCrudeExponent q rootPower + (r + q * (5 * b + 3) + 1)) := (pow_add _ _ _).symm
      _ ≤ (t : ℝ≥0) ^ R := pow_le_pow_right₀ ht hgap
      _ ≤ n := by exact_mod_cast hscale
      _ ≤ _ := by simp

end

end Erdos207
