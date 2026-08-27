/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.UniformSourceStageScale
import ErdosProblems.Erdos207.PowerSourceWellSpread

/-! # Keep the first-prefix bank coefficient while bounding the frozen source envelope -/

namespace Erdos207

open scoped NNReal

noncomputable section

theorem source_augmented_coefficient_power
    (t u z : ℝ≥0) (c v d : ℕ) (ht : 1 ≤ t) (hu : 4 ≤ u) (hc : 1 ≤ c)
    (hvd : v ≤ d) (hpower : t ^ d ≤ u ^ c) (hz : z ≤ t ^ v) :
    z + 3 * u ^ 4 ≤ u ^ (5 * c) := by
  have hu1 : 1 ≤ u := (by norm_num : (1 : ℝ≥0) ≤ 4).trans hu
  have hzc : z ≤ u ^ c := (hz.trans (pow_le_pow_right₀ ht hvd)).trans hpower
  have hzc4 : z ≤ u ^ (4 * c) := hzc.trans (pow_le_pow_right₀ hu1 (by omega))
  have h4c : u ^ 4 ≤ u ^ (4 * c) := pow_le_pow_right₀ hu1 (by omega)
  have hu4 : 4 ≤ u ^ c := hu.trans (by simpa only [pow_one] using pow_le_pow_right₀ hu1 hc)
  calc
    _ ≤ u ^ (4 * c) + 3 * u ^ (4 * c) :=
      add_le_add hzc4 (mul_le_mul_of_nonneg_left h4c zero_le)
    _ = 4 * u ^ (4 * c) := by ring
    _ ≤ u ^ c * u ^ (4 * c) := mul_le_mul_of_nonneg_right hu4 zero_le
    _ = _ := by rw [← pow_add]; congr 1; omega

theorem source_bank_coefficient_power
    (t count C Z : ℝ≥0) (E v : ℕ) (ht : 1 ≤ t)
    (hcount : count ≤ t ^ E) (hconstant : 2 * C + Z ≤ t) (hEv : E + 1 ≤ v) :
    2 * (count * C) + Z ≤ t ^ v := by
  have hZ : Z ≤ Z * t ^ E := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left (one_le_pow₀ ht : 1 ≤ t ^ E) zero_le
  calc
    _ ≤ 2 * (t ^ E * C) + Z * t ^ E := by gcongr
    _ = (2 * C + Z) * t ^ E := by ring
    _ ≤ t * t ^ E := mul_le_mul_of_nonneg_right hconstant zero_le
    _ = t ^ (E + 1) := (pow_succ' _ _).symm
    _ ≤ _ := pow_le_pow_right₀ ht hEv

theorem InitialPowerVortexPackage.zero_prefix_source_coefficient_power
    {q h n ell t rootPower step Rfixed : ℕ}
    (P : InitialPowerVortexPackage q h n ell t rootPower step)
    (hbank : powerBankSubsetCoefficient q ≤ t)
    (hfixed : powerBankSubsetExponent q rootPower + 2 ≤ Rfixed)
    (j : ℕ) (hconstant : 2 * (exactBankVortexOrderCoefficient q 0 : ℝ≥0) +
      exactBankVortexCoefficient j 0 ≤ t) :
    2 * ((subsetsUpToCard P.B q).card * (exactBankVortexOrderCoefficient q 0 : ℝ≥0)) +
      exactBankVortexCoefficient j 0 ≤ (t : ℝ≥0) ^ (Rfixed + step + 1) := by
  apply source_bank_coefficient_power
    (t : ℝ≥0) (subsetsUpToCard P.B q).card (exactBankVortexOrderCoefficient q 0)
    (exactBankVortexCoefficient j 0) (powerBankSubsetExponent q rootPower) (Rfixed + step + 1)
    (by exact_mod_cast P.base_ge_one)
    (by exact_mod_cast P.bankSubsets_le_power hbank) hconstant (by omega)

end

end Erdos207
