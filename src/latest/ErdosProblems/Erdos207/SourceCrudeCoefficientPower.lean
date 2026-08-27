/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.SourceCrudeUniformCoefficient

/-! # The uniform source coefficient has an explicit polynomial power bound -/

namespace Erdos207

open scoped NNReal

noncomputable section

theorem sourceCrudeUniformCoefficient_scale
    (ell q h : ℕ) (w Z : ℝ≥0) (hw : 1 ≤ w) (hZ : 1 ≤ Z) :
    sourceCrudeUniformCoefficient ell q h w Z ≤
      sourceCrudeUniformCoefficient ell q h 1 1 * Z ^ 2 * w ^ (2 * q) := by
  let P := Z * w ^ q
  let a1 := ((h : ℝ≥0) + (h : ℝ≥0) ^ 2) * sourceCrudeBaseCoefficient ell q 1 1
  let a2 := (h : ℝ≥0) ^ 2 *
    (2 * sourceCommonGoodCoefficient ell q 1 1 1 + sourceGainReverseGoodCoefficient ell q 1 1 1)
  have hP : 1 ≤ P := one_le_mul_of_one_le_of_one_le hZ (one_le_pow₀ hw)
  have hP2 : P ≤ P ^ 2 := by simpa only [pow_one] using pow_le_pow_right₀ hP (show 1 ≤ 2 by omega)
  have h1 : 1 ≤ P ^ 2 := one_le_pow₀ hP
  have hid : sourceCrudeUniformCoefficient ell q h w Z = 1 + a1 * P + a2 * P ^ 2 := by
    dsimp [sourceCrudeUniformCoefficient, sourceCrudeDoubleCoefficient, sourceCrudeBaseCoefficient,
      sourceCommonGoodCoefficient, sourceGainReverseGoodCoefficient, sourceCommonClassCoefficient,
      a1, a2, P]
    ring
  have hid1 : sourceCrudeUniformCoefficient ell q h 1 1 = 1 + a1 + a2 := by
    dsimp [sourceCrudeUniformCoefficient, sourceCrudeDoubleCoefficient, sourceCrudeBaseCoefficient,
      sourceCommonGoodCoefficient, sourceGainReverseGoodCoefficient, sourceCommonClassCoefficient, a1, a2]
    ring
  calc
    _ = 1 + a1 * P + a2 * P ^ 2 := hid
    _ ≤ P ^ 2 + a1 * P ^ 2 + a2 * P ^ 2 :=
      add_le_add (add_le_add h1 (mul_le_mul_of_nonneg_left hP2 zero_le)) le_rfl
    _ = sourceCrudeUniformCoefficient ell q h 1 1 * Z ^ 2 * w ^ (2 * q) := by
      rw [hid1]
      dsimp [P]
      ring

theorem sourceCrudeUniformCoefficient_power
    (ell q h a b : ℕ) (t w Z : ℝ≥0) (hw : 1 ≤ w) (hZ : 1 ≤ Z)
    (hwt : w ≤ t ^ a) (hZt : Z ≤ t ^ b) :
    sourceCrudeUniformCoefficient ell q h w Z ≤
      sourceCrudeUniformCoefficient ell q h 1 1 * t ^ (2 * b + 2 * q * a) := by
  calc
    _ ≤ sourceCrudeUniformCoefficient ell q h 1 1 * Z ^ 2 * w ^ (2 * q) :=
      sourceCrudeUniformCoefficient_scale ell q h w Z hw hZ
    _ ≤ sourceCrudeUniformCoefficient ell q h 1 1 * (t ^ b) ^ 2 * (t ^ a) ^ (2 * q) := by gcongr
    _ = _ := by rw [← pow_mul, ← pow_mul, pow_add]; ring

theorem sourceCrudeUniformCoefficient_power_cutoff
    (ell q h a b k : ℕ) (t w Z : ℝ≥0) (ht : 1 ≤ t) (hw : 1 ≤ w) (hZ : 1 ≤ Z)
    (hwt : w ≤ t ^ a) (hZt : Z ≤ t ^ b)
    (hconstant : sourceCrudeUniformCoefficient ell q h 1 1 ≤ t)
    (hk : 2 * b + 2 * q * a + 2 ≤ k) :
    t * sourceCrudeUniformCoefficient ell q h w Z ≤ t ^ k := by
  calc
    _ ≤ t * (sourceCrudeUniformCoefficient ell q h 1 1 * t ^ (2 * b + 2 * q * a)) :=
      mul_le_mul_of_nonneg_left (sourceCrudeUniformCoefficient_power ell q h a b t w Z hw hZ hwt hZt) zero_le
    _ ≤ t * (t * t ^ (2 * b + 2 * q * a)) := by gcongr
    _ = t ^ (2 * b + 2 * q * a + 2) := by rw [pow_add]; ring
    _ ≤ t ^ k := pow_le_pow_right₀ ht hk

end

end Erdos207
