/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.CFP.Bilu.Section92MahlerVolumeConversion

/-!
# Scaled Section 4 volume decay

This file isolates the two scalar comparisons needed when Section 4 is run
with a single rank-uniform normalization.  The terminal weighted volume is
dominated by a fixed multiple of ordinary body volume at the rank ceiling,
and the Proposition 7.5 decay inequality is stable under multiplication of
every body volume by the same positive scale.
-/

namespace Erdos186.CFP.Bilu.Section4ScaledDecay

open Section92PresentationDescent
open Section92WeightedRankRepair
open Section92MahlerVolumeConversion

noncomputable section

set_option autoImplicit false

/-- The fixed rank-ceiling multiple of ordinary body volume used to compare
all terminal weighted volumes in one Section 4 minimization. -/
def uniformTerminalBodyVolume {A : Finset ℤ}
    (s rankBound : ℕ) (X : RankedBodyPresentation A) : ℝ :=
  (uniformMahlerOuterVolumeConstant rankBound : ℝ) *
    canonicalRankRepairFactor s rankBound ^ rankBound * bodyVolume X

theorem uniformTerminalBodyVolume_pos {A : Finset ℤ}
    (s rankBound : ℕ) (X : RankedBodyPresentation A) :
    0 < uniformTerminalBodyVolume s rankBound X := by
  apply mul_pos
  · apply mul_pos
    · exact_mod_cast uniformMahlerOuterVolumeConstant_pos rankBound
    · exact pow_pos
        (lt_of_lt_of_le zero_lt_one
          (one_le_canonicalRankRepairFactor s rankBound)) _
  · exact bodyVolume_pos X

/-- At every rank below the fixed ceiling, the terminal rank-weighted
volume is bounded by the uniform ceiling-rank multiple. -/
theorem terminalScaledBodyVolume_le_uniformTerminalBodyVolume
    {A : Finset ℤ} (s rankBound : ℕ) (X : RankedBodyPresentation A)
    (hrank : X.1 ≤ rankBound) :
    terminalScaledBodyVolume s rankBound X ≤
      uniformTerminalBodyVolume s rankBound X := by
  have hrepair : 1 ≤ canonicalRankRepairFactor s rankBound :=
    one_le_canonicalRankRepairFactor s rankBound
  have hpow : canonicalRankRepairFactor s rankBound ^ X.1 ≤
      canonicalRankRepairFactor s rankBound ^ rankBound :=
    pow_le_pow_right₀ hrepair hrank
  have hvolume : 0 ≤ bodyVolume X := (bodyVolume_pos X).le
  have hconstant :
      (0 : ℝ) ≤ uniformMahlerOuterVolumeConstant rankBound := by
    positivity
  unfold terminalScaledBodyVolume rankWeightedBodyVolume
    uniformTerminalBodyVolume
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_right hpow hvolume) hconstant

/-- Multiplying all candidate volumes and the raw bound by the same
positive scale preserves the Section 4 decay inequality. -/
theorem scaled_decay_of_decay
    {A : Finset ℤ} (x y : RankedBodyPresentation A)
    {scale rawBound : ℝ} {q : ℕ}
    (hscale : 0 < scale) (hq : 0 < q)
    (hdecay : (2 * bodyVolume y) ^ q ≤
      rawBound * bodyVolume x ^ (q - 1)) :
    (2 * (scale * bodyVolume y)) ^ q ≤
      (scale * rawBound) * (scale * bodyVolume x) ^ (q - 1) := by
  have hscalePow : 0 ≤ scale ^ q := (pow_pos hscale q).le
  have hscaled := mul_le_mul_of_nonneg_left hdecay hscalePow
  have hqSucc : q - 1 + 1 = q := by omega
  have hscaleQ : scale ^ q = scale * scale ^ (q - 1) := by
    calc
      scale ^ q = scale ^ (q - 1 + 1) := by rw [hqSucc]
      _ = scale * scale ^ (q - 1) := pow_succ' scale (q - 1)
  calc
    (2 * (scale * bodyVolume y)) ^ q =
        scale ^ q * (2 * bodyVolume y) ^ q := by ring
    _ ≤ scale ^ q *
        (rawBound * bodyVolume x ^ (q - 1)) := hscaled
    _ = (scale * rawBound) *
        (scale * bodyVolume x) ^ (q - 1) := by
      rw [mul_pow, hscaleQ]
      ring

end

end Erdos186.CFP.Bilu.Section4ScaledDecay

#print axioms
  Erdos186.CFP.Bilu.Section4ScaledDecay.uniformTerminalBodyVolume_pos
#print axioms
  Erdos186.CFP.Bilu.Section4ScaledDecay.terminalScaledBodyVolume_le_uniformTerminalBodyVolume
#print axioms Erdos186.CFP.Bilu.Section4ScaledDecay.scaled_decay_of_decay
