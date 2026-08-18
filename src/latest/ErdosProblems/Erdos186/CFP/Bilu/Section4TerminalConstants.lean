/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.CFP.Bilu.Section4ScaledDecay

/-!
# Uniform terminal constants for Section 4

The scaled body-volume minimization uses one real normalization depending
only on the scale and rank ceiling.  This file rounds a single bound for
both the bounded-cardinality cube and the large-cardinality decay branch,
and reserves the additional singleton budget needed by the final Mahler
realization.
-/

namespace Erdos186.CFP.Bilu.Section4TerminalConstants

open Section92MahlerVolumeConversion
open Section92WeightedRankRepair

noncomputable section

set_option autoImplicit false

/-- The rank-uniform real normalization multiplying ordinary body volume. -/
def uniformTerminalScale (s rankBound : ℕ) : ℝ :=
  (uniformMahlerOuterVolumeConstant rankBound : ℝ) *
    canonicalRankRepairFactor s rankBound ^ rankBound

theorem uniformTerminalScale_pos (s rankBound : ℕ) :
    0 < uniformTerminalScale s rankBound := by
  apply mul_pos
  · exact_mod_cast uniformMahlerOuterVolumeConstant_pos rankBound
  · exact pow_pos
      (lt_of_lt_of_le zero_lt_one
        (one_le_canonicalRankRepairFactor s rankBound)) _

/-- One natural terminal volume constant covering the small cube, the
scaled large-cardinality bound, and the singleton realization. -/
def terminalVolumeConstant
    (s rankBound cardinalityThreshold rawConstant : ℕ) : ℕ :=
  Nat.ceil (uniformTerminalScale s rankBound *
      ((rawConstant + 2 ^ cardinalityThreshold : ℕ) : ℝ)) +
    2 * uniformMahlerOuterVolumeConstant rankBound

theorem terminalVolumeConstant_pos
    (s rankBound cardinalityThreshold rawConstant : ℕ)
    (_hthreshold : 1 ≤ cardinalityThreshold) :
    0 < terminalVolumeConstant
      s rankBound cardinalityThreshold rawConstant := by
  have hM : 0 < uniformMahlerOuterVolumeConstant rankBound :=
    uniformMahlerOuterVolumeConstant_pos rankBound
  unfold terminalVolumeConstant
  omega

/-- The terminal constant includes the complete singleton budget. -/
theorem two_mul_uniformMahlerOuterVolumeConstant_le_terminalVolumeConstant
    (s rankBound cardinalityThreshold rawConstant : ℕ)
    (_hthreshold : 1 ≤ cardinalityThreshold) :
    2 * uniformMahlerOuterVolumeConstant rankBound ≤
      terminalVolumeConstant
        s rankBound cardinalityThreshold rawConstant := by
  unfold terminalVolumeConstant
  omega

/-- The scaled cube volume is absorbed uniformly below the cardinality
threshold. -/
theorem uniformTerminalScale_mul_two_pow_le_terminalVolumeConstant_mul
    (s rankBound cardinalityThreshold rawConstant N : ℕ)
    (_hthreshold : 1 ≤ cardinalityThreshold)
    (hN : 0 < N) (hNthreshold : N ≤ cardinalityThreshold) :
    uniformTerminalScale s rankBound * ((2 ^ N : ℕ) : ℝ) ≤
      ((terminalVolumeConstant s rankBound cardinalityThreshold rawConstant *
        N : ℕ) : ℝ) := by
  let scale := uniformTerminalScale s rankBound
  let rawTotal : ℕ := rawConstant + 2 ^ cardinalityThreshold
  let rounded : ℕ := Nat.ceil (scale * (rawTotal : ℝ))
  let terminal := terminalVolumeConstant
    s rankBound cardinalityThreshold rawConstant
  have hscale : 0 ≤ scale :=
    (uniformTerminalScale_pos s rankBound).le
  have hpowNat : 2 ^ N ≤ 2 ^ cardinalityThreshold :=
    Nat.pow_le_pow_right (by norm_num) hNthreshold
  have hpow : ((2 ^ N : ℕ) : ℝ) ≤
      ((2 ^ cardinalityThreshold : ℕ) : ℝ) := by
    exact_mod_cast hpowNat
  have hpowRaw : ((2 ^ cardinalityThreshold : ℕ) : ℝ) ≤
      (rawTotal : ℝ) := by
    dsimp only [rawTotal]
    exact_mod_cast (show 2 ^ cardinalityThreshold ≤
      rawConstant + 2 ^ cardinalityThreshold by omega)
  have hceil : scale * (rawTotal : ℝ) ≤ (rounded : ℝ) := by
    dsimp only [rounded]
    exact Nat.le_ceil _
  have hroundedTerminal : rounded ≤ terminal := by
    dsimp only [rounded, terminal, scale, rawTotal,
      terminalVolumeConstant]
    exact Nat.le_add_right _ _
  have hterminalMul : terminal ≤ terminal * N :=
    Nat.le_mul_of_pos_right terminal hN
  calc
    uniformTerminalScale s rankBound * ((2 ^ N : ℕ) : ℝ) =
        scale * ((2 ^ N : ℕ) : ℝ) := rfl
    _ ≤ scale * ((2 ^ cardinalityThreshold : ℕ) : ℝ) :=
      mul_le_mul_of_nonneg_left hpow hscale
    _ ≤ scale * (rawTotal : ℝ) :=
      mul_le_mul_of_nonneg_left hpowRaw hscale
    _ ≤ (rounded : ℝ) := hceil
    _ ≤ (terminal : ℝ) := by exact_mod_cast hroundedTerminal
    _ ≤ ((terminal * N : ℕ) : ℝ) := by
      exact_mod_cast hterminalMul

/-- The same ceiling absorbs the scaled linear raw bound at every positive
cardinality. -/
theorem uniformTerminalScale_mul_rawConstant_mul_le_terminalVolumeConstant_mul
    (s rankBound cardinalityThreshold rawConstant N : ℕ)
    (_hthreshold : 1 ≤ cardinalityThreshold) (hN : 0 < N) :
    uniformTerminalScale s rankBound *
        (((rawConstant * N : ℕ) : ℝ)) ≤
      ((terminalVolumeConstant s rankBound cardinalityThreshold rawConstant *
        N : ℕ) : ℝ) := by
  let scale := uniformTerminalScale s rankBound
  let rawTotal : ℕ := rawConstant + 2 ^ cardinalityThreshold
  let rounded : ℕ := Nat.ceil (scale * (rawTotal : ℝ))
  let terminal := terminalVolumeConstant
    s rankBound cardinalityThreshold rawConstant
  have hscale : 0 ≤ scale :=
    (uniformTerminalScale_pos s rankBound).le
  have hraw : (rawConstant : ℝ) ≤ (rawTotal : ℝ) := by
    dsimp only [rawTotal]
    exact_mod_cast (Nat.le_add_right rawConstant (2 ^ cardinalityThreshold))
  have hceil : scale * (rawTotal : ℝ) ≤ (rounded : ℝ) := by
    dsimp only [rounded]
    exact Nat.le_ceil _
  have hroundedTerminal : rounded ≤ terminal := by
    dsimp only [rounded, terminal, scale, rawTotal,
      terminalVolumeConstant]
    exact Nat.le_add_right _ _
  have hcoefficient : scale * (rawConstant : ℝ) ≤
      (terminal : ℝ) := by
    calc
      scale * (rawConstant : ℝ) ≤ scale * (rawTotal : ℝ) :=
        mul_le_mul_of_nonneg_left hraw hscale
      _ ≤ (rounded : ℝ) := hceil
      _ ≤ (terminal : ℝ) := by exact_mod_cast hroundedTerminal
  have hNnonneg : (0 : ℝ) ≤ N := by positivity
  calc
    uniformTerminalScale s rankBound *
          (((rawConstant * N : ℕ) : ℝ)) =
        (scale * (rawConstant : ℝ)) * (N : ℝ) := by
      push_cast
      ring
    _ ≤ (terminal : ℝ) * (N : ℝ) :=
      mul_le_mul_of_nonneg_right hcoefficient hNnonneg
    _ = ((terminal * N : ℕ) : ℝ) := by
      norm_num [Nat.cast_mul]

end

end Erdos186.CFP.Bilu.Section4TerminalConstants

#print axioms
  Erdos186.CFP.Bilu.Section4TerminalConstants.terminalVolumeConstant_pos
#print axioms
  Erdos186.CFP.Bilu.Section4TerminalConstants.two_mul_uniformMahlerOuterVolumeConstant_le_terminalVolumeConstant
#print axioms
  Erdos186.CFP.Bilu.Section4TerminalConstants.uniformTerminalScale_mul_two_pow_le_terminalVolumeConstant_mul
#print axioms
  Erdos186.CFP.Bilu.Section4TerminalConstants.uniformTerminalScale_mul_rawConstant_mul_le_terminalVolumeConstant_mul
