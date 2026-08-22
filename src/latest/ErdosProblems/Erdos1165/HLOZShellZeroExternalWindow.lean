/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/
/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Formal Conjectures Authors.
-/

import ErdosProblems.Erdos1165.HLOZShellZeroReplacementWindows

/-!
# Concrete retained-count window for the shell-zero source

The source local-CLT is centered at `16 i / 15 = m`.  This file chooses the
integer retained-count interval by rounding the corresponding real interval
of radius `shellZeroCenterRadius m`.  Membership in that interval eventually
implies all three arithmetic facts needed by the literal coordinate window.
-/

open Filter

namespace Erdos1165.HLOZShellZeroExternalWindow

open HLOZProposition48Candidates HLOZShellZeroReplacementWindows
open HLOZSharpWindowProductClosure
open ScreeningInstantiation

noncomputable section

/-- Lower endpoint of the common retained-count interval. -/
def shellZeroExternalLow48 (m : ℕ) : ℕ :=
  Nat.ceil ((15 / 16 : ℝ) * ((m : ℝ) - shellZeroCenterRadius m))

/-- Exclusive upper endpoint of the common retained-count interval. -/
def shellZeroExternalHigh48 (m : ℕ) : ℕ :=
  Nat.floor ((15 / 16 : ℝ) * ((m : ℝ) + shellZeroCenterRadius m)) + 1

/-- The exact pathwise arithmetic needed to turn retained-count membership
into `TilingShellZeroCoordinateWindowData`. -/
def ShellZeroExternalWindowArithmeticAt
    (m externalLow externalHigh : ℕ) : Prop :=
  ∀ i, externalLow ≤ i → i < externalHigh →
    m / 2 ≤ i ∧
      i ≤ m - shellWidth48 m + 1 ∧
      |(m : ℝ) - (16 / 15 : ℝ) * (i : ℝ)| ≤ shellZeroCenterRadius m

theorem shellZeroExternalWindowArithmeticAt_of_small_radius
    {m : ℕ}
    (hsmall : 2 * (shellWidth48 m : ℝ) + geometricDeviation m ≤
      (m : ℝ) / 120) :
    ShellZeroExternalWindowArithmeticAt m (shellZeroExternalLow48 m)
      (shellZeroExternalHigh48 m) := by
  intro i hlow hhigh
  let R : ℝ := shellZeroCenterRadius m
  have hwidthNonneg : (0 : ℝ) ≤ shellWidth48 m := by positivity
  have hdevNonneg : 0 ≤ geometricDeviation m := geometricDeviation_nonneg m
  have hRNonneg : 0 ≤ R := by
    dsimp only [R, shellZeroCenterRadius]
    positivity
  have hRSmall : R ≤ (m : ℝ) / 120 := by
    dsimp only [R, shellZeroCenterRadius]
    nlinarith
  have hmNonneg : (0 : ℝ) ≤ m := by positivity
  have hleft : (15 / 16 : ℝ) * ((m : ℝ) - R) ≤ (i : ℝ) := by
    calc
      (15 / 16 : ℝ) * ((m : ℝ) - R) ≤
          (shellZeroExternalLow48 m : ℕ) := by
        exact Nat.le_ceil _
      _ ≤ (i : ℕ) := by exact_mod_cast hlow
  have hupperNat : i ≤
      Nat.floor ((15 / 16 : ℝ) * ((m : ℝ) + R)) := by
    change i < Nat.floor ((15 / 16 : ℝ) * ((m : ℝ) + R)) + 1 at hhigh
    omega
  have hright : (i : ℝ) ≤ (15 / 16 : ℝ) * ((m : ℝ) + R) := by
    calc
      (i : ℝ) ≤
          (Nat.floor ((15 / 16 : ℝ) * ((m : ℝ) + R)) : ℕ) := by
        exact_mod_cast hupperNat
      _ ≤ (15 / 16 : ℝ) * ((m : ℝ) + R) := by
        apply Nat.floor_le
        positivity
  have hcenter : |(m : ℝ) - (16 / 15 : ℝ) * (i : ℝ)| ≤ R := by
    rw [abs_le]
    constructor <;> nlinarith
  have hhalfR : ((m / 2 : ℕ) : ℝ) ≤ (i : ℝ) := by
    calc
      ((m / 2 : ℕ) : ℝ) ≤ (m : ℝ) / 2 := Nat.cast_div_le
      _ ≤ (15 / 16 : ℝ) * ((m : ℝ) - R) := by nlinarith
      _ ≤ (i : ℝ) := hleft
  have hhalf : m / 2 ≤ i := by exact_mod_cast hhalfR
  have hwidthLeR : (shellWidth48 m : ℝ) ≤ (m : ℝ) := by
    nlinarith
  have hwidthLe : shellWidth48 m ≤ m := by exact_mod_cast hwidthLeR
  have htranslateR : (i : ℝ) ≤ ((m - shellWidth48 m + 1 : ℕ) : ℝ) := by
    rw [Nat.cast_add, Nat.cast_sub hwidthLe, Nat.cast_one]
    dsimp only [R, shellZeroCenterRadius] at hright
    nlinarith
  have htranslate : i ≤ m - shellWidth48 m + 1 := by
    exact_mod_cast htranslateR
  exact ⟨hhalf, htranslate, hcenter⟩

/-- The concrete retained-count interval eventually satisfies every
coordinate-window side condition. -/
theorem eventually_shellZeroExternalWindowArithmetic48 :
    ∀ᶠ m : ℕ in atTop,
      ShellZeroExternalWindowArithmeticAt m (shellZeroExternalLow48 m)
        (shellZeroExternalHigh48 m) := by
  have hwidthPower :=
    ExternalProposition44.eventually_const_mul_nat_rpow_le
      960 kappaOne 1 (by norm_num [kappaOne])
  have hdeviationPower :=
    ExternalProposition44.eventually_const_mul_nat_rpow_le
      4320 (1 - kappaOne) 1 (by norm_num [kappaOne])
  filter_upwards [eventually_shellWidth48_cast_le_two_rpow,
      hwidthPower, hdeviationPower] with m hwidth hwidthPowerM
      hdeviationPowerM
  apply shellZeroExternalWindowArithmeticAt_of_small_radius
  have hwidthLinear : 480 * (shellWidth48 m : ℝ) ≤ (m : ℝ) := by
    simp only [Real.rpow_one] at hwidthPowerM
    nlinarith
  have hdeviationLinear : 240 * geometricDeviation m ≤ (m : ℝ) := by
    simp only [Real.rpow_one, geometricDeviation] at hdeviationPowerM ⊢
    nlinarith
  calc
    2 * (shellWidth48 m : ℝ) + geometricDeviation m =
        (1 / 240 : ℝ) * (480 * (shellWidth48 m : ℝ)) +
          (1 / 240 : ℝ) * (240 * geometricDeviation m) := by ring
    _ ≤ (1 / 240 : ℝ) * (m : ℝ) +
          (1 / 240 : ℝ) * (m : ℝ) := by
      exact add_le_add
        (mul_le_mul_of_nonneg_left hwidthLinear (by norm_num))
        (mul_le_mul_of_nonneg_left hdeviationLinear (by norm_num))
    _ = (m : ℝ) / 120 := by ring

end

end Erdos1165.HLOZShellZeroExternalWindow
