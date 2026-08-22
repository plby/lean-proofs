/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/
/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Formal Conjectures Authors.
-/

import ErdosProblems.Erdos1165.HLOZCandidateLocalBroadThetaProduct
import ErdosProblems.Erdos1165.HLOZSourceCorrectFullGapClosure

/-!
# Concrete data for the corrected full-beta product

The source-correct full-beta record now contains only numerical choices.  This
file fixes the external threshold at `m / 2` and uses the early-creation cutoff
as a uniform finite coordinate bound.  The capacity inequality follows from
the concrete shell-zero center window and the broad `m^(7/10)` bound.
-/

open Filter Set

namespace Erdos1165.HLOZConcreteFullBetaProductData

open HLOZCandidateLocalBroadThetaProduct HLOZCandidateLocalLazyCap
open HLOZPathEvents HLOZShellZeroExternalWindow
open HLOZProposition48Candidates
open HLOZShellZeroReplacementWindows HLOZSourceCorrectFullGapClosure
open HLOZSharpWindowProductClosure ScreeningInstantiation

noncomputable section

abbrev DominoTiling := Tilings.Tiling

/-- The retained endpoint threshold used by the concrete candidate-local
product.  It is deliberately below the shell-zero center near `15m/16`. -/
def concreteExternalThreshold48 (m : ℕ) : ℕ := m / 2

theorem eventually_concreteExternalThreshold48_pos :
    ∀ᶠ m : ℕ in atTop, 0 < concreteExternalThreshold48 m := by
  filter_upwards [eventually_ge_atTop (2 : ℕ)] with m hm
  unfold concreteExternalThreshold48
  omega

/-- The concrete lazy cap, half-level external threshold, and broad deficit
window fit below the level. -/
theorem eventually_concreteFullBeta_capacity :
    ∀ᶠ m : ℕ in atTop,
      sourceCandidateLazyCap48 m + concreteExternalThreshold48 m +
        Nat.ceil ((m : ℝ) ^ (7 / 10 : ℝ)) ≤ m + 1 := by
  filter_upwards [eventually_shellZeroWindowArithmeticAt,
      eventually_candidateLocalBroadThetaScaleArithmetic] with
      m hwindow hbroad
  have hlowLe : shellZeroExternalLow48 m ≤ m :=
    shellZeroExternalLow48_le m
  have hradius : shellZeroCenterRadius m ≤ (m : ℝ) / 60 := by
    have hmoderate := (hwindow.2.2 (m / 2) le_rfl).2.1
    unfold literalShellZeroDeviationRadius shellZeroDeviationRadius at hmoderate
    have hhalfCast : ((m / 2 : ℕ) : ℝ) ≤ (m : ℝ) / 2 := Nat.cast_div_le
    have hwidthNonneg : (0 : ℝ) ≤ shellWidth48 m := by positivity
    unfold shellZeroCenterRadius at hmoderate ⊢
    nlinarith
  have hlowLower :
      (15 / 16 : ℝ) * ((m : ℝ) - shellZeroCenterRadius m) ≤
        (shellZeroExternalLow48 m : ℕ) := by
    unfold shellZeroExternalLow48
    exact Nat.le_ceil _
  have hthresholdWidth :
      m / 2 + Nat.ceil ((m : ℝ) ^ (7 / 10 : ℝ)) ≤
        shellZeroExternalLow48 m + 1 := by
    have hhalfCast : ((m / 2 : ℕ) : ℝ) ≤ (m : ℝ) / 2 := Nat.cast_div_le
    have hreal :
        (((m / 2 + Nat.ceil ((m : ℝ) ^ (7 / 10 : ℝ)) : ℕ) : ℝ)) ≤
          ((shellZeroExternalLow48 m + 1 : ℕ) : ℝ) := by
      push_cast
      have hbroadWidth := hbroad.width
      unfold candidateLocalBroadWidth48 at hbroadWidth
      nlinarith
    exact_mod_cast hreal
  unfold sourceCandidateLazyCap48 concreteExternalThreshold48
  omega

/-- Canonical, premise-free inhabitant of the corrected full-beta product
record.  The bound is the same deterministic cutoff appearing in the early
creation event, hence it is finite and shell-independent. -/
def concreteFullBetaProductData : FullBetaSourceCorrectAllTilingProductData where
  externalThreshold := concreteExternalThreshold48
  interfaces := fun _t m _band ↦
    { totalBound := fun _shell ↦ levelCutoffTime upperTailDelta m }
  threshold_pos := eventually_concreteExternalThreshold48_pos
  capacity := eventually_concreteFullBeta_capacity

end

end Erdos1165.HLOZConcreteFullBetaProductData
