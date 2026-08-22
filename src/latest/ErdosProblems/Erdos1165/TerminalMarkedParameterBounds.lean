/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/
/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

import ErdosProblems.Erdos1165.PoissonKernelMarkedHarnack
import ErdosProblems.Erdos1165.TerminalMarkedErrorBounds

/-!
# Numerical error budget for the marked terminal kernel

This module fixes the radial cut at `s^8`, supplies an explicit potential
lower window for the literal `s^9`/`s^6` terminal annulus, and proves that
the accumulated point-hit/exit-endpoint comparison loss is at most `1/4`.
-/

open Filter Set
open scoped ENNReal Topology

namespace Erdos1165.TerminalMarkedParameterBounds

open Annulus BoundaryStoppedHarnack PotentialConvergence
open PotentialEuclideanGeometry PotentialRadialAsymptotic
open PotentialRadialGlobal RadialHarnackSpecialization
open TerminalExcursionPathwise TerminalSkeletonWords TerminalExcursionDisintegration
open TerminalParameterBounds PoissonKernelGreenPole
open PoissonKernelHarnack PoissonKernelMarkedHarnack
open TerminalMarkedErrorBounds
open AppendixLocalTime Proposition13Scales

noncomputable section

/-- Exact common lower window for the terminal point-hit Green numerator. -/
def terminalHitReferenceLower (s : ℕ) : ℝ :=
  (6 / Real.pi) * Real.log s -
    globalRadialConstant / (s : ℝ) ^ 9 -
    globalRadialConstant / ((s ^ 6 - 1 : ℕ) : ℝ) -
    literalBoundaryError (s ^ 9)

/-- Multiplicative error in the terminal entrance-to-point hit kernel. -/
def terminalHitRelativeError (s : ℕ) : ℝ :=
  literalBoundaryHitError (s ^ 9) (s ^ 6 - 1)
    (terminalHitReferenceLower s)

/-- Canonical combined marked-kernel loss, with radial cut `S=s^8`. -/
def canonicalTerminalMarkedLoss (s : ℕ) : ℝ :=
  terminalMarkedPoissonLowerError s (s ^ 8)
    (terminalHitRelativeError s)

def terminalHitLowerErrorConstant : ℝ :=
  2 * globalRadialConstant + 13000000002

def terminalHitErrorConstant : ℝ := 78000000012

theorem terminalHitLowerErrorConstant_pos :
    0 < terminalHitLowerErrorConstant := by
  unfold terminalHitLowerErrorConstant
  linarith [globalRadialConstant_pos]

theorem terminalHitErrorConstant_pos : 0 < terminalHitErrorConstant := by
  unfold terminalHitErrorConstant
  norm_num

private theorem literalBoundaryError_le_constant
    {R : ℕ} (hR : 2 ≤ R) : literalBoundaryError R ≤ 13000000002 := by
  unfold literalBoundaryError euclideanShellError
  have hdenNat : 1 ≤ R - 1 := by omega
  have hden : (1 : ℝ) ≤ (R - 1 : ℕ) := by exact_mod_cast hdenNat
  have hpos : (0 : ℝ) < (R - 1 : ℕ) := lt_of_lt_of_le zero_lt_one hden
  rw [div_le_iff₀ hpos]
  nlinarith

private theorem terminalHitReferenceError_le_constant
    (s : ℕ) (hs : 2 ≤ s) :
    globalRadialConstant / (s : ℝ) ^ 9 +
        globalRadialConstant / ((s ^ 6 - 1 : ℕ) : ℝ) +
        literalBoundaryError (s ^ 9) ≤ terminalHitLowerErrorConstant := by
  have hs1 : (1 : ℝ) ≤ s := by exact_mod_cast (show 1 ≤ s by omega)
  have hpow9 : (1 : ℝ) ≤ (s : ℝ) ^ 9 := one_le_pow₀ hs1
  have hs6 : 2 ≤ s ^ 6 := by
    have h := Nat.pow_le_pow_left hs 6
    norm_num at h ⊢
    omega
  have hden : (1 : ℝ) ≤ (s ^ 6 - 1 : ℕ) := by exact_mod_cast (show 1 ≤ s ^ 6 - 1 by omega)
  have hfirst : globalRadialConstant / (s : ℝ) ^ 9 ≤ globalRadialConstant := by
    rw [div_le_iff₀ (lt_of_lt_of_le zero_lt_one hpow9)]
    nlinarith [globalRadialConstant_pos]
  have hsecond : globalRadialConstant / ((s ^ 6 - 1 : ℕ) : ℝ) ≤
      globalRadialConstant := by
    rw [div_le_iff₀ (lt_of_lt_of_le zero_lt_one hden)]
    nlinarith [globalRadialConstant_pos]
  have hs9 : 2 ≤ s ^ 9 := by
    have h := Nat.pow_le_pow_left hs 9
    norm_num at h ⊢
    omega
  have hboundary := literalBoundaryError_le_constant hs9
  unfold terminalHitLowerErrorConstant
  linarith [globalRadialConstant_pos]

theorem eventually_terminalHitReferenceLower_ge_one :
    ∀ᶠ s : ℕ in atTop, 1 ≤ terminalHitReferenceLower s := by
  have hcoef : 0 < (3 / Real.pi : ℝ) := by positivity
  have htop : Tendsto (fun s : ℕ ↦ (3 / Real.pi) * Real.log s)
      atTop atTop :=
    Proposition13Scales.tendsto_log_nat_atTop.const_mul_atTop hcoef
  have hlarge := htop.eventually
    (eventually_ge_atTop (terminalHitLowerErrorConstant + 1))
  filter_upwards [hlarge, eventually_ge_atTop 2] with s hlarge hs
  have herr := terminalHitReferenceError_le_constant s hs
  unfold terminalHitReferenceLower
  have hlog0 : 0 ≤ Real.log s :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ s by omega))
  have hpipos := Real.pi_pos
  have hmain : (6 / Real.pi) * Real.log s =
      2 * ((3 / Real.pi) * Real.log s) := by ring
  rw [hmain]
  rw [show 2 * ((3 / Real.pi) * Real.log s) -
      globalRadialConstant / (s : ℝ) ^ 9 -
      globalRadialConstant / ((s ^ 6 - 1 : ℕ) : ℝ) -
      literalBoundaryError (s ^ 9) =
    2 * ((3 / Real.pi) * Real.log s) -
      (globalRadialConstant / (s : ℝ) ^ 9 +
       globalRadialConstant / ((s ^ 6 - 1 : ℕ) : ℝ) +
       literalBoundaryError (s ^ 9)) by ring]
  linarith [terminalHitLowerErrorConstant_pos]

private theorem literalBoundaryError_le_two_constant_div
    (s : ℕ) (hs : 2 ≤ s) :
    literalBoundaryError (s ^ 9) ≤
      26000000004 / (s : ℝ) ^ 6 := by
  have hx : (0 : ℝ) < s := by exact_mod_cast (show 0 < s by omega)
  have hx1 : (1 : ℝ) ≤ s := by exact_mod_cast (show 1 ≤ s by omega)
  have h6 : (0 : ℝ) < (s : ℝ) ^ 6 := pow_pos hx _
  have h9 : (0 : ℝ) < (s : ℝ) ^ 9 := pow_pos hx _
  have h69 : (s : ℝ) ^ 6 ≤ (s : ℝ) ^ 9 :=
    pow_le_pow_right₀ hx1 (by norm_num)
  have hs9 : 2 ≤ s ^ 9 := by
    have h := Nat.pow_le_pow_left hs 9
    norm_num at h ⊢
    omega
  have hden : (0 : ℝ) < (s ^ 9 - 1 : ℕ) := by
    exact_mod_cast (show 0 < s ^ 9 - 1 by omega)
  have hhalf : (s : ℝ) ^ 9 / 2 ≤ (s ^ 9 - 1 : ℕ) := by
    rw [Nat.cast_sub (by omega : 1 ≤ s ^ 9), Nat.cast_pow]
    norm_num
    have htwo : (2 : ℝ) ≤ (s : ℝ) ^ 9 := by exact_mod_cast hs9
    linarith
  have h9bound : literalBoundaryError (s ^ 9) ≤
      26000000004 / (s : ℝ) ^ 9 := by
    unfold literalBoundaryError euclideanShellError
    rw [div_le_iff₀ hden]
    calc
      (13000000002 : ℝ) =
          (26000000004 / (s : ℝ) ^ 9) * ((s : ℝ) ^ 9 / 2) := by
        field_simp
        norm_num
      _ ≤ (26000000004 / (s : ℝ) ^ 9) * (s ^ 9 - 1 : ℕ) := by
        gcongr
  exact h9bound.trans (div_le_div_of_nonneg_left (by norm_num) h6 h69)

private theorem terminalInnerShellError_le_two_constant_div
    (s : ℕ) (hs : 2 ≤ s) :
    euclideanShellError (s ^ 6 - 1) ≤
      26000000004 / (s : ℝ) ^ 6 := by
  have hx : (0 : ℝ) < s := by exact_mod_cast (show 0 < s by omega)
  have h6 : (0 : ℝ) < (s : ℝ) ^ 6 := pow_pos hx _
  have hs6 : 2 ≤ s ^ 6 := by
    have h := Nat.pow_le_pow_left hs 6
    norm_num at h ⊢
    omega
  have hden : (0 : ℝ) < (s ^ 6 - 1 : ℕ) := by
    exact_mod_cast (show 0 < s ^ 6 - 1 by omega)
  have hhalf : (s : ℝ) ^ 6 / 2 ≤ (s ^ 6 - 1 : ℕ) := by
    rw [Nat.cast_sub (by omega : 1 ≤ s ^ 6), Nat.cast_pow]
    norm_num
    have htwo : (2 : ℝ) ≤ (s : ℝ) ^ 6 := by exact_mod_cast hs6
    linarith
  unfold euclideanShellError
  rw [div_le_iff₀ hden]
  calc
    (13000000002 : ℝ) =
        (26000000004 / (s : ℝ) ^ 6) * ((s : ℝ) ^ 6 / 2) := by
      field_simp
      norm_num
    _ ≤ (26000000004 / (s : ℝ) ^ 6) * (s ^ 6 - 1 : ℕ) := by
      gcongr

theorem eventually_terminalHitRelativeError_le_rate :
    ∀ᶠ s : ℕ in atTop,
      terminalHitRelativeError s ≤ terminalHitErrorConstant / (s : ℝ) ^ 6 := by
  filter_upwards [eventually_terminalHitReferenceLower_ge_one,
    eventually_ge_atTop 2] with s hlower hs
  have hboundary := literalBoundaryError_le_two_constant_div s hs
  have hinner := terminalInnerShellError_le_two_constant_div s hs
  have hden : 0 < terminalHitReferenceLower s := zero_lt_one.trans_le hlower
  unfold terminalHitRelativeError literalBoundaryHitError
  apply (div_le_iff₀ hden).2
  have hspos : (0 : ℝ) < s := by exact_mod_cast (show 0 < s by omega)
  have hright0 : 0 ≤ terminalHitErrorConstant / (s : ℝ) ^ 6 :=
    div_nonneg terminalHitErrorConstant_pos.le (pow_pos hspos _).le
  have hmul : terminalHitErrorConstant / (s : ℝ) ^ 6 ≤
      terminalHitErrorConstant / (s : ℝ) ^ 6 * terminalHitReferenceLower s := by
    nlinarith
  have hnumerator : 2 * literalBoundaryError (s ^ 9) +
      euclideanShellError (s ^ 6 - 1) ≤
        terminalHitErrorConstant / (s : ℝ) ^ 6 := by
    calc
      2 * literalBoundaryError (s ^ 9) +
          euclideanShellError (s ^ 6 - 1) ≤
        2 * (26000000004 / (s : ℝ) ^ 6) +
          26000000004 / (s : ℝ) ^ 6 := by linarith
      _ = terminalHitErrorConstant / (s : ℝ) ^ 6 := by
        unfold terminalHitErrorConstant
        ring
  exact hnumerator.trans hmul

theorem eventually_terminalHitRelativeError_le_budget :
    ∀ᶠ s : ℕ in atTop,
      terminalHitRelativeError s ≤ 1 / (24 * (s : ℝ) ^ 2) := by
  have hlarge := tendsto_natCast_atTop_atTop.eventually
    (eventually_ge_atTop (24 * terminalHitErrorConstant))
  filter_upwards [eventually_terminalHitRelativeError_le_rate,
    hlarge, eventually_ge_atTop 2] with s hrate hlarge hs
  have hx : (0 : ℝ) < s := by exact_mod_cast (show 0 < s by omega)
  have hx1 : (1 : ℝ) ≤ s := by exact_mod_cast (show 1 ≤ s by omega)
  have hx2 : (0 : ℝ) < (s : ℝ) ^ 2 := pow_pos hx _
  have hx6 : (0 : ℝ) < (s : ℝ) ^ 6 := pow_pos hx _
  have hx4 : (s : ℝ) ≤ (s : ℝ) ^ 4 := by
    simpa using (pow_le_pow_right₀ hx1 (show 1 ≤ 4 by omega))
  have hC : 24 * terminalHitErrorConstant ≤ (s : ℝ) ^ 4 :=
    hlarge.trans hx4
  calc
    terminalHitRelativeError s ≤ terminalHitErrorConstant / (s : ℝ) ^ 6 := hrate
    _ ≤ 1 / (24 * (s : ℝ) ^ 2) := by
      rw [div_le_div_iff₀ hx6 (by positivity : 0 < 24 * (s : ℝ) ^ 2)]
      have hsplit : (s : ℝ) ^ 6 = (s : ℝ) ^ 4 * (s : ℝ) ^ 2 := by ring
      rw [hsplit]
      nlinarith

/-! ## The canonical `s^8` Poisson cut -/

def terminalExitErrorConstant : ℝ :=
  16 * (2 * globalRadialConstant + 3)

theorem terminalExitErrorConstant_pos : 0 < terminalExitErrorConstant := by
  unfold terminalExitErrorConstant
  linarith [globalRadialConstant_pos]

theorem terminalCut_inner_separated
    (s : ℕ) (hs : 2 ≤ s) : s ^ 6 + 2 ≤ s ^ 8 := by
  have hs2 : 2 ≤ s ^ 6 := by
    have h := Nat.pow_le_pow_left hs 6
    norm_num at h ⊢
    omega
  have hsSq : 2 ≤ s ^ 2 := by
    have h := Nat.pow_le_pow_left hs 2
    norm_num at h ⊢
    omega
  calc
    s ^ 6 + 2 ≤ s ^ 6 + s ^ 6 := by omega
    _ = 2 * s ^ 6 := by ring
    _ ≤ s ^ 2 * s ^ 6 := Nat.mul_le_mul_right _ hsSq
    _ = s ^ 8 := by ring

theorem terminalCut_scale_separated
    (s : ℕ) (hs : 2 ≤ s) : s ^ 8 + 2 * s ^ 6 + 2 ≤ s ^ 9 := by
  have hs6 : 2 ≤ s ^ 6 := by
    have h := Nat.pow_le_pow_left hs 6
    norm_num at h ⊢
    omega
  have hs2 : 4 ≤ s ^ 2 := Nat.pow_le_pow_left hs 2
  have hcoef : s ^ 2 + 3 ≤ s ^ 3 := by
    calc
      s ^ 2 + 3 ≤ 2 * s ^ 2 := by omega
      _ ≤ s * s ^ 2 := Nat.mul_le_mul_right _ hs
      _ = s ^ 3 := by ring
  calc
    s ^ 8 + 2 * s ^ 6 + 2 ≤ s ^ 8 + 3 * s ^ 6 := by omega
    _ = s ^ 6 * (s ^ 2 + 3) := by ring
    _ ≤ s ^ 6 * s ^ 3 := Nat.mul_le_mul_left _ hcoef
    _ = s ^ 9 := by ring

theorem terminalCut_outer_separated
    (s : ℕ) (hs : 2 ≤ s) : s ^ 8 + 4 ≤ s ^ 9 := by
  have hs8 : 4 ≤ s ^ 8 := by
    have h := Nat.pow_le_pow_left hs 8
    norm_num at h ⊢
    omega
  calc
    s ^ 8 + 4 ≤ 2 * s ^ 8 := by omega
    _ ≤ s * s ^ 8 := Nat.mul_le_mul_right _ hs
    _ = s ^ 9 := by ring

private theorem terminalCut_logRatio_lower
    (s : ℕ) (hs : 4 ≤ s) :
    Real.log (s : ℝ) - Real.log 4 ≤
      Real.log (outerPoleGap (s ^ 9) (s ^ 6) /
        ((s ^ 8 : ℕ) + (s ^ 6 : ℕ) + 2)) := by
  let x : ℝ := s
  let R : ℝ := (s : ℝ) ^ 9
  let S : ℝ := (s : ℝ) ^ 8
  let r : ℝ := (s : ℝ) ^ 6
  have hx : 0 < x := by dsimp [x]; exact_mod_cast (show 0 < s by omega)
  have hx4 : (4 : ℝ) ≤ x := by dsimp [x]; exact_mod_cast hs
  have hR : 0 < R := by dsimp [R]; positivity
  have hS : 0 < S := by dsimp [S]; positivity
  have hr : 0 < r := by dsimp [r]; positivity
  have hpow98 : R = x * S := by dsimp [R, S, x]; ring
  have hpow86 : S = x ^ 2 * r := by dsimp [S, r, x]; ring
  have hrS : r ≤ S := by
    rw [hpow86]
    have hxSq : (1 : ℝ) ≤ x ^ 2 := one_le_pow₀ (by linarith)
    nlinarith
  have hSfour : (4 : ℝ) ≤ S := by
    dsimp [S, x]
    have hnat : 4 ≤ s ^ 8 := by
      have h := Nat.pow_le_pow_left (show 2 ≤ s by omega) 8
      norm_num at h ⊢
      omega
    exact_mod_cast hnat
  have hrTwo : r + 2 ≤ S := by
    dsimp [r, S]
    exact_mod_cast terminalCut_inner_separated s (by omega)
  have hdenUpper : S + r + 2 ≤ 2 * S := by linarith
  have hRquarter : 4 * S ≤ R := by rw [hpow98]; nlinarith
  have hrQuarter : r ≤ R / 4 := hrS.trans (by nlinarith [hS.le])
  have hnumLower : R / 2 ≤ R - r := by
    have : r ≤ R / 2 := by nlinarith [hrQuarter, hR.le]
    linarith
  have hdenPos : 0 < S + r + 2 := by positivity
  have hnumPos : 0 < R - r := by linarith
  have hratio : x / 4 ≤ (R - r) / (S + r + 2) := by
    apply (le_div_iff₀ hdenPos).2
    calc
      x / 4 * (S + r + 2) ≤ x / 4 * (2 * S) := by gcongr
      _ = R / 2 := by rw [hpow98]; ring
      _ ≤ R - r := hnumLower
  have hxdiv : 0 < x / 4 := div_pos hx (by norm_num)
  have hlog := Real.log_le_log hxdiv hratio
  have hlogDiv : Real.log (x / 4) = Real.log x - Real.log 4 := by
    rw [Real.log_div hx.ne' (by norm_num : (4 : ℝ) ≠ 0)]
  have hcastGap : outerPoleGap (s ^ 9) (s ^ 6) = R - r := by
    unfold outerPoleGap
    dsimp [R, r]
    norm_num
  have hcastS : ((s ^ 8 : ℕ) : ℝ) = S := by simp [S]
  have hcastr : ((s ^ 6 : ℕ) : ℝ) = r := by simp [r]
  rw [hlogDiv] at hlog
  rw [hcastGap]
  rw [hcastS, hcastr]
  change Real.log (s : ℝ) - Real.log 4 ≤
    Real.log ((R - r) / (S + r + 2))
  simpa [x] using hlog

private theorem terminalGreenPoleLower_error_le_constant
    (s : ℕ) (hs : 2 ≤ s) :
    globalRadialConstant / outerPoleGap (s ^ 9) (s ^ 6) +
        globalRadialConstant / intermediatePoleGap (s ^ 8) (s ^ 6) +
        boundaryPoleError (s ^ 9) (s ^ 6) ≤
      4 * globalRadialConstant + 3 := by
  have hscale := terminalCut_scale_separated s hs
  have hS := terminalCut_inner_separated s hs
  have houterPos := outerPoleGap_pos (show s ^ 6 + 1 ≤ s ^ 9 by omega)
  have hinterPos := intermediatePoleGap_pos hS
  have hboundaryPos := boundaryPoleGap_pos (show s ^ 6 + 2 ≤ s ^ 9 by omega)
  have houterOne : (1 : ℝ) ≤ outerPoleGap (s ^ 9) (s ^ 6) := by
    unfold outerPoleGap
    have hcast : (((s ^ 6 + 1 : ℕ) : ℝ)) ≤ (s ^ 9 : ℕ) := by
      exact_mod_cast (show s ^ 6 + 1 ≤ s ^ 9 by omega)
    push_cast at hcast
    norm_num [Nat.cast_pow] at hcast ⊢
    linarith
  have hinterOne : (1 : ℝ) ≤ intermediatePoleGap (s ^ 8) (s ^ 6) := by
    unfold intermediatePoleGap
    have hcast : (((s ^ 6 + 2 : ℕ) : ℝ)) ≤ (s ^ 8 : ℕ) := by
      exact_mod_cast hS
    push_cast at hcast
    norm_num [Nat.cast_pow] at hcast ⊢
    linarith
  have hboundaryDenom : ((s ^ 6 : ℕ) : ℝ) + 1 ≤
      boundaryPoleGap (s ^ 9) (s ^ 6) := by
    unfold boundaryPoleGap
    have hcast : (((2 * s ^ 6 + 2 : ℕ) : ℝ)) ≤ (s ^ 9 : ℕ) := by
      exact_mod_cast (show 2 * s ^ 6 + 2 ≤ s ^ 9 by omega)
    push_cast at hcast
    norm_num [Nat.cast_pow] at hcast ⊢
    linarith
  have houterErr : globalRadialConstant /
      outerPoleGap (s ^ 9) (s ^ 6) ≤ globalRadialConstant := by
    rw [div_le_iff₀ houterPos]
    nlinarith [globalRadialConstant_pos]
  have hinterErr : globalRadialConstant /
      intermediatePoleGap (s ^ 8) (s ^ 6) ≤ globalRadialConstant := by
    rw [div_le_iff₀ hinterPos]
    nlinarith [globalRadialConstant_pos]
  have hboundaryErr : boundaryPoleError (s ^ 9) (s ^ 6) ≤
      2 * globalRadialConstant + 3 := by
    unfold boundaryPoleError
    apply (div_le_iff₀ hboundaryPos).2
    have hr0 : (0 : ℝ) ≤ s ^ 6 := by positivity
    have hK : 0 ≤ 2 * globalRadialConstant + 3 := by
      linarith [globalRadialConstant_pos]
    calc
      2 * globalRadialConstant + (2 * s ^ 6 + 1 : ℕ) ≤
          (2 * globalRadialConstant + 3) * ((s ^ 6 : ℕ) + 1) := by
        push_cast
        nlinarith [mul_nonneg globalRadialConstant_pos.le hr0]
      _ ≤ (2 * globalRadialConstant + 3) *
          boundaryPoleGap (s ^ 9) (s ^ 6) :=
        mul_le_mul_of_nonneg_left hboundaryDenom hK
  linarith

theorem eventually_terminalGreenPoleLower_ge_one :
    ∀ᶠ s : ℕ in atTop,
      1 ≤ greenPoleLower (s ^ 9) (s ^ 8) (s ^ 6) := by
  have hcoef : 0 < (2 / Real.pi : ℝ) := by positivity
  have htop : Tendsto (fun s : ℕ ↦ (2 / Real.pi) *
      (Real.log s - Real.log 4)) atTop atTop := by
    have hbase := Proposition13Scales.tendsto_log_nat_atTop.const_mul_atTop hcoef
    have hshift := tendsto_atTop_add_const_right atTop
      (-((2 / Real.pi) * Real.log 4)) hbase
    apply hshift.congr'
    filter_upwards [] with s
    ring
  have hlarge := htop.eventually
    (eventually_ge_atTop (4 * globalRadialConstant + 4))
  filter_upwards [hlarge, eventually_ge_atTop 4] with s hlarge hs
  have hratio := terminalCut_logRatio_lower s hs
  have herr := terminalGreenPoleLower_error_le_constant s (by omega)
  unfold greenPoleLower
  have hmul := mul_le_mul_of_nonneg_left hratio (by positivity : 0 ≤ 2 / Real.pi)
  linarith

private theorem terminalCut_inner_double
    (s : ℕ) (hs : 2 ≤ s) : 2 * (s ^ 6 + 1) ≤ s ^ 8 := by
  have hs6 : 2 ≤ s ^ 6 := by
    have h := Nat.pow_le_pow_left hs 6
    norm_num at h ⊢
    omega
  have hs2 : 4 ≤ s ^ 2 := Nat.pow_le_pow_left hs 2
  calc
    2 * (s ^ 6 + 1) ≤ 4 * s ^ 6 := by omega
    _ ≤ s ^ 2 * s ^ 6 := Nat.mul_le_mul_right _ hs2
    _ = s ^ 8 := by ring

/-- At the terminal cut `s^8`, the full moving-pole error is uniformly
`O(s⁻²)` with the explicit constant used by the marked-kernel budget. -/
theorem terminalGreenPoleAdditiveError_le_rate
    (s : ℕ) (hs : 2 ≤ s) :
    greenPoleAdditiveError (s ^ 9) (s ^ 8) (s ^ 6) ≤
      terminalExitErrorConstant / (s : ℝ) ^ 2 := by
  let x : ℝ := s
  let C : ℝ := globalRadialConstant
  let K : ℝ := 2 * C + 3
  have hx : 0 < x := by dsimp [x]; exact_mod_cast (show 0 < s by omega)
  have hx1 : 1 ≤ x := by dsimp [x]; exact_mod_cast (show 1 ≤ s by omega)
  have hC : 0 ≤ C := by dsimp [C]; exact globalRadialConstant_pos.le
  have hK : 0 ≤ K := by dsimp [K]; linarith
  have hbPos := boundaryPoleGap_pos
    (show s ^ 6 + 2 ≤ s ^ 9 by
      have houter := terminalCut_outer_separated s hs
      have hinner := terminalCut_inner_separated s hs
      omega)
  have hoPos := outerPoleGap_pos
    (show s ^ 6 + 1 ≤ s ^ 9 by
      have hscale := terminalCut_scale_separated s hs
      omega)
  have hiPos := intermediatePoleGap_pos
    (terminalCut_inner_separated s hs)
  have hbDen : x ^ 9 / 2 ≤ boundaryPoleGap (s ^ 9) (s ^ 6) := by
    unfold boundaryPoleGap
    have hcast : (2 : ℝ) * ((s : ℝ) ^ 6 + 1) ≤ (s : ℝ) ^ 9 := by
      exact_mod_cast (show 2 * (s ^ 6 + 1) ≤ s ^ 9 by
        have houter := terminalCut_outer_separated s hs
        have hinner := terminalCut_inner_double s hs
        omega)
    dsimp [x]
    norm_num [Nat.cast_pow] at hcast ⊢
    linarith
  have hoDen : x ^ 9 / 2 ≤ outerPoleGap (s ^ 9) (s ^ 6) := by
    unfold outerPoleGap
    have hcast : (2 : ℝ) * (s : ℝ) ^ 6 ≤ (s : ℝ) ^ 9 := by
      exact_mod_cast (show 2 * s ^ 6 ≤ s ^ 9 by
        have := terminalCut_scale_separated s hs
        omega)
    dsimp [x]
    norm_num [Nat.cast_pow] at hcast ⊢
    linarith
  have hiDen : x ^ 8 / 2 ≤ intermediatePoleGap (s ^ 8) (s ^ 6) := by
    unfold intermediatePoleGap
    have hcast : (2 : ℝ) * ((s : ℝ) ^ 6 + 1) ≤ (s : ℝ) ^ 8 := by
      exact_mod_cast terminalCut_inner_double s hs
    dsimp [x]
    norm_num [Nat.cast_pow] at hcast ⊢
    linarith
  have hboundaryNumerator :
      2 * C + (2 * s ^ 6 + 1 : ℕ) ≤ 2 * K * x ^ 6 := by
    norm_num only [Nat.cast_add, Nat.cast_mul, Nat.cast_pow,
      Nat.cast_ofNat, Nat.cast_one]
    dsimp [K, x]
    have hs6 : (1 : ℝ) ≤ (s : ℝ) ^ 6 := one_le_pow₀ hx1
    nlinarith [mul_nonneg hC (sub_nonneg.mpr hs6)]
  have houterNumerator :
      2 * C + (2 * s ^ 6 : ℕ) ≤ 2 * K * x ^ 6 := by
    norm_num only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
    dsimp [K, x]
    have hs6 : (1 : ℝ) ≤ (s : ℝ) ^ 6 := one_le_pow₀ hx1
    nlinarith [mul_nonneg hC (zero_le_one.trans hs6)]
  have hboundary : boundaryPoleError (s ^ 9) (s ^ 6) ≤
      4 * K / x ^ 3 := by
    unfold boundaryPoleError
    apply (div_le_iff₀ hbPos).2
    calc
      _ ≤ 2 * K * x ^ 6 := by simpa [C] using hboundaryNumerator
      _ = (4 * K / x ^ 3) * (x ^ 9 / 2) := by
        field_simp
        ring
      _ ≤ (4 * K / x ^ 3) * boundaryPoleGap (s ^ 9) (s ^ 6) := by
        exact mul_le_mul_of_nonneg_left hbDen (by positivity)
  have houter : outerPoleError (s ^ 9) (s ^ 6) ≤
      4 * K / x ^ 3 := by
    unfold outerPoleError
    apply (div_le_iff₀ hoPos).2
    calc
      _ ≤ 2 * K * x ^ 6 := by simpa [C] using houterNumerator
      _ = (4 * K / x ^ 3) * (x ^ 9 / 2) := by
        field_simp
        ring
      _ ≤ (4 * K / x ^ 3) * outerPoleGap (s ^ 9) (s ^ 6) := by
        exact mul_le_mul_of_nonneg_left hoDen (by positivity)
  have hintermediate : intermediatePoleError (s ^ 8) (s ^ 6) ≤
      4 * K / x ^ 2 := by
    unfold intermediatePoleError
    apply (div_le_iff₀ hiPos).2
    calc
      _ ≤ 2 * K * x ^ 6 := by simpa [C] using houterNumerator
      _ = (4 * K / x ^ 2) * (x ^ 8 / 2) := by
        field_simp
        ring
      _ ≤ (4 * K / x ^ 2) * intermediatePoleGap (s ^ 8) (s ^ 6) := by
        exact mul_le_mul_of_nonneg_left hiDen (by positivity)
  have hpow : x ^ 2 ≤ x ^ 3 := by nlinarith [sq_nonneg x]
  have hrate : 4 * K / x ^ 3 ≤ 4 * K / x ^ 2 := by
    exact div_le_div_of_nonneg_left (by positivity) (by positivity) hpow
  unfold greenPoleAdditiveError terminalExitErrorConstant
  dsimp only [K, C, x] at *
  calc
    2 * boundaryPoleError (s ^ 9) (s ^ 6) +
          outerPoleError (s ^ 9) (s ^ 6) +
          intermediatePoleError (s ^ 8) (s ^ 6) ≤
        2 * (4 * (2 * globalRadialConstant + 3) / (s : ℝ) ^ 3) +
          4 * (2 * globalRadialConstant + 3) / (s : ℝ) ^ 3 +
          4 * (2 * globalRadialConstant + 3) / (s : ℝ) ^ 2 := by linarith
    _ = 3 * (4 * (2 * globalRadialConstant + 3) / (s : ℝ) ^ 3) +
          4 * (2 * globalRadialConstant + 3) / (s : ℝ) ^ 2 := by ring
    _ ≤ 3 * (4 * (2 * globalRadialConstant + 3) / (s : ℝ) ^ 2) +
          4 * (2 * globalRadialConstant + 3) / (s : ℝ) ^ 2 := by
      gcongr
    _ = 16 * (2 * globalRadialConstant + 3) / (s : ℝ) ^ 2 := by ring

/-- The exact Green lower window at radii `s^9,s^8,s^6` tends to infinity.
This threshold form is convenient for dividing the additive Poisson error. -/
theorem eventually_terminalGreenPoleLower_ge (B : ℝ) :
    ∀ᶠ s : ℕ in atTop,
      B ≤ greenPoleLower (s ^ 9) (s ^ 8) (s ^ 6) := by
  have hcoef : 0 < (2 / Real.pi : ℝ) := by positivity
  have htop : Tendsto (fun s : ℕ ↦ (2 / Real.pi) *
      (Real.log s - Real.log 4)) atTop atTop := by
    have hbase := Proposition13Scales.tendsto_log_nat_atTop.const_mul_atTop hcoef
    have hshift := tendsto_atTop_add_const_right atTop
      (-((2 / Real.pi) * Real.log 4)) hbase
    apply hshift.congr'
    filter_upwards [] with s
    ring
  have hlarge := htop.eventually
    (eventually_ge_atTop (B + (4 * globalRadialConstant + 3)))
  filter_upwards [hlarge, eventually_ge_atTop 4] with s hlarge hs
  have hratio := terminalCut_logRatio_lower s hs
  have herr := terminalGreenPoleLower_error_le_constant s (by omega)
  unfold greenPoleLower
  have hmul := mul_le_mul_of_nonneg_left hratio (by positivity : 0 ≤ 2 / Real.pi)
  linarith

/-- The actual relative Poisson exit-endpoint error is eventually below the
`1/(24s²)` budget required by the marked terminal product estimate. -/
theorem eventually_terminalPoissonExitError_le_budget :
    ∀ᶠ s : ℕ in atTop,
      terminalPoissonExitError s (s ^ 8) ≤
        1 / (24 * (s : ℝ) ^ 2) := by
  filter_upwards [eventually_terminalGreenPoleLower_ge
      (24 * terminalExitErrorConstant), eventually_ge_atTop 4]
      with s hlower hs
  have hrate := terminalGreenPoleAdditiveError_le_rate s (by omega)
  have hpos : 0 < greenPoleLower (s ^ 9) (s ^ 8) (s ^ 6) :=
    terminalExitErrorConstant_pos.trans_le
      ((show terminalExitErrorConstant ≤ 24 * terminalExitErrorConstant by
        nlinarith [terminalExitErrorConstant_pos]).trans hlower)
  have hx : (0 : ℝ) < s := by exact_mod_cast (show 0 < s by omega)
  have ha0 : 0 ≤ 1 / (24 * (s : ℝ) ^ 2) := by positivity
  unfold terminalPoissonExitError poissonKernelRelativeError
  apply (div_le_iff₀ hpos).2
  calc
    greenPoleAdditiveError (s ^ 9) (s ^ 8) (s ^ 6) ≤
        terminalExitErrorConstant / (s : ℝ) ^ 2 := hrate
    _ = (1 / (24 * (s : ℝ) ^ 2)) *
        (24 * terminalExitErrorConstant) := by
      field_simp
    _ ≤ (1 / (24 * (s : ℝ) ^ 2)) *
        greenPoleLower (s ^ 9) (s ^ 8) (s ^ 6) :=
      mul_le_mul_of_nonneg_left hlower ha0

/-- The explicit hit lower window is valid for every lattice point on the
literal terminal inner boundary, not only for the canonical axis entrance. -/
theorem terminalHitReferenceLower_le_boundaryReference
    (s : ℕ) (hs : 2 ≤ s) {z : Point}
    (hz : z ∈ ThickPoint.discBoundary 0 ((s ^ 6 : ℕ) : ℝ)) :
    terminalHitReferenceLower s ≤
      planarPotentialKernel (axisPoint (s ^ 9)) -
        planarPotentialKernel z - literalBoundaryError (s ^ 9) := by
  have hs6 : 1 ≤ s ^ 6 := Nat.one_le_pow 6 s (by omega)
  have hs6m1 : 1 ≤ s ^ 6 - 1 := by
    have hpow := Nat.pow_le_pow_left hs 6
    norm_num at hpow ⊢
    omega
  have hzBounds := discBoundary_zero_euclideanRadius_bounds_nat hs6 hz
  have hzPos : 0 < euclideanRadius z := by
    have hcast : (0 : ℝ) < (s ^ 6 - 1 : ℕ) := by exact_mod_cast hs6m1
    exact hcast.trans hzBounds.1
  have hzNe : z ≠ 0 := (euclideanRadius_pos_iff z).mp hzPos
  have haxisNe : axisPoint (s ^ 9) ≠ 0 := by
    intro h
    have hfirst := congrArg Prod.fst h
    simp [axisPoint] at hfirst
    have : 0 < s ^ 9 := pow_pos (by omega) 9
    omega
  have houter :=
    abs_planarPotentialKernel_sub_log_euclideanRadius_sub_cPotential_le_global
      haxisNe
  have hinner :=
    abs_planarPotentialKernel_sub_log_euclideanRadius_sub_cPotential_le_global hzNe
  rw [euclideanRadius_axisPoint, Nat.cast_pow, Real.log_pow] at houter
  norm_num at houter
  have hinnerDen : (0 : ℝ) < (s ^ 6 - 1 : ℕ) := by exact_mod_cast hs6m1
  have hinnerErr : globalRadialConstant / euclideanRadius z ≤
      globalRadialConstant / ((s ^ 6 - 1 : ℕ) : ℝ) :=
    div_le_div_of_nonneg_left globalRadialConstant_pos.le hinnerDen
      hzBounds.1.le
  have hlogInner : Real.log (euclideanRadius z) ≤ 6 * Real.log s := by
    have hlog := Real.log_le_log hzPos hzBounds.2
    rw [Nat.cast_pow, Real.log_pow] at hlog
    norm_num at hlog
    exact hlog
  rw [abs_le] at houter hinner
  have houterLower :
      (18 / Real.pi) * Real.log s + cPotential -
          globalRadialConstant / (s : ℝ) ^ 9 ≤
        planarPotentialKernel (axisPoint (s ^ 9)) := by
    have := houter.1
    ring_nf at this ⊢
    linarith
  have hinnerMain :
      (2 / Real.pi) * Real.log (euclideanRadius z) ≤
        (12 / Real.pi) * Real.log s := by
    have := mul_le_mul_of_nonneg_left hlogInner
      (by positivity : 0 ≤ 2 / Real.pi)
    ring_nf at this ⊢
    exact this
  have hinnerUpper : planarPotentialKernel z ≤
      (12 / Real.pi) * Real.log s + cPotential +
        globalRadialConstant / ((s ^ 6 - 1 : ℕ) : ℝ) := by
    linarith [hinner.2]
  unfold terminalHitReferenceLower
  calc
    _ = ((18 / Real.pi) * Real.log s + cPotential -
          globalRadialConstant / (s : ℝ) ^ 9) -
        ((12 / Real.pi) * Real.log s + cPotential +
          globalRadialConstant / ((s ^ 6 - 1 : ℕ) : ℝ)) -
        literalBoundaryError (s ^ 9) := by ring
    _ ≤ planarPotentialKernel (axisPoint (s ^ 9)) -
          planarPotentialKernel z - literalBoundaryError (s ^ 9) := by
      linarith

/-- Uniform literal hit comparison for all packaged terminal entrances,
normalized by the actual canonical hit probability. -/
theorem terminalBoundaryStoppedHit_two_sided
    (s : ℕ) (hs : 2 ≤ s) (center : Point)
    (hlower : 0 < terminalHitReferenceLower s)
    (u : TerminalEntrance s center) :
    (1 - terminalHitRelativeError s) * terminalHitProbability s ≤
        boundaryStoppedHitKernel (terminalOuterBoundary s center) center u.1 ∧
      boundaryStoppedHitKernel (terminalOuterBoundary s center) center u.1 ≤
        (1 + terminalHitRelativeError s) * terminalHitProbability s := by
  have houterEq : terminalOuterBoundary s center =
      ThickPoint.discBoundary center ((s ^ 9 : ℕ) : ℝ) := by
    simp [terminalOuterBoundary, ThickPoint.scaleRadius_of_le,
      ThickPoint.regularRadius_self]
  have hinnerEq : terminalInnerBoundary s center =
      ThickPoint.discBoundary center ((s ^ 6 : ℕ) : ℝ) := by
    simp [terminalInnerBoundary, ThickPoint.scaleRadius_succ_self]
  have hu0 : u.1 - center ∈
      ThickPoint.discBoundary 0 ((s ^ 6 : ℕ) : ℝ) := by
    apply (mem_discBoundary_translate center ((s ^ 6 : ℕ) : ℝ) u.1).mp
    simpa only [← hinnerEq] using u.2
  have hR : 5 ≤ s ^ 9 := by
    have hpow := Nat.pow_le_pow_left hs 9
    norm_num at hpow ⊢
    omega
  have hsep : s ^ 6 - 1 + 2 ≤ s ^ 9 := by
    have hpow3 := Nat.pow_le_pow_left hs 3
    have hpow6 : 0 < s ^ 6 := pow_pos (by omega) 6
    calc
      s ^ 6 - 1 + 2 = s ^ 6 + 1 := by omega
      _ ≤ 2 * s ^ 6 := by omega
      _ ≤ s ^ 3 * s ^ 6 := Nat.mul_le_mul_right _ (by omega)
      _ = s ^ 9 := by ring
  have hrho : 4 ≤ s ^ 6 - 1 := by
    have hpow := Nat.pow_le_pow_left hs 6
    norm_num at hpow ⊢
    omega
  have hxInside : axisPoint (s ^ 6) ∈ boundaryInterior (s ^ 9) :=
    axisPoint_mem_boundaryInterior_power s hs
  have hyInside : u.1 - center ∈ boundaryInterior (s ^ 9) := by
    have hs6 : 1 ≤ s ^ 6 := Nat.one_le_pow 6 s (by omega)
    apply centeredInnerBoundary_shift_mem_boundaryInterior hsep
    have hcast : (((s ^ 6 - 1 : ℕ) : ℝ) + 1) = (s ^ 6 : ℕ) := by
      rw [Nat.cast_sub hs6]
      norm_num
    rw [hcast]
    simpa only [← hinnerEq] using u.2
  have huBounds := discBoundary_zero_euclideanRadius_bounds_nat
    (Nat.one_le_pow 6 s (by omega)) hu0
  have hxRadius : ((s ^ 6 - 1 : ℕ) : ℝ) ≤
      euclideanRadius (axisPoint (s ^ 6)) := by
    rw [euclideanRadius_axisPoint]
    exact_mod_cast (Nat.sub_le (s ^ 6) 1)
  have hyRadius : ((s ^ 6 - 1 : ℕ) : ℝ) ≤
      euclideanRadius (u.1 - center) := huBounds.1.le
  have hgap : |euclideanRadius (axisPoint (s ^ 6)) -
      euclideanRadius (u.1 - center)| ≤ 1 := by
    rw [euclideanRadius_axisPoint, abs_le]
    have hs6 : 1 ≤ s ^ 6 := Nat.one_le_pow 6 s (by omega)
    have hcast : (((s ^ 6 - 1 : ℕ) : ℝ) + 1) = (s ^ 6 : ℕ) := by
      rw [Nat.cast_sub hs6]
      norm_num
    constructor <;> linarith
  have hq : axisPoint (s ^ 9) ∈
      ThickPoint.discBoundary 0 ((s ^ 9 : ℕ) : ℝ) :=
    axisPoint_mem_discBoundary (s ^ 9)
  have href := terminalHitReferenceLower_le_boundaryReference s hs
    (axisPoint_mem_discBoundary (s ^ 6))
  have hcomparison := boundaryStoppedHit_compare_of_euclideanShells
    (s ^ 9) (s ^ 6 - 1) hR hq hxInside hyInside hrho hxRadius hyRadius
    hgap hlower href
  have hyKernel :
      boundaryStoppedHitKernel
          (ThickPoint.discBoundary 0 ((s ^ 9 : ℕ) : ℝ)) 0 (u.1 - center) =
        boundaryStoppedHitKernel (terminalOuterBoundary s center) center u.1 := by
    rw [houterEq]
    exact (boundaryStoppedHitKernel_centered_eq_zero (s ^ 9) center u.1).symm
  rw [hyKernel] at hcomparison
  simpa [terminalHitRelativeError, literalBoundaryHitError,
    terminalHitProbability, literalHitProbability] using hcomparison

theorem eventually_terminalHitRelativeError_nonneg :
    ∀ᶠ s : ℕ in atTop, 0 ≤ terminalHitRelativeError s := by
  filter_upwards [eventually_terminalHitReferenceLower_ge_one]
      with s hlower
  unfold terminalHitRelativeError literalBoundaryHitError
  exact div_nonneg (add_nonneg
    (mul_nonneg (by norm_num) (literalBoundaryError_nonneg _))
    (euclideanShellError_nonneg _)) (by linarith)

theorem eventually_terminalPoissonExitError_nonneg :
    ∀ᶠ s : ℕ in atTop, 0 ≤ terminalPoissonExitError s (s ^ 8) := by
  filter_upwards [eventually_terminalGreenPoleLower_ge_one,
    eventually_ge_atTop 4] with s hlower hs
  unfold terminalPoissonExitError
  exact poissonKernelRelativeError_nonneg
    (terminalCut_inner_separated s (by omega))
    (by
      have hscale := terminalCut_scale_separated s (by omega)
      omega)
    (by linarith)

private theorem markedPoissonUpperError_le_three_mul
    {q hitError exitError a : ℝ}
    (hq0 : 0 ≤ q) (hqHalf : q ≤ 1 / 2)
    (hhit0 : 0 ≤ hitError) (hexit0 : 0 ≤ exitError)
    (hhit : hitError ≤ a) (hexit : exitError ≤ a)
    (ha1 : a ≤ 1) :
    markedPoissonUpperError q hitError exitError ≤ 3 * a := by
  have ha0 : 0 ≤ a := hhit0.trans hhit
  have hhit1 : hitError ≤ 1 := hhit.trans ha1
  have hexit1 : exitError ≤ 1 := hexit.trans ha1
  have hproductA : hitError * exitError ≤ a := by
    calc
      hitError * exitError ≤ hitError * 1 :=
        mul_le_mul_of_nonneg_left hexit1 hhit0
      _ = hitError := mul_one _
      _ ≤ a := hhit
  have hqDenom : 0 < 1 - q := by linarith
  have hodds0 : 0 ≤ q / (1 - q) := div_nonneg hq0 hqDenom.le
  have hodds1 : q / (1 - q) ≤ 1 := by
    rw [div_le_one hqDenom]
    linarith
  have hsum0 : 0 ≤ hitError + exitError - hitError * exitError := by
    nlinarith [mul_nonneg hexit0 (sub_nonneg.mpr hhit1)]
  unfold markedPoissonUpperError
  rw [max_le_iff]
  constructor
  · linarith
  · calc
      (hitError + exitError - hitError * exitError) * q / (1 - q) =
          (hitError + exitError - hitError * exitError) * (q / (1 - q)) := by
            ring
      _ ≤ (hitError + exitError - hitError * exitError) * 1 :=
        mul_le_mul_of_nonneg_left hodds1 hsum0
      _ ≤ 3 * a := by nlinarith [mul_nonneg hhit0 hexit0]

theorem eventually_terminalMarkedLoss_budgets :
    ∀ᶠ s : ℕ in atTop,
      (requiredTerminalCount s chosenProfileDelta : ℝ) *
          canonicalTerminalMarkedLoss s ≤ 1 / 4 ∧
      (requiredTerminalCount s chosenProfileDelta : ℝ) *
          terminalMarkedPoissonUpperError s (s ^ 8)
            (terminalHitRelativeError s) ≤ 1 / 4 := by
  filter_upwards [eventually_terminalHitRelativeError_le_budget,
    eventually_terminalPoissonExitError_le_budget,
    eventually_terminalHitRelativeError_nonneg,
    eventually_terminalPoissonExitError_nonneg,
    eventually_terminalHitProbability_le_half,
    eventually_ge_atTop 4] with s hhit hexit hhit0 hexit0 hqHalf hs
  let a : ℝ := 1 / (24 * (s : ℝ) ^ 2)
  have ha1 : a ≤ 1 := by
    dsimp [a]
    rw [div_le_one (by positivity : 0 < 24 * (s : ℝ) ^ 2)]
    have hsCast : (4 : ℝ) ≤ s := by exact_mod_cast hs
    nlinarith [sq_nonneg (s : ℝ)]
  have hlower := requiredTerminalCount_mul_markedPoissonLowerError_le_quarter
    s (by omega) (terminalHitProbability_nonneg s) hqHalf hhit0 hexit0
    hhit hexit
  have hupperError := markedPoissonUpperError_le_three_mul
    (terminalHitProbability_nonneg s) hqHalf hhit0 hexit0
    (by simpa [a] using hhit) (by simpa [a] using hexit) ha1
  have hupper0 : 0 ≤ terminalMarkedPoissonUpperError s (s ^ 8)
      (terminalHitRelativeError s) := by
    unfold terminalMarkedPoissonUpperError markedPoissonUpperError
    apply le_max_of_le_left
    positivity
  have hm := requiredTerminalCount_chosenProfile_le_two_sq s (by omega)
  constructor
  · simpa [canonicalTerminalMarkedLoss, terminalMarkedPoissonLowerError] using hlower
  · calc
      (requiredTerminalCount s chosenProfileDelta : ℝ) *
          terminalMarkedPoissonUpperError s (s ^ 8)
            (terminalHitRelativeError s) ≤
        (2 * (s : ℝ) ^ 2) * (3 * a) :=
          mul_le_mul hm (by
            simpa [terminalMarkedPoissonUpperError,
              terminalPoissonExitError] using hupperError)
            hupper0 (by positivity)
      _ = 1 / 4 := by
        dsimp [a]
        field_simp
        norm_num

/-- All analytic and numerical fields required by the marked terminal
one-excursion adapters, at one deterministic terminal scale. -/
structure TerminalMarkedAnalyticCertificate (s : ℕ) : Prop where
  scale_ge_four : 4 ≤ s
  cut_inner : s ^ 6 + 2 ≤ s ^ 8
  cut_scale : s ^ 8 + 2 * s ^ 6 + 2 ≤ s ^ 9
  cut_outer : s ^ 8 + 4 ≤ s ^ 9
  greenLower_pos : 0 < greenPoleLower (s ^ 9) (s ^ 8) (s ^ 6)
  hitError_nonneg : 0 ≤ terminalHitRelativeError s
  hitFactor_nonneg : 0 ≤ 1 - terminalHitRelativeError s
  exitError_nonneg : 0 ≤ terminalPoissonExitError s (s ^ 8)
  exitError_le_one : terminalPoissonExitError s (s ^ 8) ≤ 1
  markedLoss_le_one : canonicalTerminalMarkedLoss s ≤ 1
  markedLoss_quarter :
    (requiredTerminalCount s chosenProfileDelta : ℝ) *
      canonicalTerminalMarkedLoss s ≤ 1 / 4
  markedUpperLoss_quarter :
    (requiredTerminalCount s chosenProfileDelta : ℝ) *
      terminalMarkedPoissonUpperError s (s ^ 8)
        (terminalHitRelativeError s) ≤ 1 / 4
  hitLower : ∀ center (u : TerminalEntrance s center),
    (1 - terminalHitRelativeError s) * terminalHitProbability s ≤
      boundaryStoppedHitKernel (terminalOuterBoundary s center) center u.1
  hitUpper : ∀ center (u : TerminalEntrance s center),
    boundaryStoppedHitKernel (terminalOuterBoundary s center) center u.1 ≤
      (1 + terminalHitRelativeError s) * terminalHitProbability s

theorem eventually_terminalMarkedAnalyticCertificate :
    ∀ᶠ s : ℕ in atTop, TerminalMarkedAnalyticCertificate s := by
  filter_upwards [eventually_terminalHitReferenceLower_ge_one,
    eventually_terminalGreenPoleLower_ge_one,
    eventually_terminalHitRelativeError_le_budget,
    eventually_terminalPoissonExitError_le_budget,
    eventually_terminalHitRelativeError_nonneg,
    eventually_terminalPoissonExitError_nonneg,
    eventually_terminalMarkedLoss_budgets,
    eventually_terminalHitProbability_le_half,
    eventually_ge_atTop 4] with s hhitLower hgreen hhit hexit hhit0 hexit0
      hloss hqHalf hs
  have hbudgetOne : 1 / (24 * (s : ℝ) ^ 2) ≤ 1 := by
    rw [div_le_one (by positivity : 0 < 24 * (s : ℝ) ^ 2)]
    have hsCast : (4 : ℝ) ≤ s := by exact_mod_cast hs
    nlinarith [sq_nonneg (s : ℝ)]
  have hhit1 : terminalHitRelativeError s ≤ 1 := hhit.trans hbudgetOne
  have hexit1 : terminalPoissonExitError s (s ^ 8) ≤ 1 := hexit.trans hbudgetOne
  have hlossOne : canonicalTerminalMarkedLoss s ≤ 1 := by
    have herr := markedPoissonLowerError_le_three_mul
      (terminalHitProbability_nonneg s) hqHalf hhit0 hexit0 hhit hexit hbudgetOne
    unfold canonicalTerminalMarkedLoss terminalMarkedPoissonLowerError
    exact herr.trans (by
      have hsCast : (4 : ℝ) ≤ s := by exact_mod_cast hs
      have hden : (0 : ℝ) < 24 * (s : ℝ) ^ 2 := by positivity
      have hthird : 1 / (24 * (s : ℝ) ^ 2) ≤ 1 / 3 := by
        rw [div_le_div_iff₀ hden (by norm_num : (0 : ℝ) < 3)]
        nlinarith [sq_nonneg (s : ℝ)]
      linarith)
  refine
    { scale_ge_four := hs
      cut_inner := terminalCut_inner_separated s (by omega)
      cut_scale := terminalCut_scale_separated s (by omega)
      cut_outer := terminalCut_outer_separated s (by omega)
      greenLower_pos := by linarith
      hitError_nonneg := hhit0
      hitFactor_nonneg := sub_nonneg.mpr hhit1
      exitError_nonneg := hexit0
      exitError_le_one := hexit1
      markedLoss_le_one := hlossOne
      markedLoss_quarter := hloss.1
      markedUpperLoss_quarter := hloss.2
      hitLower := ?_
      hitUpper := ?_ }
  · intro center u
    exact (terminalBoundaryStoppedHit_two_sided s (by omega) center
      (by linarith) u).1
  · intro center u
    exact (terminalBoundaryStoppedHit_two_sided s (by omega) center
      (by linarith) u).2

/-- Combined terminal certificate: the exact `q/p` mean--variance bounds
and all marked Poisson-kernel geometry/error fields at the same scale. -/
structure TerminalMarkedScaleCertificate (delta : ℝ) (s : ℕ) : Prop where
  parameters : TerminalParameterCertificate delta s
  marked : TerminalMarkedAnalyticCertificate s

/-- Final HLOZ-scale package consumed by the terminal-thickness and pair
adapters.  Both the concentration certificate and the marked-kernel error
certificate hold eventually along `s = scaleIndex delta n`. -/
theorem eventually_terminalMarkedScaleCertificate_scaleIndex
    {delta : ℝ} (hdelta : 0 < delta) :
    ∀ᶠ n : ℕ in atTop,
      TerminalMarkedScaleCertificate delta
        (Proposition13Scales.scaleIndex delta n) := by
  have htendstoNat : Tendsto (Proposition13Scales.scaleIndex delta)
      atTop atTop := by
    apply tendsto_atTop.2
    intro b
    have hreal := (Proposition13Scales.tendsto_scaleIndex_atTop delta).eventually
      (eventually_ge_atTop (b : ℝ))
    filter_upwards [hreal] with n hn
    exact_mod_cast hn
  have hmarked :=
    htendstoNat.eventually eventually_terminalMarkedAnalyticCertificate
  filter_upwards [eventually_terminalParameterCertificate_scaleIndex hdelta,
    hmarked] with n hparameters hmarkedAt
  exact ⟨hparameters, hmarkedAt⟩

end

end Erdos1165.TerminalMarkedParameterBounds
