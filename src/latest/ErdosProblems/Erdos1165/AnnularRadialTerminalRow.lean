/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/
/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

import ErdosProblems.Erdos1165.AnnularRadialOneStepRow
import ErdosProblems.Erdos1165.TerminalProfileClockEquivalence
import ErdosProblems.Erdos1165.ExcursionTransition

/-!
# The asymmetric terminal row of the chronological radial chain

The last annulus is not a logarithmic midpoint: the outward potential gap
is `3 log n` times the inward one.  This file gives the corresponding
endpoint-integrated comparison with the exact HLOZ terminal success
parameter, retaining the literal real radii throughout.
-/

open MeasureTheory Set Filter
open scoped BigOperators ENNReal Topology

namespace Erdos1165.AnnularRadialTerminalRow

open Annulus AnnulusHarnack ThickPoint PlanarPotential RealDiscFinite
open PotentialConvergence
open MarkedBoundaryVisitKernel AnnularOffspringKernelRadial
open AnnularOffspringKernelRadialExit AnnularRadialOneStepRow
open AnnularRadialLabelWord LiteralRealAnnulus LiteralRealAnnulusRadialExit
open AnnularProfileClocks ProfileAnnularRowRegular
open TerminalProfileClockEquivalence TerminalSpliceProfileGeometry
open ExcursionTransition

noncomputable section

/-- Relative error normalized by the smaller, inward terminal potential
gap. -/
def terminalRadialRowError (n : ℕ) : ℝ :=
  (max (realBoundaryPotentialError (scaleRadius n (n + 1)))
      (realBoundaryPotentialError (scaleRadius n (n - 1))) +
    realBoundaryPotentialError (scaleRadius n n)) /
    (realBoundaryPotentialValue (scaleRadius n (n - 1)) -
      realBoundaryPotentialValue (scaleRadius n n))

/-- A fixed coefficient for the terminal relative row error. -/
def terminalRadialRowErrorConstant : ℝ :=
  8 * (PotentialRadialGlobal.globalRadialConstant + 2)

/-- A non-midpoint annulus row is controlled relative to its exact inward
radial-potential ratio. -/
theorem literalRealAnnulusInnerExit_relative_bounds
    {rInner rMiddle rOuter : ℝ} {boxRadius : ℕ} {x : Point}
    (hrInner : 2 < rInner) (hrMiddle : 2 < rMiddle)
    (hrOuter : 2 < rOuter)
    (hOuterBox : rOuter ≤ (boxRadius : ℝ))
    (hInnerSep : rInner + 1 ≤ rMiddle)
    (hOuterSep : rMiddle + 1 ≤ rOuter)
    (hxMiddle : x ∈ discBoundary 0 rMiddle)
    (hdelta : 0 < realBoundaryPotentialValue rOuter -
      realBoundaryPotentialValue rInner)
    (hgap : 0 < realBoundaryPotentialValue rOuter -
      realBoundaryPotentialValue rMiddle) :
    let error :=
      (max (realBoundaryPotentialError rInner)
          (realBoundaryPotentialError rOuter) +
        realBoundaryPotentialError rMiddle) /
        (realBoundaryPotentialValue rOuter -
          realBoundaryPotentialValue rMiddle)
    let ideal :=
      (realBoundaryPotentialValue rOuter -
          realBoundaryPotentialValue rMiddle) /
        (realBoundaryPotentialValue rOuter -
          realBoundaryPotentialValue rInner)
    (1 - error) * ideal ≤
        (exitMass (literalRealAnnulus rInner rOuter boxRadius)
          (literalRealAnnulusInnerExit rInner rOuter boxRadius) x).toReal ∧
      (exitMass (literalRealAnnulus rInner rOuter boxRadius)
          (literalRealAnnulusInnerExit rInner rOuter boxRadius) x).toReal ≤
        (1 + error) * ideal := by
  dsimp only
  let epsilon := max (realBoundaryPotentialError rInner)
    (realBoundaryPotentialError rOuter)
  let middleError := realBoundaryPotentialError rMiddle
  let innerValue := realBoundaryPotentialValue rInner
  let middleValue := realBoundaryPotentialValue rMiddle
  let outerValue := realBoundaryPotentialValue rOuter
  let delta := outerValue - innerValue
  let gap := outerValue - middleValue
  let error := (epsilon + middleError) / gap
  let ideal := gap / delta
  have hx := mem_literalRealAnnulus_of_mem_intermediate_discBoundary
    (by linarith : 0 ≤ rOuter) hOuterBox hInnerSep hOuterSep hxMiddle
  have hratio := literalRealAnnulusInnerExit_ratio_bounds
    hrInner hrOuter hOuterBox hx hdelta
  have hmiddle :=
    abs_planarPotentialKernel_sub_realBoundaryPotentialValue_le
      hrMiddle hxMiddle
  change |planarPotentialKernel x - middleValue| ≤ middleError at hmiddle
  rw [abs_le] at hmiddle
  change 0 < delta at hdelta
  change 0 < gap at hgap
  have hmulLower : ((1 - error) * ideal) * delta =
      gap - (epsilon + middleError) := by
    have hdeltaNe : outerValue - innerValue ≠ 0 := by
      exact ne_of_gt hdelta
    have hgapNe : outerValue - middleValue ≠ 0 := by
      exact ne_of_gt hgap
    dsimp only [error, ideal, delta, gap]
    field_simp [hdeltaNe, hgapNe]
  have hmulUpper : ((1 + error) * ideal) * delta =
      gap + (epsilon + middleError) := by
    have hdeltaNe : outerValue - innerValue ≠ 0 := by
      exact ne_of_gt hdelta
    have hgapNe : outerValue - middleValue ≠ 0 := by
      exact ne_of_gt hgap
    dsimp only [error, ideal, delta, gap]
    field_simp [hdeltaNe, hgapNe]
  change
    (1 - error) * ideal ≤
        (exitMass (literalRealAnnulus rInner rOuter boxRadius)
          (literalRealAnnulusInnerExit rInner rOuter boxRadius) x).toReal ∧
      (exitMass (literalRealAnnulus rInner rOuter boxRadius)
          (literalRealAnnulusInnerExit rInner rOuter boxRadius) x).toReal ≤
        (1 + error) * ideal
  constructor
  · calc
      (1 - error) * ideal ≤
          (outerValue - planarPotentialKernel x - epsilon) / delta := by
        rw [le_div_iff₀ hdelta]
        rw [hmulLower]
        linarith
      _ ≤ _ := hratio.1
  · calc
      _ ≤ (outerValue - planarPotentialKernel x + epsilon) / delta :=
        hratio.2
      _ ≤ (1 + error) * ideal := by
        rw [div_le_iff₀ hdelta]
        rw [hmulUpper]
        linarith

theorem terminal_outer_middle_potential_gap
    {n : ℕ} (hn : 0 < n) :
    realBoundaryPotentialValue (scaleRadius n (n - 1)) -
        realBoundaryPotentialValue (scaleRadius n n) = 2 / Real.pi := by
  rw [scaleRadius_of_le (by omega : n - 1 ≤ n),
    scaleRadius_of_le le_rfl]
  unfold realBoundaryPotentialValue
  rw [log_regularRadius n (n - 1) hn, log_regularRadius n n hn]
  have hcast : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ n)]
    norm_num
  rw [hcast]
  ring

theorem terminal_middle_inner_potential_gap
    {n : ℕ} (_hn : 0 < n) :
    realBoundaryPotentialValue (scaleRadius n n) -
        realBoundaryPotentialValue (scaleRadius n (n + 1)) =
      (6 / Real.pi) * Real.log n := by
  rw [scaleRadius_of_le le_rfl, regularRadius_self,
    scaleRadius_succ_self]
  unfold realBoundaryPotentialValue
  rw [Real.log_pow, Real.log_pow]
  ring

theorem one_sub_terminalSuccess_eq_terminal_inward_ratio
    {n : ℕ} (hn : 2 ≤ n) :
    1 - terminalSuccess n =
      (realBoundaryPotentialValue (scaleRadius n (n - 1)) -
          realBoundaryPotentialValue (scaleRadius n n)) /
        (realBoundaryPotentialValue (scaleRadius n (n - 1)) -
          realBoundaryPotentialValue (scaleRadius n (n + 1))) := by
  rw [terminal_outer_middle_potential_gap (by omega),
    show realBoundaryPotentialValue (scaleRadius n (n - 1)) -
        realBoundaryPotentialValue (scaleRadius n (n + 1)) =
      (realBoundaryPotentialValue (scaleRadius n (n - 1)) -
          realBoundaryPotentialValue (scaleRadius n n)) +
        (realBoundaryPotentialValue (scaleRadius n n) -
          realBoundaryPotentialValue (scaleRadius n (n + 1))) by ring,
    terminal_outer_middle_potential_gap (by omega),
    terminal_middle_inner_potential_gap (by omega)]
  have hlog : 0 < Real.log (n : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < n by omega))
  unfold terminalSuccess
  field_simp [ne_of_gt Real.pi_pos, ne_of_gt (by positivity :
    (0 : ℝ) < 1 + 3 * Real.log n)]
  ring

theorem terminalSuccess_eq_terminal_outward_ratio
    {n : ℕ} (hn : 2 ≤ n) :
    terminalSuccess n =
      (realBoundaryPotentialValue (scaleRadius n n) -
          realBoundaryPotentialValue (scaleRadius n (n + 1))) /
        (realBoundaryPotentialValue (scaleRadius n (n - 1)) -
          realBoundaryPotentialValue (scaleRadius n (n + 1))) := by
  rw [show realBoundaryPotentialValue (scaleRadius n (n - 1)) -
        realBoundaryPotentialValue (scaleRadius n (n + 1)) =
      (realBoundaryPotentialValue (scaleRadius n (n - 1)) -
          realBoundaryPotentialValue (scaleRadius n n)) +
        (realBoundaryPotentialValue (scaleRadius n n) -
          realBoundaryPotentialValue (scaleRadius n (n + 1))) by ring,
    terminal_outer_middle_potential_gap (by omega),
    terminal_middle_inner_potential_gap (by omega)]
  have hlog : 0 < Real.log (n : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < n by omega))
  unfold terminalSuccess
  field_simp [ne_of_gt Real.pi_pos, ne_of_gt (by positivity :
    (0 : ℝ) < 1 + 3 * Real.log n)]
  ring

/-- Exact terminal `n → n+1` and `n → n-1` relative lower bounds,
with every spatial endpoint integrated only at its chronological step. -/
theorem radialOneStepKernelENNReal_terminal_ofReal_lower
    {n : ℕ} (hn : 2 ≤ n) (center start : Point)
    (hstart : start ∈ radialBoundary n center ⟨n, by omega⟩) :
    ENNReal.ofReal
        ((1 - terminalRadialRowError n) * (1 - terminalSuccess n)) ≤
        radialOneStepKernelENNReal n center ⟨n, by omega⟩
          ⟨n + 1, by omega⟩ start ∧
      ENNReal.ofReal
        ((1 - terminalRadialRowError n) * terminalSuccess n) ≤
        radialOneStepKernelENNReal n center ⟨n, by omega⟩
          ⟨n - 1, by omega⟩ start := by
  let rInner := scaleRadius n (n + 1)
  let rMiddle := scaleRadius n n
  let rOuter := scaleRadius n (n - 1)
  let boxRadius : ℕ := Nat.ceil rOuter
  let u : ProfileCycleMiddlePoint n n center :=
    ⟨start, mem_discBoundaryFinset.mpr (by
      simpa [radialBoundary] using hstart)⟩
  let u0 : LiteralMiddlePoint rMiddle :=
    ⟨start - center, mem_discBoundaryFinset.mpr
      ((BoundaryStoppedHarnack.mem_discBoundary_translate center rMiddle start).mp
        (by simpa [rMiddle, radialBoundary] using hstart))⟩
  have hrInner : 2 < rInner := by
    dsimp [rInner]
    rw [scaleRadius_succ_self]
    have hnreal : (2 : ℝ) ≤ n := by exact_mod_cast hn
    nlinarith [pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hnreal 6]
  have hrMiddle : 2 < rMiddle := by
    dsimp [rMiddle]
    rw [scaleRadius_of_le le_rfl, regularRadius_self]
    have hnreal : (2 : ℝ) ≤ n := by exact_mod_cast hn
    nlinarith [pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hnreal 9]
  have hrOuter : 2 < rOuter := by
    dsimp [rOuter]
    have hle : scaleRadius n n ≤ scaleRadius n (n - 1) :=
      scaleRadius_antitone_of_le (by omega) (by omega)
    linarith
  have hbox : rOuter ≤ (boxRadius : ℝ) := by
    exact_mod_cast Nat.le_ceil rOuter
  have hInnerSep : rInner + 1 ≤ rMiddle := by
    exact terminal_profile_radius_add_one_le hn
  have hOuterSep : rMiddle + 1 ≤ rOuter := by
    exact scaleRadius_self_add_one_le_of_lt (by omega) (by omega)
  have hgap : 0 < realBoundaryPotentialValue rOuter -
      realBoundaryPotentialValue rMiddle := by
    dsimp [rOuter, rMiddle]
    rw [terminal_outer_middle_potential_gap (by omega)]
    positivity
  have hdelta : 0 < realBoundaryPotentialValue rOuter -
      realBoundaryPotentialValue rInner := by
    have hmiddleInner : 0 < realBoundaryPotentialValue rMiddle -
        realBoundaryPotentialValue rInner := by
      dsimp [rMiddle, rInner]
      rw [terminal_middle_inner_potential_gap (by omega)]
      have hlog : 0 < Real.log (n : ℝ) :=
        Real.log_pos (by exact_mod_cast (show 1 < n by omega))
      positivity
    linarith
  have hinnerBounds := literalRealAnnulusInnerExit_relative_bounds
    hrInner hrMiddle hrOuter hbox hInnerSep hOuterSep
      (mem_discBoundaryFinset.mp u0.2) hdelta hgap
  have hcentered := sum_skeletonExitKernel_literalInnerBoundary_eq_exitMass
    (by linarith : 0 ≤ rOuter) hbox hInnerSep hOuterSep u0
  have hinwardExact := radialOneStepKernelENNReal_terminal_inward_toReal_eq
    hn center start hstart
  have hprofileCenter := profileInwardRow_eq_centeredInwardRow u
  have hidealIn :
      (realBoundaryPotentialValue rOuter -
          realBoundaryPotentialValue rMiddle) /
        (realBoundaryPotentialValue rOuter -
          realBoundaryPotentialValue rInner) = 1 - terminalSuccess n := by
    dsimp [rOuter, rMiddle, rInner]
    exact (one_sub_terminalSuccess_eq_terminal_inward_ratio hn).symm
  have herror :
      (max (realBoundaryPotentialError rInner)
          (realBoundaryPotentialError rOuter) +
        realBoundaryPotentialError rMiddle) /
        (realBoundaryPotentialValue rOuter -
          realBoundaryPotentialValue rMiddle) = terminalRadialRowError n := by
    rfl
  have hinnerLower :
      (1 - terminalRadialRowError n) * (1 - terminalSuccess n) ≤
        (radialOneStepKernelENNReal n center ⟨n, by omega⟩
          ⟨n + 1, by omega⟩ start).toReal := by
    rw [hinwardExact, hprofileCenter, hcentered]
    simpa [herror, hidealIn] using hinnerBounds.1
  have hinnerUpper :
      (radialOneStepKernelENNReal n center ⟨n, by omega⟩
          ⟨n + 1, by omega⟩ start).toReal ≤
        (1 + terminalRadialRowError n) * (1 - terminalSuccess n) := by
    rw [hinwardExact, hprofileCenter, hcentered]
    simpa [herror, hidealIn] using hinnerBounds.2
  have houterNonempty : (profileOuterBoundary n n center).Nonempty := by
    apply ProfileAnnularRowRegular.discBoundary_center_nonempty_of_nonneg
    unfold scaleRadius regularRadius
    split_ifs <;> positivity
  have hrenewal := profileAnnularCycle_escape_isStochasticRenewalRow
    houterNonempty
    (terminalRadius_le_regularRadius_self n (by omega)) hOuterSep u
  have hmiddleNonempty : (profileInnerBoundary n n center).Nonempty := by
    apply ProfileAnnularRowRegular.discBoundary_center_nonempty_of_nonneg
    unfold scaleRadius regularRadius
    split_ifs <;> positivity
  have hcycle := sum_profileAnnularCycleKernelReal_eq_inwardRow
    hmiddleNonempty u
  rw [hcycle] at hrenewal
  have houtwardExact := radialOneStepKernelENNReal_terminal_outward_toReal_eq
    hn center start hstart
  have herrNonneg : 0 ≤ terminalRadialRowError n := by
    unfold terminalRadialRowError
    apply div_nonneg
    · exact add_nonneg
        ((realBoundaryPotentialError_nonneg (by
            dsimp [rInner] at hrInner ⊢
            linarith)).trans
          (le_max_left _ _))
        (realBoundaryPotentialError_nonneg (by
          dsimp [rMiddle] at hrMiddle ⊢
          linarith))
    · exact hgap.le
  have hsuccessDominates : 1 - terminalSuccess n ≤ terminalSuccess n := by
    have hlogMonotone : Real.log 2 ≤ Real.log (n : ℝ) := by
      apply Real.log_le_log (by norm_num)
      exact_mod_cast hn
    have hlog : (1 : ℝ) ≤ 3 * Real.log n := by
      nlinarith [Real.log_two_gt_d9]
    have hden : 0 < 1 + 3 * Real.log n := by positivity
    unfold terminalSuccess
    rw [show 1 - 3 * Real.log (n : ℝ) /
        (1 + 3 * Real.log (n : ℝ)) =
      1 / (1 + 3 * Real.log (n : ℝ)) by
        field_simp [ne_of_gt hden]
        ring]
    exact (div_le_div_iff_of_pos_right hden).2 hlog
  have houtwardLower :
      (1 - terminalRadialRowError n) * terminalSuccess n ≤
        (radialOneStepKernelENNReal n center ⟨n, by omega⟩
          ⟨n - 1, by omega⟩ start).toReal := by
    rw [houtwardExact]
    rw [hinwardExact] at hinnerUpper
    linarith [mul_le_mul_of_nonneg_left hsuccessDominates herrNonneg]
  constructor
  · exact (ENNReal.ofReal_le_iff_le_toReal (by
      unfold radialOneStepKernelENNReal
      exact measure_ne_top fairSteps _)).2 hinnerLower
  · exact (ENNReal.ofReal_le_iff_le_toReal (by
      unfold radialOneStepKernelENNReal
      exact measure_ne_top fairSteps _)).2 houtwardLower

/-- The explicit terminal relative error is `O(n⁻⁶)`. -/
theorem terminalRadialRowError_le_rate
    {n : ℕ} (hn : 2 ≤ n) :
    terminalRadialRowError n ≤
      terminalRadialRowErrorConstant / (n : ℝ) ^ 6 := by
  let rInner := scaleRadius n (n + 1)
  let rMiddle := scaleRadius n n
  let rOuter := scaleRadius n (n - 1)
  have hrInner : 1 < rInner := by
    dsimp [rInner]
    rw [scaleRadius_succ_self]
    have hnreal : (2 : ℝ) ≤ n := by exact_mod_cast hn
    nlinarith [pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hnreal 6]
  have hInnerMiddle : rInner ≤ rMiddle :=
    terminalRadius_le_regularRadius_self n (by omega)
  have hMiddleOuter : rMiddle ≤ rOuter := by
    exact scaleRadius_antitone_of_le (by omega) (by omega)
  have hmiddleError := realBoundaryPotentialError_antitone
    hrInner hInnerMiddle
  have houterError := realBoundaryPotentialError_antitone
    hrInner (hInnerMiddle.trans hMiddleOuter)
  have hinnerError0 := realBoundaryPotentialError_nonneg hrInner
  let N : ℝ := (n : ℝ) ^ 6
  let K : ℝ := PotentialRadialGlobal.globalRadialConstant + 2
  have hK : 0 ≤ K := by
    dsimp [K]
    linarith [PotentialRadialGlobal.globalRadialConstant_pos]
  have hN : 2 ≤ N := by
    dsimp [N]
    have hnreal : (2 : ℝ) ≤ n := by exact_mod_cast hn
    nlinarith [pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hnreal 6]
  have hden : N / 2 ≤ N - 1 := by linarith
  have herrorRate : realBoundaryPotentialError rInner ≤ 2 * K / N := by
    dsimp [rInner, N, K]
    rw [scaleRadius_succ_self]
    unfold realBoundaryPotentialError
    calc
      (PotentialRadialGlobal.globalRadialConstant + 2) /
          ((n : ℝ) ^ 6 - 1) ≤
          (PotentialRadialGlobal.globalRadialConstant + 2) /
            ((n : ℝ) ^ 6 / 2) := by
        apply div_le_div_of_nonneg_left hK (by positivity)
        simpa [N] using hden
      _ = 2 * (PotentialRadialGlobal.globalRadialConstant + 2) /
          (n : ℝ) ^ 6 := by
        field_simp
  unfold terminalRadialRowError terminalRadialRowErrorConstant
  rw [terminal_outer_middle_potential_gap (by omega),
    max_eq_left houterError]
  calc
    (realBoundaryPotentialError (scaleRadius n (n + 1)) +
          realBoundaryPotentialError (scaleRadius n n)) / (2 / Real.pi) ≤
        (realBoundaryPotentialError rInner +
          realBoundaryPotentialError rInner) / (2 / Real.pi) := by
      gcongr
    _ = Real.pi * realBoundaryPotentialError rInner := by
      field_simp [ne_of_gt Real.pi_pos]
      ring
    _ ≤ 4 * realBoundaryPotentialError rInner :=
      mul_le_mul_of_nonneg_right Real.pi_le_four hinnerError0
    _ ≤ 4 * (2 * K / N) :=
      mul_le_mul_of_nonneg_left herrorRate (by norm_num)
    _ = 8 * (PotentialRadialGlobal.globalRadialConstant + 2) /
        (n : ℝ) ^ 6 := by
      dsimp [K, N]
      ring

/-- The terminal error is eventually at most `n⁻⁵`; one power is spent
absorbing its fixed coefficient. -/
theorem eventually_terminalRadialRowError_le_inv_pow_five :
    ∀ᶠ n : ℕ in atTop,
      terminalRadialRowError n ≤ 1 / (n : ℝ) ^ 5 := by
  have hlarge := tendsto_natCast_atTop_atTop.eventually
    (eventually_ge_atTop terminalRadialRowErrorConstant)
  filter_upwards [hlarge, eventually_ge_atTop 2] with n hnLarge hn
  have hrate := terminalRadialRowError_le_rate hn
  have hnPos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  calc
    terminalRadialRowError n ≤
        terminalRadialRowErrorConstant / (n : ℝ) ^ 6 := hrate
    _ ≤ (n : ℝ) / (n : ℝ) ^ 6 := by gcongr
    _ = 1 / (n : ℝ) ^ 5 := by
      field_simp

/-- Fully automatic terminal decision lower bounds. -/
theorem eventually_radialOneStepKernelENNReal_terminal_lower_inv_pow_five :
    ∀ᶠ n : ℕ in atTop, ∀ (center start : Point),
      start ∈ radialBoundary n center ⟨n, by omega⟩ →
      ENNReal.ofReal
          ((1 - 1 / (n : ℝ) ^ 5) * (1 - terminalSuccess n)) ≤
          radialOneStepKernelENNReal n center ⟨n, by omega⟩
            ⟨n + 1, by omega⟩ start ∧
        ENNReal.ofReal
          ((1 - 1 / (n : ℝ) ^ 5) * terminalSuccess n) ≤
          radialOneStepKernelENNReal n center ⟨n, by omega⟩
            ⟨n - 1, by omega⟩ start := by
  filter_upwards [eventually_terminalRadialRowError_le_inv_pow_five,
      eventually_ge_atTop 2] with n herror hn
  intro center start hstart
  have hlower := radialOneStepKernelENNReal_terminal_ofReal_lower
    hn center start hstart
  have hsuccess0 : 0 ≤ terminalSuccess n :=
    (terminalSuccess_pos hn).le
  have hfailure0 : 0 ≤ 1 - terminalSuccess n :=
    sub_nonneg.mpr (terminalSuccess_le_one hn)
  constructor
  · exact (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right
      (by linarith) hfailure0)).trans hlower.1
  · exact (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right
      (by linarith) hsuccess0)).trans hlower.2

end

end Erdos1165.AnnularRadialTerminalRow
