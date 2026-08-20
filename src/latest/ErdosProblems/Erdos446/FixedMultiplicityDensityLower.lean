/-
Copyright (c) 2026 The Formal Conjectures Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Formal Conjectures Authors
-/

import ErdosProblems.Erdos446.FixedMultiplicityAtomScale
import ErdosProblems.Erdos446.FixedMultiplicityParameters
import ErdosProblems.Erdos446.FixedMultiplicityReduction
import ErdosProblems.Erdos446.FixedMultiplicitySizedAssembly
import ErdosProblems.Erdos446.FixedLowerEnergyMoment
import ErdosProblems.Erdos446.EulerEstimate

/-!
# Erdős Problem 446: unconditional prescribed-multiplicity lower bound

This module closes Ford's fixed-multiplicity construction.  It compares the
explicit size-truncated prime-block family with the selected-depth model,
uses the weak Mertens estimate for the remaining Euler factor, and packages
the result in `FixedMultiplicityModelDensityLower`.
-/

namespace Erdos446

open Filter Real Asymptotics
open scoped Topology

/-- The finite isolated-divisor core before the outer-prime and Euler sieve
factors are inserted. -/
noncomputable def fixedMultiplicityCore (r K : ℕ) : ℝ :=
  ((((2 : ℝ) ^ K) / 2) ^ (r - 1)) * (91 / 600 : ℝ) *
    (2 * Real.log 2 : ℝ) ^ K *
    ((1 / 8 : ℝ) *
      ((K : ℝ) ^ K / ((K + 1).factorial : ℝ)))

/-- The literal left side of the complete finite exact-multiplicity
construction at the selected depth. -/
noncomputable def fixedMultiplicityFiniteLower (r M y : ℕ) : ℝ :=
  let K := fordScaleDepth M y
  smallPrimeEulerDensity (2 * y) *
    ((((1 : ℝ) / (8 * Real.log (y : ℝ))) ^ r /
        (r.factorial : ℝ)) * fixedMultiplicityCore r K)

/-- The same numerator with Ford's reciprocal-factorial coefficient and
without the explicit sieve constants. -/
noncomputable def fixedMultiplicityCombinatorialDensity
    (r M y : ℕ) : ℝ :=
  let K := fordScaleDepth M y
  (((2 : ℝ) ^ K) ^ (r - 1) * fordCombinatorialWeight K) /
    Real.log (y : ℝ) ^ (r + 1)

theorem fixedMultiplicityCore_nonneg (r K : ℕ) :
    0 ≤ fixedMultiplicityCore r K := by
  dsimp [fixedMultiplicityCore]
  positivity

theorem fordNaturalScale_half_combinatorial {K : ℕ} (hK : 1 ≤ K) :
    (K : ℝ) ^ (K - 1) / (K.factorial : ℝ) ≤
      2 * ((K : ℝ) ^ K / ((K + 1).factorial : ℝ)) := by
  rw [Nat.factorial_succ]
  push_cast
  have hKR : (0 : ℝ) < K := by positivity
  have hfac : (0 : ℝ) < (K.factorial : ℝ) := by positivity
  have hpow : (K : ℝ) ^ K = (K : ℝ) ^ (K - 1) * K := by
    simpa [Nat.sub_add_cancel hK] using (pow_succ (K : ℝ) (K - 1))
  rw [hpow]
  have hbase : 0 ≤ (K : ℝ) ^ (K - 1) := by positivity
  have hKCast : (1 : ℝ) ≤ K := by exact_mod_cast hK
  field_simp [hfac.ne', (by positivity : (0 : ℝ) < K + 1).ne']
  nlinarith

/-- The explicit finite core loses only a fixed `r`-dependent constant
relative to the combinatorial numerator. -/
theorem fixedMultiplicity_numerator_le_core
    {r K : ℕ} (hK : 1 ≤ K) :
    (((2 : ℝ) ^ K) ^ (r - 1) * fordCombinatorialWeight K) ≤
      ((2 : ℝ) ^ (r - 1) * 10000) *
        fixedMultiplicityCore r K := by
  have hx : (((2 : ℝ) ^ K) ^ (r - 1)) =
      (2 : ℝ) ^ (r - 1) *
        ((((2 : ℝ) ^ K) / 2) ^ (r - 1)) := by
    rw [div_pow]
    field_simp
  have hnat := fordNaturalScale_half_combinatorial hK
  have hcommon : 0 ≤
      (2 : ℝ) ^ (r - 1) *
        (((((2 : ℝ) ^ K) / 2) ^ (r - 1)) *
          (2 * Real.log 2 : ℝ) ^ K) := by positivity
  rw [fordCombinatorialWeight, hx]
  calc
    ((2 : ℝ) ^ (r - 1) * ((((2 : ℝ) ^ K) / 2) ^ (r - 1)) *
          ((2 * Real.log 2 : ℝ) ^ K *
            ((K : ℝ) ^ (K - 1) / (K.factorial : ℝ)))) =
        ((2 : ℝ) ^ (r - 1) *
          (((((2 : ℝ) ^ K) / 2) ^ (r - 1)) *
            (2 * Real.log 2 : ℝ) ^ K)) *
            ((K : ℝ) ^ (K - 1) / (K.factorial : ℝ)) := by ring
    _ ≤ ((2 : ℝ) ^ (r - 1) *
          (((((2 : ℝ) ^ K) / 2) ^ (r - 1)) *
            (2 * Real.log 2 : ℝ) ^ K)) *
            (2 * ((K : ℝ) ^ K / ((K + 1).factorial : ℝ))) :=
      mul_le_mul_of_nonneg_left hnat hcommon
    _ ≤ ((2 : ℝ) ^ (r - 1) * 10000) *
          fixedMultiplicityCore r K := by
      dsimp [fixedMultiplicityCore]
      have hscale : 0 ≤
          ((K : ℝ) ^ K / ((K + 1).factorial : ℝ)) := by positivity
      have hcoef : (2 : ℝ) ≤ 10000 * (91 / 600 : ℝ) * (1 / 8) := by
        norm_num
      nlinarith [mul_le_mul_of_nonneg_left hcoef (mul_nonneg hcommon hscale)]

noncomputable def fixedMultiplicitySieveConstant (r : ℕ) : ℝ :=
  (1 / 8 : ℝ) ^ r / (r.factorial : ℝ)

theorem fixedMultiplicitySieveConstant_pos (r : ℕ) :
    0 < fixedMultiplicitySieveConstant r := by
  dsimp [fixedMultiplicitySieveConstant]
  positivity

theorem fixedMultiplicity_selectionFactor_eq
    (r : ℕ) {L : ℝ} (hL : L ≠ 0) :
    ((1 / (8 * L) : ℝ) ^ r / (r.factorial : ℝ)) =
      fixedMultiplicitySieveConstant r / L ^ r := by
  dsimp [fixedMultiplicitySieveConstant]
  rw [show (1 / (8 * L) : ℝ) = (1 / 8 : ℝ) / L by
    field_simp [hL]]
  rw [div_pow]
  ring

/-- The explicit finite lower expression dominates the combinatorial depth
model up to a constant depending only on the fixed multiplicity. -/
theorem fixedMultiplicityCombinatorialDensity_isBigO_finiteLower
    (r M : ℕ) :
    fixedMultiplicityCombinatorialDensity r M =O[atTop]
      fixedMultiplicityFiniteLower r M := by
  let A : ℝ := cleanMertensConstant446
  let H : ℝ := (2 : ℝ) ^ (r - 1) * 10000
  let s : ℝ := fixedMultiplicitySieveConstant r
  have hA : 0 < A := cleanMertensConstant446_pos
  have hH : 0 < H := by dsimp [H]; positivity
  have hs : 0 < s := by
    dsimp [s]
    exact fixedMultiplicitySieveConstant_pos r
  apply Asymptotics.IsBigO.of_bound (H * (2 * A) / s)
  filter_upwards [eventually_ge_atTop
      (max 2 (fordConstructionScale M 1))] with y hy
  have hy2 : 2 ≤ y := (le_max_left _ _).trans hy
  have hyScale : fordConstructionScale M 1 ≤ y :=
    (le_max_right _ _).trans hy
  let K := fordScaleDepth M y
  have hK : 1 ≤ K := fordScaleDepth_pos hyScale
  have hlog : 0 < Real.log (y : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < y by omega))
  have h2y : 2 ≤ 2 * y := by omega
  have hlog2y : 0 < Real.log (2 * y : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < 2 * y by omega))
  have hlog2le : Real.log (2 * y : ℝ) ≤ 2 * Real.log (y : ℝ) := by
    rw [Real.log_mul (by norm_num) (by positivity)]
    have hlog2lelogy : Real.log 2 ≤ Real.log (y : ℝ) :=
      Real.log_le_log (by norm_num) (by exact_mod_cast hy2)
    linarith
  have heuler : 1 / (A * Real.log (2 * y : ℝ)) ≤
      smallPrimeEulerDensity (2 * y) := by
    simpa only [A, Nat.cast_mul, Nat.cast_ofNat] using
      smallPrimeEulerDensity_lower (2 * y) h2y
  have hden : A * Real.log (2 * y : ℝ) ≤
      2 * A * Real.log (y : ℝ) := by
    dsimp [A]
    nlinarith
  have heuler' : 1 / (2 * A * Real.log (y : ℝ)) ≤
      smallPrimeEulerDensity (2 * y) :=
    (one_div_le_one_div_of_le (by positivity) hden).trans heuler
  have hnum := fixedMultiplicity_numerator_le_core
    (r := r) (K := K) hK
  have hnum0 : 0 ≤
      ((2 : ℝ) ^ K) ^ (r - 1) * fordCombinatorialWeight K := by
    dsimp [fordCombinatorialWeight]
    positivity
  have hcore0 : 0 ≤ fixedMultiplicityCore r K :=
    fixedMultiplicityCore_nonneg r K
  have hfinite0 : 0 ≤ fixedMultiplicityFiniteLower r M y := by
    dsimp [fixedMultiplicityFiniteLower]
    exact mul_nonneg (smallPrimeEulerDensity_nonneg _)
      (mul_nonneg (by positivity) hcore0)
  change ‖((((2 : ℝ) ^ K) ^ (r - 1) * fordCombinatorialWeight K) /
      Real.log (y : ℝ) ^ (r + 1))‖ ≤
    (H * (2 * A) / s) * ‖fixedMultiplicityFiniteLower r M y‖
  rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg hnum0 (by positivity)),
    Real.norm_eq_abs, abs_of_nonneg hfinite0]
  change (((2 : ℝ) ^ K) ^ (r - 1) * fordCombinatorialWeight K) /
      Real.log (y : ℝ) ^ (r + 1) ≤
    (H * (2 * A) / s) * fixedMultiplicityFiniteLower r M y
  calc
    (((2 : ℝ) ^ K) ^ (r - 1) * fordCombinatorialWeight K) /
          Real.log (y : ℝ) ^ (r + 1) ≤
        (H * fixedMultiplicityCore r K) /
          Real.log (y : ℝ) ^ (r + 1) := by
      exact div_le_div_of_nonneg_right (by simpa [H] using hnum)
        (by positivity)
    _ = (H * (2 * A) / s) *
        ((1 / (2 * A * Real.log (y : ℝ))) *
          ((s / Real.log (y : ℝ) ^ r) *
            fixedMultiplicityCore r K)) := by
      have hfac : (0 : ℝ) < (r.factorial : ℝ) := by positivity
      rw [show r + 1 = r + 1 by rfl, pow_succ]
      field_simp [hA.ne', hs.ne', hlog.ne']
    _ ≤ (H * (2 * A) / s) *
        (smallPrimeEulerDensity (2 * y) *
          ((s / Real.log (y : ℝ) ^ r) *
            fixedMultiplicityCore r K)) := by
      gcongr
    _ = (H * (2 * A) / s) * fixedMultiplicityFiniteLower r M y := by
      dsimp [fixedMultiplicityFiniteLower]
      rw [fixedMultiplicity_selectionFactor_eq r hlog.ne']

/-- Replacing Ford's exact reciprocal-factorial coefficient by its depth
model changes the fixed-multiplicity expression by only a constant factor. -/
theorem fordFixedMultiplicityDepthDensityModel_isBigO_combinatorial
    (r M : ℕ) :
    fordFixedMultiplicityDepthDensityModel r M =O[atTop]
      fixedMultiplicityCombinatorialDensity r M := by
  let F : ℕ → ℝ := fun y ↦
    ((2 : ℝ) ^ fordScaleDepth M y) ^ (r - 1) /
      Real.log (y : ℝ) ^ (r + 1)
  have hcoeff := (fordCombinatorialWeight_depth_isTheta_depthModel M).2
  have hfactor : F =O[atTop] F := isBigO_refl _ _
  have hmul := hcoeff.mul hfactor
  apply hmul.congr'
  · filter_upwards with y
    dsimp [fordFixedMultiplicityDepthDensityModel, F]
    ring
  · filter_upwards with y
    dsimp [fixedMultiplicityCombinatorialDensity, F]
    ring

theorem fordFixedMultiplicityDepthDensityModel_isBigO_finiteLower
    (r M : ℕ) :
    fordFixedMultiplicityDepthDensityModel r M =O[atTop]
      fixedMultiplicityFiniteLower r M :=
  (fordFixedMultiplicityDepthDensityModel_isBigO_combinatorial r M).trans
    (fixedMultiplicityCombinatorialDensity_isBigO_finiteLower r M)

/-- For every fixed positive multiplicity, Ford's explicit isolated-divisor
construction supplies a positive constant lower bound by the declared depth
model.  This is the unconditional arithmetic input reserved by the final
Problem 446 assembly. -/
theorem exists_fixedMultiplicityModelDensityLower
    (r : ℕ) (hr : 1 ≤ r) :
    ∃ M : ℕ, ∃ c : ℝ, ∃ Y : ℕ,
      0 < c ∧ FixedMultiplicityModelDensityLower r M c Y := by
  obtain ⟨N, M, C, E, Q, D, hN, hM, hNM, hC, hD, hprime, hmass,
    hCM, hsmall, hbudget, hErr, hQ, hquality, hQdef, hDdef⟩ :=
      exists_fixedMultiplicity_parameters
  have hfinite : ∀ᶠ y : ℕ in atTop,
      fixedMultiplicityFiniteLower r M y ≤ epsilonR r y (2 * y) := by
    filter_upwards
        [eventually_ge_atTop (fordConstructionScale M 1),
         (tendsto_fordScaleDepth_atTop M).eventually (eventually_ge_atTop 2),
         eventually_fordConstructionBound_atom r M]
      with y hyScaleOne hkTwo hatom
    let K := fordScaleDepth M y
    have hK : 2 ≤ K := hkTwo
    have hKpos : 0 < K := by omega
    have hyScale : fordConstructionScale M K ≤ y :=
      fordScaleDepth_scale_le hyScaleOne
    have hNB : N ≤ fordConstructionBound M K :=
      hNM.trans (fordConstructionBound_ge_M hKpos)
    have hmassK : ∀ i : Fin K,
        |primeBlockMass (M + i) - Real.log 2| ≤
          C / (2 : ℝ) ^ (M + i.val) := by
      intro i
      exact hmass (M + i) (Nat.le_add_right M i)
    have hhalf : ∀ i : Fin K,
        Real.log 2 / 2 ≤ primeBlockMass (M + i) := by
      intro i
      have hi := hmassK i
      have hpow : (2 : ℝ) ^ M ≤ (2 : ℝ) ^ (M + i.val) := by
        rw [pow_add]
        exact le_mul_of_one_le_right (by positivity)
          (one_le_pow₀ (by norm_num))
      have hCi : C / (2 : ℝ) ^ (M + i.val) ≤
          C / (2 : ℝ) ^ M := by
        exact div_le_div_of_nonneg_left hC.le (by positivity) hpow
      have hlower := (abs_le.mp hi).1
      linarith
    have henergy : fixedLowerPrefixEnergyMoment K ≤
        D * ((K : ℝ) ^ K / ((K + 1).factorial : ℝ)) := by
      rw [hDdef]
      exact fixedLowerPrefixEnergyMoment_le_scale (by omega)
    have hraw := fordFixedMultiplicitySized_finite_lower
      (M := M) (N := N) (k := K) (r := r) (y := y)
      (C := C) (E := E) (Q := Q) (D := D)
      (by omega) hK hr hN hNM hC.le hD hprime hmass hsmall
      hbudget hhalf hErr hQ hquality hQdef henergy hyScale hNB hatom
    simpa only [fixedMultiplicityFiniteLower, fixedMultiplicityCore]
      using hraw
  have hbig := fordFixedMultiplicityDepthDensityModel_isBigO_finiteLower r M
  rcases hbig.bound with ⟨C₀, hC₀⟩
  let B : ℝ := |C₀| + 1
  let c : ℝ := B⁻¹
  have hB : 0 < B := by dsimp [B]; positivity
  have hc : 0 < c := inv_pos.mpr hB
  have hevent : ∀ᶠ y : ℕ in atTop,
      c * fordFixedMultiplicityDepthDensityModel r M y ≤
        epsilonR r y (2 * y) := by
    filter_upwards [hfinite, hC₀,
      eventually_fordFixedMultiplicityDepthDensityModel_pos r M]
      with y hfin hbound hmodel
    have hraw0 : 0 ≤ fixedMultiplicityFiniteLower r M y := by
      dsimp [fixedMultiplicityFiniteLower]
      exact mul_nonneg (smallPrimeEulerDensity_nonneg _)
        (mul_nonneg (by positivity)
          (fixedMultiplicityCore_nonneg r (fordScaleDepth M y)))
    have hCB : C₀ ≤ B := by
      dsimp [B]
      linarith [le_abs_self C₀]
    have hmodelRaw : fordFixedMultiplicityDepthDensityModel r M y ≤
        B * fixedMultiplicityFiniteLower r M y := by
      have h0 : fordFixedMultiplicityDepthDensityModel r M y ≤
          C₀ * fixedMultiplicityFiniteLower r M y := by
        simpa only [Real.norm_eq_abs, abs_of_pos hmodel,
          abs_of_nonneg hraw0] using hbound
      exact h0.trans (mul_le_mul_of_nonneg_right hCB hraw0)
    calc
      c * fordFixedMultiplicityDepthDensityModel r M y ≤
          c * (B * fixedMultiplicityFiniteLower r M y) :=
        mul_le_mul_of_nonneg_left hmodelRaw hc.le
      _ = fixedMultiplicityFiniteLower r M y := by
        dsimp [c]
        field_simp [hB.ne']
      _ ≤ epsilonR r y (2 * y) := hfin
  rw [eventually_atTop] at hevent
  obtain ⟨Y, hY⟩ := hevent
  exact ⟨M, c, Y, hc, hY⟩

end Erdos446
