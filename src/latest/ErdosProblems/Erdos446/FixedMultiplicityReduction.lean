/-
Copyright (c) 2026 The Formal Conjectures Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Formal Conjectures Authors
-/

import ErdosProblems.Erdos446.FixedMultiplicityAsymptotic
import ErdosProblems.Erdos446.FixedMultiplicityTransfer

/-!
# Erdős Problem 446: reduction of fixed multiplicity to the isolated model

This module states the exact remaining finite-count output of Ford's
isolated-divisor construction and proves that it implies
`FixedMultiplicityPrefixLower`.  The proof uses the fixed-`r` model
asymptotic and the already formalized dyadic upper estimate; no additional
number theory is hidden in the reduction.
-/

namespace Erdos446

open Filter Real Asymptotics
open scoped Topology

/-- The finite prefix-count estimate produced by the isolated-divisor
construction before comparison with the union count. -/
def FixedMultiplicityModelPrefixLower
    (r M : ℕ) (c : ℝ) (Y : ℕ) : Prop :=
  ∀ y : ℕ, Y ≤ y → ∀ X : ℕ, y * y ≤ X →
    c * (X : ℝ) * fordFixedMultiplicityDepthDensityModel r M y ≤
      (exactDivisorPrefixCount r X y (2 * y) : ℝ)

/-- The density-level output of Ford's isolated-divisor construction.

This is the natural interface for the fixed-multiplicity argument: for each
fixed `y`, Ford's sieve is followed by a limit in the ambient counting
variable.  Unlike `FixedMultiplicityModelPrefixLower`, it does not impose an
unneeded uniform lower cutoff on that ambient variable. -/
def FixedMultiplicityModelDensityLower
    (r M : ℕ) (c : ℝ) (Y : ℕ) : Prop :=
  ∀ y : ℕ, Y ≤ y →
    c * fordFixedMultiplicityDepthDensityModel r M y ≤
      epsilonR r y (2 * y)

/-- A Theta-equivalence between two eventually positive functions supplies
an eventual pointwise lower comparison with a positive constant. -/
theorem exists_const_mul_le_of_isTheta_of_eventually_pos
    {f g : ℕ → ℝ}
    (hf : ∀ᶠ n : ℕ in atTop, 0 < f n)
    (hg : ∀ᶠ n : ℕ in atTop, 0 < g n)
    (hTheta : f =Θ[atTop] g) :
    ∃ d : ℝ, 0 < d ∧ ∀ᶠ n : ℕ in atTop, d * g n ≤ f n := by
  rcases hTheta.2.bound with ⟨C, hC⟩
  let D : ℝ := |C| + 1
  let d : ℝ := D⁻¹
  have hD : 0 < D := by dsimp [D]; positivity
  have hd : 0 < d := inv_pos.mpr hD
  refine ⟨d, hd, ?_⟩
  filter_upwards [hf, hg, hC] with n hfn hgn hCn
  have hCD : C ≤ D := by
    dsimp [D]
    linarith [le_abs_self C]
  have hnorm : g n ≤ C * f n := by
    simpa only [Real.norm_eq_abs, abs_of_pos hgn, abs_of_pos hfn] using hCn
  have hDnorm : g n ≤ D * f n :=
    hnorm.trans (mul_le_mul_of_nonneg_right hCD hfn.le)
  calc
    d * g n ≤ d * (D * f n) := mul_le_mul_of_nonneg_left hDnorm hd.le
    _ = f n := by dsimp [d]; field_simp [hD.ne']

/-- The exact finite isolated-divisor model estimate implies Ford's uniform
fixed-multiplicity prefix comparison. -/
theorem exists_fixedMultiplicityPrefixLower_of_model
    {r M : ℕ} {cR cUnion CUnion : ℝ} {YR YUnion : ℕ}
    (hr : 1 ≤ r) (hcR : 0 < cR) (hCUnion : 0 < CUnion)
    (hUnion : DyadicPrefixBounds cUnion CUnion YUnion)
    (hR : FixedMultiplicityModelPrefixLower r M cR YR) :
    ∃ c : ℝ, ∃ Y : ℕ, 0 < c ∧ 1 ≤ Y ∧
      FixedMultiplicityPrefixLower r c Y := by
  have hmodelTheta :=
    fordFixedMultiplicityDepthDensityModel_isTheta_growth446 hr M
  obtain ⟨d, hd, hmodelLower⟩ :=
    exists_const_mul_le_of_isTheta_of_eventually_pos
      (eventually_fordFixedMultiplicityDepthDensityModel_pos r M)
      (eventually_growthDenominator446_pos.mono fun n hn ↦ inv_pos.mpr hn)
      hmodelTheta
  rw [eventually_atTop] at hmodelLower
  obtain ⟨YModel, hYModel⟩ := hmodelLower
  let c : ℝ := cR * d / CUnion
  let Y : ℕ := max 1 (max YModel (max YR YUnion))
  have hc : 0 < c := by dsimp [c]; positivity
  have hYone : 1 ≤ Y := le_max_left _ _
  refine ⟨c, Y, hc, hYone, ?_⟩
  intro y hy X hX
  have hyModel : YModel ≤ y :=
    (le_max_left YModel (max YR YUnion)).trans
      ((le_max_right 1 (max YModel (max YR YUnion))).trans hy)
  have hyR : YR ≤ y :=
    (le_max_left YR YUnion).trans
      ((le_max_right YModel (max YR YUnion)).trans
        ((le_max_right 1 (max YModel (max YR YUnion))).trans hy))
  have hyUnion : YUnion ≤ y :=
    (le_max_right YR YUnion).trans
      ((le_max_right YModel (max YR YUnion)).trans
        ((le_max_right 1 (max YModel (max YR YUnion))).trans hy))
  have hUpper := (hUnion y hyUnion X hX).2
  have hExact := hR y hyR X hX
  have hModel := hYModel y hyModel
  have hXR : 0 ≤ (X : ℝ) := Nat.cast_nonneg X
  have hscale :
      cR * d * ((X : ℝ) * growth446 y) ≤
        cR * (X : ℝ) * fordFixedMultiplicityDepthDensityModel r M y := by
    calc
      cR * d * ((X : ℝ) * growth446 y) =
          (cR * (X : ℝ)) * (d * growth446 y) := by ring
      _ ≤ (cR * (X : ℝ)) *
          fordFixedMultiplicityDepthDensityModel r M y :=
        mul_le_mul_of_nonneg_left hModel (mul_nonneg hcR.le hXR)
      _ = cR * (X : ℝ) *
          fordFixedMultiplicityDepthDensityModel r M y := by ring
  calc
    c * (divisorPrefixCount X y (2 * y) : ℝ) ≤
        c * (CUnion * (X : ℝ) * growth446 y) :=
      mul_le_mul_of_nonneg_left hUpper hc.le
    _ = cR * d * ((X : ℝ) * growth446 y) := by
      dsimp [c]
      field_simp [hCUnion.ne']
    _ ≤ cR * (X : ℝ) *
        fordFixedMultiplicityDepthDensityModel r M y := hscale
    _ ≤ (exactDivisorPrefixCount r X y (2 * y) : ℝ) := hExact

/-- A density lower bound by the fixed-multiplicity model gives Ford's
eventual comparison with the union density as soon as the already needed
sharp union upper bound is available.

The proof is only asymptotic bookkeeping.  In particular, the sole
number-theoretic input on the exact-multiplicity side is
`FixedMultiplicityModelDensityLower`; no finite-prefix uniformity is hidden
in this reduction. -/
theorem exists_eventually_epsilon_mul_le_epsilonR_of_modelDensity
    {r M : ℕ} {cR : ℝ} {YR : ℕ}
    (hr : 1 ≤ r) (hcR : 0 < cR)
    (hUpper : (fun y : ℕ ↦ epsilon y (2 * y)) =O[atTop] growth446)
    (hR : FixedMultiplicityModelDensityLower r M cR YR) :
    ∃ c : ℝ, 0 < c ∧
      ∀ᶠ y : ℕ in atTop,
        c * epsilon y (2 * y) ≤ epsilonR r y (2 * y) := by
  have hmodelTheta :=
    fordFixedMultiplicityDepthDensityModel_isTheta_growth446 hr M
  obtain ⟨d, hd, hmodelLower⟩ :=
    exists_const_mul_le_of_isTheta_of_eventually_pos
      (eventually_fordFixedMultiplicityDepthDensityModel_pos r M)
      (eventually_growthDenominator446_pos.mono fun n hn ↦ inv_pos.mpr hn)
      hmodelTheta
  rcases hUpper.bound with ⟨C, hC⟩
  let D : ℝ := |C| + 1
  let c : ℝ := cR * d / D
  have hD : 0 < D := by dsimp [D]; positivity
  have hc : 0 < c := by dsimp [c]; positivity
  refine ⟨c, hc, ?_⟩
  filter_upwards [hmodelLower, hC, eventually_ge_atTop YR,
      eventually_growthDenominator446_pos]
    with y hmodel hCy hyR hgrowthDen
  have heps0 : 0 ≤ epsilon y (2 * y) := epsilon_nonneg _ _
  have hgrowth : 0 < growth446 y := inv_pos.mpr hgrowthDen
  have hCD : C ≤ D := by
    dsimp [D]
    linarith [le_abs_self C]
  have hepsUpper : epsilon y (2 * y) ≤ D * growth446 y := by
    have hepsC : epsilon y (2 * y) ≤ C * growth446 y := by
      simpa only [Real.norm_eq_abs, abs_of_nonneg heps0,
        abs_of_pos hgrowth] using hCy
    exact hepsC.trans
      (mul_le_mul_of_nonneg_right hCD hgrowth.le)
  have hscaled :
      c * epsilon y (2 * y) ≤ cR * d * growth446 y := by
    calc
      c * epsilon y (2 * y) ≤ c * (D * growth446 y) :=
        mul_le_mul_of_nonneg_left hepsUpper hc.le
      _ = cR * d * growth446 y := by
        dsimp [c]
        field_simp [hD.ne']
  calc
    c * epsilon y (2 * y) ≤ cR * d * growth446 y := hscaled
    _ = cR * (d * growth446 y) := by ring
    _ ≤ cR * fordFixedMultiplicityDepthDensityModel r M y :=
      mul_le_mul_of_nonneg_left hmodel hcR.le
    _ ≤ epsilonR r y (2 * y) := hR y hyR

/-- Direct density form of the fixed-multiplicity reduction, packaged with
the literal open-interval conclusion and the failure of little-oh. -/
theorem fixedMultiplicity_resolution_of_modelDensity
    {r M : ℕ} {cR : ℝ} {YR : ℕ}
    (hr : 1 ≤ r) (hcR : 0 < cR)
    (hTheta : (fun y : ℕ ↦ epsilon y (2 * y)) =Θ[atTop] growth446)
    (hR : FixedMultiplicityModelDensityLower r M cR YR) :
    (∃ c : ℝ, 0 < c ∧
      ∀ᶠ n : ℕ in atTop, c * delta n ≤ deltaR r n) ∧
      ¬ (fun n : ℕ ↦ deltaR r n) =o[atTop] delta := by
  obtain ⟨c, hc, hhalf⟩ :=
    exists_eventually_epsilon_mul_le_epsilonR_of_modelDensity
      hr hcR hTheta.1 hR
  have hopen := eventually_deltaR_lower_of_epsilonR_lower hc hTheta hhalf
  refine ⟨⟨c / 2, half_pos hc, hopen⟩, ?_⟩
  exact deltaR_not_isLittleO_delta_of_eventual_lower (half_pos hc)
    (delta_isTheta_growth446_of_epsilon hTheta) hopen

end Erdos446
