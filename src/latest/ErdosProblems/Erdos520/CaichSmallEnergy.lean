import ErdosProblems.Erdos520.ExactCaichEnergyComparison
import ErdosProblems.Erdos520.MertensProduct

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open Finset MeasureTheory Set
open scoped BigOperators

namespace Erdos
namespace Problem520

/-!
# Caich's small-energy estimate reduced to Harper's low moment

The finite Euler normalizer is now comparable with `log y` unconditionally.
This file therefore combines the exact energy martingale, localized Doob,
and the two-sided Mertens comparison.  The sole remaining input is Harper's
deep `2/3`-moment estimate at the first cutoff.
-/

/-- The explicit constant in the elementary Mertens upper bound. -/
noncomputable def energyMertensUpperConstant : ℝ :=
  Real.exp
    (1 - Real.log (Real.log 2) +
      2 * (Real.log 4 + 4) / Real.log 2)

theorem energyMertensUpperConstant_pos :
    0 < energyMertensUpperConstant := Real.exp_pos _

/-- Constant comparing every scheduled Caich energy with the exact energy. -/
noncomputable def caichToExactEnergyConstant : ℝ :=
  2 * Real.pi * energyMertensUpperConstant

theorem caichToExactEnergyConstant_pos :
    0 < caichToExactEnergyConstant := by
  exact mul_pos (mul_pos (by norm_num) Real.pi_pos)
    energyMertensUpperConstant_pos

/-- The Mertens upper bound makes the comparison with exact energy
unconditional. -/
theorem caichNormalizedEnergy_le_unconditional_exact
    {ell K y₀ y : ℕ} (hy₀ : 2 ≤ y₀) (hy₀y : y₀ ≤ y)
    (omega : Omega) :
    caichNormalizedEnergy ell K y₀ y omega ≤
      caichToExactEnergyConstant * exactNormalizedEnergy omega y := by
  apply caichNormalizedEnergy_le_mul_exactNormalizedEnergy
    (show 1 < y₀ by omega) hy₀y
  simpa only [energyMertensUpperConstant] using!
    (primeEnergyNormalizer_le_mertensConstant_mul_log
      (hy₀.trans hy₀y))

/-- At the first cutoff the reverse comparison is also unconditional; the
constant simplifies to `1 / pi`. -/
theorem exactNormalizedEnergy_le_unconditional_caich_initial
    {ell K y₀ : ℕ} (hy₀ : 2 ≤ y₀) (omega : Omega) :
    exactNormalizedEnergy omega y₀ ≤
      (1 / Real.pi) * caichNormalizedEnergy ell K y₀ y₀ omega := by
  have h := exactNormalizedEnergy_le_mul_caichNormalizedEnergy_initial
    (ell := ell) (K := K) (show 1 < y₀ by omega)
    (c := (1 / 2 : ℝ)) (by norm_num)
    (half_mul_log_le_primeEnergyNormalizer hy₀) omega
  convert! h using 1
  field_simp [Real.pi_pos.ne']

/-- Harper's initial `2/3` moment now transfers with no Mertens hypothesis. -/
theorem integral_scheduledExactEnergy_twoThird_le_of_harperMoment
    (y : ℕ → ℕ) {ell K y₀ : ℕ} (hyInit : y 0 = y₀)
    (hy₀ : 2 ≤ y₀) {C : ℝ}
    (hHarper :
      (∫ omega,
        caichNormalizedEnergy ell K y₀ y₀ omega ^ ((2 : ℝ) / 3) ∂μ) ≤
          caichInitialEnergyMomentBudget ell K C) :
    (∫ omega,
      scheduledExactNormalizedEnergy y 0 omega ^ ((2 : ℝ) / 3) ∂μ) ≤
      caichInitialEnergyMomentBudget ell K
        ((1 / Real.pi) ^ ((2 : ℝ) / 3) * C) := by
  have h :=
    integral_scheduledExactNormalizedEnergy_rpow_twoThird_le_caichBudget
      y hyInit (show 1 < y₀ by omega)
      (c := (1 / 2 : ℝ)) (by norm_num)
      (half_mul_log_le_primeEnergyNormalizer hy₀) hHarper
  convert! h using 1
  congr 2
  field_simp [Real.pi_pos.ne']

/-- Caich's small-energy maximal estimate, conditional only on the precise
Harper initial moment.  All martingale, localization, Mertens, and exponent
bookkeeping has been discharged. -/
theorem measureReal_scheduledExactEnergy_max_le_of_harperMoment
    (y : ℕ → ℕ) (hy : Monotone y) {y₀ : ℕ} (hyInit : y 0 = y₀)
    (hy₀ : 2 ≤ y₀) (n ell K : ℕ) (T1 C : ℝ)
    (hell : 0 < ell) (hT1 : 0 < T1)
    (hHarper :
      (∫ omega,
        caichNormalizedEnergy ell K y₀ y₀ omega ^ ((2 : ℝ) / 3) ∂μ) ≤
          caichInitialEnergyMomentBudget ell K C) :
    μ.real {omega |
        caichMaximalEnergyThreshold ell K T1 ≤
          finiteRunningMax (scheduledExactNormalizedEnergy y) n omega} ≤
      T1 ^ (-(1 : ℝ) / 4) +
        ((1 / Real.pi) ^ ((2 : ℝ) / 3) * C) *
          T1 ^ (-(1 : ℝ) / 6) := by
  exact measureReal_scheduledExactNormalizedEnergy_max_le_caich
    y hy n ell K T1
      ((1 / Real.pi) ^ ((2 : ℝ) / 3) * C)
      hell hT1
      (integral_scheduledExactEnergy_twoThird_le_of_harperMoment
        y hyInit hy₀ hHarper)

/-- Caich's energy sampled along a deterministic cutoff schedule. -/
noncomputable def scheduledCaichNormalizedEnergy
    (ell K : ℕ) (y : ℕ → ℕ) (j : ℕ) (omega : Omega) : ℝ :=
  caichNormalizedEnergy ell K (y 0) (y j) omega

/-- Running maxima of the scheduled Caich energies are controlled by the
running maximum of the exact martingale energy. -/
theorem finiteRunningMax_scheduledCaich_le_exact
    (ell K : ℕ) (y : ℕ → ℕ) (hy : Monotone y)
    (hy₀ : 2 ≤ y 0) (n : ℕ) (omega : Omega) :
    finiteRunningMax (scheduledCaichNormalizedEnergy ell K y) n omega ≤
      caichToExactEnergyConstant *
        finiteRunningMax (scheduledExactNormalizedEnergy y) n omega := by
  unfold finiteRunningMax
  apply Finset.sup'_le _ _
  intro j hj
  have hjn : j ≤ n := by simpa using! Finset.mem_range.mp hj
  have hpoint : scheduledCaichNormalizedEnergy ell K y j omega ≤
      caichToExactEnergyConstant *
        scheduledExactNormalizedEnergy y j omega := by
    exact caichNormalizedEnergy_le_unconditional_exact hy₀
      (hy (Nat.zero_le j)) omega
  exact hpoint.trans <| mul_le_mul_of_nonneg_left
    (Finset.le_sup' (fun k => scheduledExactNormalizedEnergy y k omega) hj)
    caichToExactEnergyConstant_pos.le

/-- The scheduled Caich-energy crossing event is contained in the exact
martingale crossing event, after multiplying the threshold by the explicit
comparison constant. -/
theorem measureReal_scheduledCaichEnergy_max_le_of_exact
    (ell K : ℕ) (y : ℕ → ℕ) (hy : Monotone y)
    (hy₀ : 2 ≤ y 0) (n : ℕ) {u R : ℝ}
    (hExact :
      μ.real {omega |
          u ≤ finiteRunningMax (scheduledExactNormalizedEnergy y) n omega} ≤ R) :
    μ.real {omega |
        caichToExactEnergyConstant * u ≤
          finiteRunningMax (scheduledCaichNormalizedEnergy ell K y) n omega} ≤
      R := by
  apply (measureReal_mono ?_).trans hExact
  intro omega homega
  have hmax := finiteRunningMax_scheduledCaich_le_exact
    ell K y hy hy₀ n omega
  have hmul : caichToExactEnergyConstant * u ≤
      caichToExactEnergyConstant *
        finiteRunningMax (scheduledExactNormalizedEnergy y) n omega :=
    homega.trans hmax
  exact (mul_le_mul_iff_of_pos_left caichToExactEnergyConstant_pos).mp hmul

/-- Final paper-facing small-energy estimate.  The threshold now controls
Caich's own damped energies, while the probability budget still has the
sharp `T1^(-1/6)` form. -/
theorem measureReal_scheduledCaichEnergy_max_le_of_harperMoment
    (y : ℕ → ℕ) (hy : Monotone y) {y₀ : ℕ} (hyInit : y 0 = y₀)
    (hy₀ : 2 ≤ y₀) (n ell K : ℕ) (T1 C : ℝ)
    (hell : 0 < ell) (hT1 : 0 < T1)
    (hHarper :
      (∫ omega,
        caichNormalizedEnergy ell K y₀ y₀ omega ^ ((2 : ℝ) / 3) ∂μ) ≤
          caichInitialEnergyMomentBudget ell K C) :
    μ.real {omega |
        caichToExactEnergyConstant *
            caichMaximalEnergyThreshold ell K T1 ≤
          finiteRunningMax
            (scheduledCaichNormalizedEnergy ell K y) n omega} ≤
      T1 ^ (-(1 : ℝ) / 4) +
        ((1 / Real.pi) ^ ((2 : ℝ) / 3) * C) *
          T1 ^ (-(1 : ℝ) / 6) := by
  subst y₀
  apply measureReal_scheduledCaichEnergy_max_le_of_exact
    ell K y hy hy₀ n (u := caichMaximalEnergyThreshold ell K T1)
  exact measureReal_scheduledExactEnergy_max_le_of_harperMoment
    y hy rfl hy₀ n ell K T1 C hell hT1 hHarper

end Problem520
end Erdos
