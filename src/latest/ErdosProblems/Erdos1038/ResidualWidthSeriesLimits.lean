import ErdosProblems.Erdos1038.ResidualWidthStrictReference
import Mathlib.Analysis.Normed.Group.Tannery

/-!
# Dominated limits for inverse-width series

The canonical reference mesh changes its finite coordinate type at every
stage.  Tannery's theorem nevertheless applies directly to the resulting
scalar coefficient series.  These wrappers reduce convergence of the full
inverse width and its material derivative to coefficientwise convergence
and one uniform summable majorant.
-/

set_option warningAsError false

open Filter Topology

namespace Erdos1038

noncomputable section

/-- Coefficientwise convergence plus a uniform summable majorant passes the
odd inverse-width series through a changing finite-coordinate limit. -/
theorem tendsto_inverseWidthSeries_of_dominated_coefficients
    (index : ℕ → Type*) [∀ n, Fintype (index n)]
    (alpha reference : ∀ n, index n → ℝ)
    (limitCoefficient majorant : ℕ → ℝ)
    (hmajorant : Summable majorant)
    (hcoefficient : ∀ j, Tendsto
      (fun n ↦ scaledLagrangeCoefficient
        (alpha n) (2 * j + 1) (reference n))
      atTop (nhds (limitCoefficient j)))
    (hdominated : ∀ᶠ n in atTop, ∀ j,
      ‖scaledLagrangeCoefficient
        (alpha n) (2 * j + 1) (reference n)‖ ≤ majorant j) :
    Tendsto
      (fun n ↦ inverseWidthSeries (alpha n) (reference n))
      atTop (nhds (2 * ∑' j, limitCoefficient j)) := by
  have htsum := tendsto_tsum_of_dominated_convergence
    hmajorant hcoefficient hdominated
  simpa only [inverseWidthSeries] using! htsum.const_mul (2 : ℝ)

/-- Directional counterpart of
`tendsto_inverseWidthSeries_of_dominated_coefficients`. -/
theorem tendsto_inverseWidthSeriesDirectional_of_dominated_coefficients
    (index : ℕ → Type*) [∀ n, Fintype (index n)]
    (alpha reference target : ∀ n, index n → ℝ)
    (limitCoefficient majorant : ℕ → ℝ)
    (hmajorant : Summable majorant)
    (hcoefficient : ∀ j, Tendsto
      (fun n ↦ scaledLagrangeCoefficientDirectional
        (alpha n) (2 * j + 1) (reference n) (target n))
      atTop (nhds (limitCoefficient j)))
    (hdominated : ∀ᶠ n in atTop, ∀ j,
      ‖scaledLagrangeCoefficientDirectional
        (alpha n) (2 * j + 1) (reference n) (target n)‖ ≤ majorant j) :
    Tendsto
      (fun n ↦ inverseWidthSeriesDirectional
        (alpha n) (reference n) (target n))
      atTop (nhds (2 * ∑' j, limitCoefficient j)) := by
  have htsum := tendsto_tsum_of_dominated_convergence
    hmajorant hcoefficient hdominated
  simpa only [inverseWidthSeriesDirectional] using!
    htsum.const_mul (2 : ℝ)

/-- A target identification can be supplied separately from the dominated
series argument, which is convenient when the limiting coefficients are
identified by an inverse-branch theorem. -/
theorem tendsto_inverseWidthSeries_of_dominated_coefficients_eq
    (index : ℕ → Type*) [∀ n, Fintype (index n)]
    (alpha reference : ∀ n, index n → ℝ)
    (limitCoefficient majorant : ℕ → ℝ)
    (hmajorant : Summable majorant)
    (hcoefficient : ∀ j, Tendsto
      (fun n ↦ scaledLagrangeCoefficient
        (alpha n) (2 * j + 1) (reference n))
      atTop (nhds (limitCoefficient j)))
    (hdominated : ∀ᶠ n in atTop, ∀ j,
      ‖scaledLagrangeCoefficient
        (alpha n) (2 * j + 1) (reference n)‖ ≤ majorant j)
    {limit : ℝ} (hlimit : 2 * ∑' j, limitCoefficient j = limit) :
    Tendsto
      (fun n ↦ inverseWidthSeries (alpha n) (reference n))
      atTop (nhds limit) := by
  rw [← hlimit]
  exact tendsto_inverseWidthSeries_of_dominated_coefficients
    index alpha reference limitCoefficient majorant
      hmajorant hcoefficient hdominated

/-- Directional target-identification wrapper. -/
theorem tendsto_inverseWidthSeriesDirectional_of_dominated_coefficients_eq
    (index : ℕ → Type*) [∀ n, Fintype (index n)]
    (alpha reference target : ∀ n, index n → ℝ)
    (limitCoefficient majorant : ℕ → ℝ)
    (hmajorant : Summable majorant)
    (hcoefficient : ∀ j, Tendsto
      (fun n ↦ scaledLagrangeCoefficientDirectional
        (alpha n) (2 * j + 1) (reference n) (target n))
      atTop (nhds (limitCoefficient j)))
    (hdominated : ∀ᶠ n in atTop, ∀ j,
      ‖scaledLagrangeCoefficientDirectional
        (alpha n) (2 * j + 1) (reference n) (target n)‖ ≤ majorant j)
    {limit : ℝ} (hlimit : 2 * ∑' j, limitCoefficient j = limit) :
    Tendsto
      (fun n ↦ inverseWidthSeriesDirectional
        (alpha n) (reference n) (target n))
      atTop (nhds limit) := by
  rw [← hlimit]
  exact tendsto_inverseWidthSeriesDirectional_of_dominated_coefficients
    index alpha reference target limitCoefficient majorant
      hmajorant hcoefficient hdominated

end

end Erdos1038
