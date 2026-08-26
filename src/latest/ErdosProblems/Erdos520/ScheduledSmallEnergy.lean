import ErdosProblems.Erdos520.CaichSmallEnergy
import ErdosProblems.Erdos520.QuadraticVariationReduction

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open Filter Finset MeasureTheory Set
open scoped Topology

namespace Erdos
namespace Problem520

/-!
# Small-energy failures for a scale-dependent cutoff schedule

`CaichSmallEnergy` proves the exact one-scale maximal estimate.  This file
packages it for endpoints that change with the outer scale and performs the
summability comparison once and for all.
-/

/-- Caich's normalized energy attached to a two-parameter cutoff schedule. -/
noncomputable def caichScheduledEnergy
    (K : ℕ) (y : ℕ → ℕ → ℕ) (ell j : ℕ) (omega : Omega) : ℝ :=
  caichNormalizedEnergy ell K (y ell 0) (y ell j) omega

/-- Failure of the maximal-energy estimate at one outer scale. -/
def caichScheduledEnergyFailure
    (K : ℕ) (J : ℕ → ℕ) (y : ℕ → ℕ → ℕ)
    (T1 : ℕ → ℝ) (ell : ℕ) : Set Omega :=
  {omega |
    caichToExactEnergyConstant *
          caichMaximalEnergyThreshold ell K (T1 ell) ≤
      caichBlockEnergyMax J (caichScheduledEnergy K y) ell omega}

theorem measureReal_caichScheduledEnergyFailure_le
    {K : ℕ} (J : ℕ → ℕ) (y : ℕ → ℕ → ℕ)
    (T1 : ℕ → ℝ) {C : ℝ} {ell : ℕ}
    (hy : Monotone (y ell)) (hy₀ : 2 ≤ y ell 0)
    (hell : 0 < ell) (hT1 : 0 < T1 ell)
    (hmoment :
      (∫ omega,
        caichNormalizedEnergy ell K (y ell 0) (y ell 0) omega ^
          ((2 : ℝ) / 3) ∂μ) ≤
        caichInitialEnergyMomentBudget ell K C) :
    μ.real (caichScheduledEnergyFailure K J y T1 ell) ≤
      T1 ell ^ (-(1 : ℝ) / 4) +
        ((1 / Real.pi) ^ ((2 : ℝ) / 3) * C) *
          T1 ell ^ (-(1 : ℝ) / 6) := by
  have h := measureReal_scheduledCaichEnergy_max_le_of_harperMoment
    (y ell) hy (y₀ := y ell 0) rfl hy₀ (J ell) ell K (T1 ell) C
      hell hT1 hmoment
  simpa only [caichScheduledEnergyFailure, caichBlockEnergyMax,
    caichScheduledEnergy, scheduledCaichNormalizedEnergy] using! h

/-- A summable explicit scalar budget makes the actual maximal-energy
failure probabilities summable. -/
theorem summable_measureReal_caichScheduledEnergyFailure
    {K : ℕ} (J : ℕ → ℕ) (y : ℕ → ℕ → ℕ)
    (T1 : ℕ → ℝ) {C : ℝ}
    (hy : ∀ ell, Monotone (y ell))
    (hy₀ : ∀ ell, 2 ≤ y ell 0)
    (hT1 : ∀ᶠ ell : ℕ in atTop, 0 < T1 ell)
    (hmoment : ∀ᶠ ell : ℕ in atTop,
      (∫ omega,
        caichNormalizedEnergy ell K (y ell 0) (y ell 0) omega ^
          ((2 : ℝ) / 3) ∂μ) ≤
        caichInitialEnergyMomentBudget ell K C)
    (hbudget : Summable fun ell =>
      T1 ell ^ (-(1 : ℝ) / 4) +
        ((1 / Real.pi) ^ ((2 : ℝ) / 3) * C) *
          T1 ell ^ (-(1 : ℝ) / 6)) :
    Summable fun ell =>
      μ.real (caichScheduledEnergyFailure K J y T1 ell) := by
  apply hbudget.of_norm_bounded_eventually_nat
  filter_upwards [hmoment, hT1, eventually_ge_atTop (1 : ℕ)]
    with ell hmom hT1ell hell
  rw [Real.norm_eq_abs, abs_of_nonneg measureReal_nonneg]
  exact measureReal_caichScheduledEnergyFailure_le
    J y T1 (hy ell) (hy₀ ell) (by omega) hT1ell hmom

/-- Borel--Cantelli form of the scale-dependent small-energy estimate. -/
theorem ae_eventually_not_caichScheduledEnergyFailure
    {K : ℕ} (J : ℕ → ℕ) (y : ℕ → ℕ → ℕ)
    (T1 : ℕ → ℝ) {C : ℝ}
    (hy : ∀ ell, Monotone (y ell))
    (hy₀ : ∀ ell, 2 ≤ y ell 0)
    (hT1 : ∀ᶠ ell : ℕ in atTop, 0 < T1 ell)
    (hmoment : ∀ᶠ ell : ℕ in atTop,
      (∫ omega,
        caichNormalizedEnergy ell K (y ell 0) (y ell 0) omega ^
          ((2 : ℝ) / 3) ∂μ) ≤
        caichInitialEnergyMomentBudget ell K C)
    (hbudget : Summable fun ell =>
      T1 ell ^ (-(1 : ℝ) / 4) +
        ((1 / Real.pi) ^ ((2 : ℝ) / 3) * C) *
          T1 ell ^ (-(1 : ℝ) / 6)) :
    ∀ᵐ omega ∂μ, ∀ᶠ ell : ℕ in atTop,
      omega ∉ caichScheduledEnergyFailure K J y T1 ell :=
  ae_eventually_notMem_of_summable_measureReal
    (summable_measureReal_caichScheduledEnergyFailure
      J y T1 hy hy₀ hT1 hmoment hbudget)

end Problem520
end Erdos
