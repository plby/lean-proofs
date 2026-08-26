import ErdosProblems.Erdos520.CaichThresholdBudget

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open Filter Finset MeasureTheory Set
open scoped Topology

namespace Erdos
namespace Problem520

/-!
# Small energy with a rescaled outer index

The gap-free integer geometry uses its analytic scale `L ell = ell + S`,
where `S` is a fixed finite shift.  `ScheduledSmallEnergy` treats the special
case `L ell = ell`; this file proves the same result with an explicit scale
map and then closes the scalar summability budget for every fixed shift.
-/

/-- Caich's normalized energy when the analytic scale is `L ell`. -/
noncomputable def caichRescaledScheduledEnergy
    (L : ℕ → ℕ) (K : ℕ) (y : ℕ → ℕ → ℕ)
    (ell j : ℕ) (omega : Omega) : ℝ :=
  caichNormalizedEnergy (L ell) K (y ell 0) (y ell j) omega

/-- Failure of the rescaled maximal-energy estimate at one outer index. -/
def caichRescaledScheduledEnergyFailure
    (L : ℕ → ℕ) (K : ℕ) (J : ℕ → ℕ) (y : ℕ → ℕ → ℕ)
    (T1 : ℕ → ℝ) (ell : ℕ) : Set Omega :=
  {omega |
    caichToExactEnergyConstant *
          caichMaximalEnergyThreshold (L ell) K (T1 (L ell)) ≤
      caichBlockEnergyMax J (caichRescaledScheduledEnergy L K y) ell omega}

theorem measureReal_caichRescaledScheduledEnergyFailure_le
    (L : ℕ → ℕ) {K : ℕ} (J : ℕ → ℕ) (y : ℕ → ℕ → ℕ)
    (T1 : ℕ → ℝ) {C : ℝ} {ell : ℕ}
    (hy : Monotone (y ell)) (hy₀ : 2 ≤ y ell 0)
    (hL : 0 < L ell) (hT1 : 0 < T1 (L ell))
    (hmoment :
      (∫ omega,
        caichNormalizedEnergy (L ell) K (y ell 0) (y ell 0) omega ^
          ((2 : ℝ) / 3) ∂μ) ≤
        caichInitialEnergyMomentBudget (L ell) K C) :
    μ.real (caichRescaledScheduledEnergyFailure L K J y T1 ell) ≤
      T1 (L ell) ^ (-(1 : ℝ) / 4) +
        ((1 / Real.pi) ^ ((2 : ℝ) / 3) * C) *
          T1 (L ell) ^ (-(1 : ℝ) / 6) := by
  have h := measureReal_scheduledCaichEnergy_max_le_of_harperMoment
    (y ell) hy (y₀ := y ell 0) rfl hy₀ (J ell) (L ell) K
      (T1 (L ell)) C hL hT1 hmoment
  simpa only [caichRescaledScheduledEnergyFailure, caichBlockEnergyMax,
    caichRescaledScheduledEnergy, scheduledCaichNormalizedEnergy] using! h

/-- Generic rescaled scheduled small-energy theorem. -/
theorem summable_measureReal_caichRescaledScheduledEnergyFailure
    (L : ℕ → ℕ) {K : ℕ} (J : ℕ → ℕ) (y : ℕ → ℕ → ℕ)
    (T1 : ℕ → ℝ) {C : ℝ}
    (hy : ∀ ell, Monotone (y ell))
    (hy₀ : ∀ ell, 2 ≤ y ell 0)
    (hL : ∀ᶠ ell : ℕ in atTop, 0 < L ell)
    (hT1 : ∀ᶠ ell : ℕ in atTop, 0 < T1 (L ell))
    (hmoment : ∀ᶠ ell : ℕ in atTop,
      (∫ omega,
        caichNormalizedEnergy (L ell) K (y ell 0) (y ell 0) omega ^
          ((2 : ℝ) / 3) ∂μ) ≤
        caichInitialEnergyMomentBudget (L ell) K C)
    (hbudget : Summable fun ell =>
      T1 (L ell) ^ (-(1 : ℝ) / 4) +
        ((1 / Real.pi) ^ ((2 : ℝ) / 3) * C) *
          T1 (L ell) ^ (-(1 : ℝ) / 6)) :
    Summable fun ell =>
      μ.real (caichRescaledScheduledEnergyFailure L K J y T1 ell) := by
  apply hbudget.of_norm_bounded_eventually_nat
  filter_upwards [hmoment, hL, hT1] with ell hmom hLell hT1ell
  rw [Real.norm_eq_abs, abs_of_nonneg measureReal_nonneg]
  exact measureReal_caichRescaledScheduledEnergyFailure_le
    L J y T1 (hy ell) (hy₀ ell) hLell hT1ell hmom

/-- The exact `T₁` budget remains summable after any fixed natural shift. -/
theorem summable_caichSmallEnergyT1_budget_shift
    (S : ℕ) {C : ℝ} (hC : 0 ≤ C) :
    Summable fun ell : ℕ =>
      caichSmallEnergyT1 (ell + S) ^ (-(1 : ℝ) / 4) +
        C * caichSmallEnergyT1 (ell + S) ^ (-(1 : ℝ) / 6) := by
  exact (summable_nat_add_iff S).2
    (summable_caichSmallEnergyT1_budget hC)

/-- Positivity of the exact `T₁` parameter after a shift by at least two. -/
theorem caichSmallEnergyT1_add_pos {S ell : ℕ} (hS : 2 ≤ S) :
    0 < caichSmallEnergyT1 (ell + S) :=
  caichSmallEnergyT1_pos (by omega)

/-- Fully specialized fixed-shift summability theorem. -/
theorem summable_measureReal_caichShiftedScheduledEnergyFailure
    {K S : ℕ} (hS : 2 ≤ S) (J : ℕ → ℕ) (y : ℕ → ℕ → ℕ)
    {C : ℝ} (hC : 0 ≤ C)
    (hy : ∀ ell, Monotone (y ell))
    (hy₀ : ∀ ell, 2 ≤ y ell 0)
    (hmoment : ∀ᶠ ell : ℕ in atTop,
      (∫ omega,
        caichNormalizedEnergy (ell + S) K (y ell 0) (y ell 0) omega ^
          ((2 : ℝ) / 3) ∂μ) ≤
        caichInitialEnergyMomentBudget (ell + S) K C) :
    Summable fun ell => μ.real
      (caichRescaledScheduledEnergyFailure (fun n => n + S) K J y
        caichSmallEnergyT1 ell) := by
  apply summable_measureReal_caichRescaledScheduledEnergyFailure
    (fun n => n + S) J y caichSmallEnergyT1 hy hy₀
  · filter_upwards with ell
    omega
  · filter_upwards with ell
    exact caichSmallEnergyT1_add_pos hS
  · exact hmoment
  · exact summable_caichSmallEnergyT1_budget_shift S (by positivity)

end Problem520
end Erdos
