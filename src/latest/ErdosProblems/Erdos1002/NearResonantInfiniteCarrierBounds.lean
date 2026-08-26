import ErdosProblems.Erdos1002.NearResonantInfiniteCarriers

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Quantitative bounds for the infinite nonzero near-carrier sum

This file connects the dyadic `ENNReal` coefficient-energy estimates to the
actual Hilbert-space sum of every nonzero Bernoulli carrier.  In particular,
the passage from one carrier to infinitely many carriers loses only the
absolutely summable Bernoulli carrier mass and introduces no finite carrier
cutoff.
-/

open Filter MeasureTheory Set
open scoped BigOperators ENNReal Real Topology

namespace Erdos1002

noncomputable section

private theorem nearCarrierLowCommonEnergyBound_ne_top
    (A L : ℝ) (M : ℕ) :
    nearCarrierLowCommonEnergyBound A L M ≠ ∞ := by
  unfold nearCarrierLowCommonEnergyBound
  finiteness

private theorem nearCarrierHighCommonEnergyBound_ne_top
    (a : ℝ) (H : ℕ) :
    nearCarrierHighCommonEnergyBound a H ≠ ∞ := by
  unfold nearCarrierHighCommonEnergyBound
  finiteness

/-- The low-denominator dyadic estimate as a real norm-squared bound for
one physical circle `L²` carrier. -/
theorem eventually_norm_sq_smoothNearPrimitivePoleCarrierTailL2_low_le
    (A ε : ℝ) (hA : 0 < A) (hε : 0 < ε) (hεhalf : ε < 1 / 2) :
    ∀ᶠ L : ℝ in atTop, ∀ (N M : ℕ) (ell : ℤ)
      (ha : 0 < A / L) (haε : A / L ≤ ε / 4),
      0 < N → ell ≠ 0 → Real.exp L = (N : ℝ) →
      (∀ s ∈ nearCarrierDyadicExponents M,
        (2 ^ s : ℕ) / (N : ℝ) ≤
          Real.exp (-L ^ (1 / 3 : ℝ))) →
      ‖smoothNearPrimitivePoleCarrierTailL2
          N ell (A / L) ε 2 (2 ^ (M + 1))
          ha haε‖ ^ 2 ≤
        ‖bernoulliMarkFourierCoefficient ell‖ ^ 2 *
          (nearCarrierLowCommonEnergyBound A L M).toReal := by
  filter_upwards [
      eventually_coefficientEnergy_nearCarrierDyadicTotal_le_coeff_sq_mul
        A ε hA hε hεhalf] with L henergy
  intro N M ell ha haε hN hell hNL hcut
  have hphysical :
      ENNReal.ofReal
          (∫ alpha in (0 : ℝ)..1,
            ‖smoothNearPrimitivePoleCarrierTail
              N ell (A / L) ε 2 (2 ^ (M + 1)) alpha‖ ^ 2) ≤
        ENNReal.ofReal
            (‖bernoulliMarkFourierCoefficient ell‖ ^ 2) *
          nearCarrierLowCommonEnergyBound A L M := by
    rw [← nearCarrierDyadicTotal_eq_tail]
    rw [← coefficientEnergy_nearCarrierDyadicTotalCoefficients_eq_integral
      N M ell (A / L) ε ha haε]
    exact henergy N M ell hN hell hNL hcut
  exact norm_sq_smoothNearPrimitivePoleCarrierTailL2_le_of_ennreal
    N ell (A / L) ε 2 (2 ^ (M + 1)) ha haε
    (nearCarrierLowCommonEnergyBound A L M)
    (nearCarrierLowCommonEnergyBound_ne_top A L M) hphysical

/-- The low-denominator bound after summing every nonzero Bernoulli
carrier in circle `L²`. -/
theorem eventually_norm_smoothNearInfiniteNonzeroCarrierL2_low_le
    (A ε : ℝ) (hA : 0 < A) (hε : 0 < ε) (hεhalf : ε < 1 / 2) :
    ∀ᶠ L : ℝ in atTop, ∀ (N M : ℕ)
      (ha : 0 < A / L) (haε : A / L ≤ ε / 4),
      0 < N → Real.exp L = (N : ℝ) →
      (∀ s ∈ nearCarrierDyadicExponents M,
        (2 ^ s : ℕ) / (N : ℝ) ≤
          Real.exp (-L ^ (1 / 3 : ℝ))) →
      ‖smoothNearInfiniteNonzeroCarrierL2
          N (A / L) ε 2 (2 ^ (M + 1))
          ha haε‖ ≤
        windowCarrierMassConstant *
          Real.sqrt (nearCarrierLowCommonEnergyBound A L M).toReal := by
  filter_upwards [
      eventually_norm_sq_smoothNearPrimitivePoleCarrierTailL2_low_le
        A ε hA hε hεhalf] with L hcarrier
  intro N M ha haε hN hNL hcut
  apply norm_smoothNearInfiniteNonzeroCarrierL2_le
    N (A / L) ε 2 (2 ^ (M + 1)) ha haε
    (ENNReal.toReal_nonneg)
  intro ell
  exact hcarrier N M (ell : ℤ) ha haε hN ell.property hNL hcut

theorem eventually_summable_smoothNearNonzeroCarrierL2Term_low
    (A ε : ℝ) (hA : 0 < A) (hε : 0 < ε) (hεhalf : ε < 1 / 2) :
    ∀ᶠ L : ℝ in atTop, ∀ (N M : ℕ)
      (ha : 0 < A / L) (haε : A / L ≤ ε / 4),
      0 < N → Real.exp L = (N : ℝ) →
      (∀ s ∈ nearCarrierDyadicExponents M,
        (2 ^ s : ℕ) / (N : ℝ) ≤
          Real.exp (-L ^ (1 / 3 : ℝ))) →
      Summable (smoothNearNonzeroCarrierL2Term
        N (A / L) ε 2 (2 ^ (M + 1)) ha haε) := by
  filter_upwards [
      eventually_norm_sq_smoothNearPrimitivePoleCarrierTailL2_low_le
        A ε hA hε hεhalf] with L hcarrier
  intro N M ha haε hN hNL hcut
  apply summable_smoothNearNonzeroCarrierL2Term
    N (A / L) ε 2 (2 ^ (M + 1)) ha haε
    ENNReal.toReal_nonneg
  intro ell
  exact hcarrier N M (ell : ℤ) ha haε hN ell.property hNL hcut

/-- The short high-denominator range as a real norm-squared bound for one
physical circle `L²` carrier. -/
theorem norm_sq_smoothNearPrimitivePoleCarrierTailL2_high_le
    (N S H : ℕ) (ell : ℤ) (a ε : ℝ)
    (hS : 2 ≤ S) (ha : 0 < a) (hε : 0 < ε)
    (haε : a ≤ ε / 4) (hεhalf : ε < 1 / 2) :
    ‖smoothNearPrimitivePoleCarrierTailL2
        N ell a ε ((2 ^ S) / 2) ((2 ^ (S + H)) / 2) ha haε‖ ^ 2 ≤
      ‖bernoulliMarkFourierCoefficient ell‖ ^ 2 *
        (nearCarrierHighCommonEnergyBound a H).toReal := by
  have hphysical :
      ENNReal.ofReal
          (∫ alpha in (0 : ℝ)..1,
            ‖smoothNearPrimitivePoleCarrierTail N ell a ε
              ((2 ^ S) / 2) ((2 ^ (S + H)) / 2) alpha‖ ^ 2) ≤
        ENNReal.ofReal
            (‖bernoulliMarkFourierCoefficient ell‖ ^ 2) *
          nearCarrierHighCommonEnergyBound a H := by
    rw [← nearCarrierDyadicRangeTotal_eq_tail]
    rw [← coefficientEnergy_nearCarrierDyadicRangeTotalCoefficients_eq_integral
      N S H ell a ε ha haε]
    exact
      coefficientEnergy_nearCarrierDyadicRangeTotalCoefficients_le_coeff_sq_mul
        N S H ell a ε hS ha hε haε hεhalf
  exact norm_sq_smoothNearPrimitivePoleCarrierTailL2_le_of_ennreal
    N ell a ε ((2 ^ S) / 2) ((2 ^ (S + H)) / 2) ha haε
    (nearCarrierHighCommonEnergyBound a H)
    (nearCarrierHighCommonEnergyBound_ne_top a H) hphysical

/-- The short high-denominator bound after summing every nonzero Bernoulli
carrier in circle `L²`. -/
theorem norm_smoothNearInfiniteNonzeroCarrierL2_high_le
    (N S H : ℕ) (a ε : ℝ)
    (hS : 2 ≤ S) (ha : 0 < a) (hε : 0 < ε)
    (haε : a ≤ ε / 4) (hεhalf : ε < 1 / 2) :
    ‖smoothNearInfiniteNonzeroCarrierL2 N a ε
        ((2 ^ S) / 2) ((2 ^ (S + H)) / 2) ha haε‖ ≤
      windowCarrierMassConstant *
        Real.sqrt (nearCarrierHighCommonEnergyBound a H).toReal := by
  apply norm_smoothNearInfiniteNonzeroCarrierL2_le
    N a ε ((2 ^ S) / 2) ((2 ^ (S + H)) / 2) ha haε
    ENNReal.toReal_nonneg
  intro ell
  exact norm_sq_smoothNearPrimitivePoleCarrierTailL2_high_le
    N S H (ell : ℤ) a ε hS ha hε haε hεhalf

theorem summable_smoothNearNonzeroCarrierL2Term_high
    (N S H : ℕ) (a ε : ℝ)
    (hS : 2 ≤ S) (ha : 0 < a) (hε : 0 < ε)
    (haε : a ≤ ε / 4) (hεhalf : ε < 1 / 2) :
    Summable (smoothNearNonzeroCarrierL2Term N a ε
      ((2 ^ S) / 2) ((2 ^ (S + H)) / 2) ha haε) := by
  apply summable_smoothNearNonzeroCarrierL2Term
    N a ε ((2 ^ S) / 2) ((2 ^ (S + H)) / 2) ha haε
    ENNReal.toReal_nonneg
  intro ell
  exact norm_sq_smoothNearPrimitivePoleCarrierTailL2_high_le
    N S H (ell : ℤ) a ε hS ha hε haε hεhalf

end

end Erdos1002
