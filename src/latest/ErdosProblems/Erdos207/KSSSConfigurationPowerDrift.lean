/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.KSSSConfigurationPowerData
import ErdosProblems.Erdos207.KSSSOneStepPowerBounds

/-! # Discharging the configuration drift budgets with the fixed power hierarchy -/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

theorem minimalForbiddenFamily_idempotent
    {V : Type*} [DecidableEq V] (F : ForbiddenFamilyOn V) :
    minimalForbiddenFamily (minimalForbiddenFamily F) = minimalForbiddenFamily F := by
  classical
  apply Subset.antisymm (minimalForbiddenFamily_subset _)
  intro C hC
  apply mem_filter.mpr
  refine ⟨hC, ?_⟩
  intro D hD hDC
  exact (eq_of_mem_minimalForbiddenFamily_of_subset hD hC hDC).symm.subset

theorem KSSSOnTrajectories.configuration_power_drift
    {V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {S : GreedyStateOn V} {q b B k t Rmin : ℕ}
    {Q : Finset (Finset V)} {a coeff : ℕ → ℝ} {E A time : ℝ}
    (h : KSSSOnTrajectories F S q Q a E A
      ((Fintype.card V : ℝ) / (t : ℝ) ^ ksssPowerErrorExponent b B) B time)
    (hscalar : KSSSScalarPowerBounds q b B k a E A time (Fintype.card V) t)
    (hcrude : CrudeStateBounds F S q (dyadicCrudeThresholds V t k))
    (hminimal : minimalForbiddenFamily F = F)
    (hS : GreedyInvariant F S) (hpack : ∀ D ∈ F, IsPackingOn D)
    (hcard : ∀ D ∈ F, 2 ≤ D.card → D.card + 2 ≤ q)
    (hQ : ∀ P ∈ Q, P.card = 2)
    (hcover : ∀ P : Finset V, P.card = 2 →
      (availableTrianglesContainingPair S P).Nonempty → P ∈ Q)
    (hQcard : (Q.card : ℝ) = E * ksssEdgeDensity E time)
    (hE : 0 < E) (hA : 0 < A) (htime : 0 ≤ time) (hN : 1 ≤ Fintype.card V)
    (ht : 32 ≤ t) (hconst : 2 ^ q ≤ t)
    (hscale : t ^ ksssPowerDenominatorExponent q b B k Rmin ≤ Fintype.card V)
    (hfloor : 1 / (t : ℝ) ^ b ≤ ksssEdgeDensity E time)
    (hratio : (Fintype.card V : ℝ) / (t : ℝ) ^ b ≤ A / E)
    (ha : ∀ d ∈ ksssOrders q, 0 ≤ a d)
    (hab : ∀ d ∈ ksssOrders q, a d * E ^ d ≤ coeff d)
    (hcoeff : KSSSPowerCoefficientBounds q coeff B t)
    (i : CrudeOrderIndex q 4) {root : TripleOn V} (hroot : root ∈ S.available)
    (hR : (S.available \ greedyClosedThreats F S root).Nonempty) :
    |(restrictedGreedyKernel F S (S.available \ greedyClosedThreats F S root) hR).expectationReal
        (fun S' ↦ ((greedyConfigurationClass (forbiddenFamilyOfOrder F i.order) S' root i.chosen).card : ℝ) -
          (greedyConfigurationClass (forbiddenFamilyOfOrder F i.order) S root i.chosen).card) -
      ksssConfigurationSlope (ksssOrders q) a E A (i.order - 3) i.chosen time| ≤
      ksssIndexedConfigurationDriftCoefficient q coeff i *
        ksssConfigurationErrorEnvelope E A
          ((Fintype.card V : ℝ) / (t : ℝ) ^ ksssPowerErrorExponent b B) B
          (i.order - 3 - i.chosen - 1) time / (E * ksssEdgeDensity E time) := by
  have ht1 : (1 : ℝ) ≤ t := by exact_mod_cast (show 1 ≤ t by omega)
  have hcommon : ((dyadicCrudeThresholds V t k).common : ℝ) ≤
      ksssErrorEnvelope E ((Fintype.card V : ℝ) / (t : ℝ) ^ ksssPowerErrorExponent b B) B time := by
    change (t : ℝ) ^ k ≤ _
    exact (pow_le_pow_right₀ ht1 (Nat.le_succ k)).trans hscalar.overlap_error
  have hoverlap : 9 + 6 * (dyadicCrudeThresholds V t k).pair + (dyadicCrudeThresholds V t k).common ≤
      ((t ^ (k + 1) : ℕ) : ℝ≥0) := by
    have hpow := power_crude_overlap_le (t : ℝ) k (by exact_mod_cast (show 16 ≤ t by omega))
    have hreal : (9 : ℝ) + 6 * (t : ℝ) ^ k + (t : ℝ) ^ k ≤ (t : ℝ) ^ (k + 1) := by linarith
    dsimp only [dyadicCrudeThresholds]
    exact_mod_cast hreal
  have hK : ((t ^ (k + 1) : ℕ) : ℝ) ≤
      ksssErrorEnvelope E ((Fintype.card V : ℝ) / (t : ℝ) ^ ksssPowerErrorExponent b B) B time := by
    simpa only [Nat.cast_pow] using hscalar.overlap_error
  have hc := i.budget
  have hj := i.order_le
  have hd : i.order - 3 ∈ ksssOrders q := by simp only [ksssOrders, mem_Icc]; omega
  have hjid : i.order - 3 + 3 = i.order := by omega
  cases hi : i.chosen with
  | zero =>
    have hraw := h.configuration_zero_drift_error hcrude hS hpack hcard hQ hcover hQcard
      hE hA (by positivity) htime hscalar.clock_strict ha hab hscalar.error_two hscalar.error_small
      hcommon (hcoeff.threat.trans hscalar.clock_base) hscalar.pair_clock_error hoverlap hK
      (i.order - 3) hd root hroot hR
    simpa only [ksssIndexedConfigurationDriftCoefficient, hi, if_pos rfl, ite_true,
      hjid, Nat.sub_zero] using hraw
  | succ c =>
    have hcrudeMin : CrudeStateBounds (minimalForbiddenFamily F) S q (dyadicCrudeThresholds V t k) := by
      simpa only [hminimal] using hcrude
    have hgap : k + ksssPowerErrorExponent b B + 3 * b * (i.order - c - 4) + 2 ≤
        ksssPowerDenominatorExponent q b B k Rmin := by
      have hg := ksss_power_gain_exponent_gap q b B k Rmin (i.order - c - 5) (by omega)
      have heq : i.order - c - 5 + 1 = i.order - c - 4 := by omega
      simpa only [heq] using hg
    have hgain := hcrudeMin.dyadic_redundant_gain_budget (B := B) i.order c hroot hj (by omega)
      hE htime hscalar.clock_strict ha hab hN (show 1 ≤ t by omega) hscale hconst hgap
      hfloor hratio hcoeff.poisson
    have hidx : i.order - 4 - (c + 1) = i.order - 3 - (c + 1) - 1 := by omega
    simp only [hminimal, hidx] at hgain
    have hraw := h.configuration_succ_drift_error hcrude hS hpack hcard hQ hcover hQcard
      hE hA (by positivity) htime hscalar.clock_strict ha hab hscalar.error_two hscalar.error_small
      hcommon (hcoeff.threat.trans hscalar.clock_base) hscalar.pair_clock_error hoverlap hK
      (i.order - 3) c hd (by omega) root hroot hR (by simpa only [hjid] using hgain)
    simpa only [ksssIndexedConfigurationDriftCoefficient, hi, Nat.succ_ne_zero,
      if_false, Nat.add_sub_cancel, hjid] using hraw

end

end Erdos207
