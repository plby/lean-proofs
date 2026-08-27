/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.KSSSConfigurationPowerData
import ErdosProblems.Erdos207.KSSSOneStepPowerBounds
import ErdosProblems.Erdos207.DyadicConfigurationVariance

/-! # Actual configuration jumps and second moments from the active-state bounds -/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

theorem KSSSOnTrajectories.configuration_raw_power
    {V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {S : GreedyStateOn V} {q b B k t : ℕ}
    {Q : Finset (Finset V)} {a coeff : ℕ → ℝ} {E A time : ℝ}
    (h : KSSSOnTrajectories F S q Q a E A
      ((Fintype.card V : ℝ) / (t : ℝ) ^ ksssPowerErrorExponent b B) B time)
    (hscalar : KSSSScalarPowerBounds q b B k a E A time (Fintype.card V) t)
    (hcrude : CrudeStateBounds F S q (dyadicCrudeThresholds V t k))
    (hS : GreedyInvariant F S) (hpack : ∀ D ∈ F, IsPackingOn D)
    (hcard : ∀ D ∈ F, 2 ≤ D.card → D.card + 2 ≤ q)
    (hQ : ∀ P ∈ Q, P.card = 2)
    (hcover : ∀ P : Finset V, P.card = 2 →
      (availableTrianglesContainingPair S P).Nonempty → P ∈ Q)
    (hQcard : (Q.card : ℝ) = E * ksssEdgeDensity E time)
    (hE : 0 < E) (hA : 0 < A) (htime : 0 ≤ time) (hN : 1 ≤ Fintype.card V)
    (hratio : A / E ≤ (Fintype.card V : ℝ)) (ht : 32 ≤ t) (hconst : 2 ^ q ≤ t) (hqt : q ≤ t)
    (ha : ∀ d ∈ ksssOrders q, 0 ≤ a d)
    (hab : ∀ d ∈ ksssOrders q, a d * E ^ d ≤ coeff d)
    (hcoeff : KSSSPowerCoefficientBounds q coeff B t)
    (i : CrudeOrderIndex q 4) {root : TripleOn V} (hroot : root ∈ S.available) :
    let index : KSSSTrajectoryIndex V q := .inr (i, root)
    (∀ T ∈ ksssTrajectorySelectors F S index,
      |ksssTrajectoryValue F (greedyStep F S T) index - ksssTrajectoryValue F S index| ≤
        (Fintype.card V : ℝ) ^ ksssTrajectoryDimension index * (t : ℝ) ^ (k + 2)) ∧
    ∀ hR : (ksssTrajectorySelectors F S index).Nonempty,
      (restrictedGreedyKernel F S (ksssTrajectorySelectors F S index) hR).expectationReal
        (fun S' ↦ (ksssTrajectoryValue F S' index - ksssTrajectoryValue F S index) ^ 2) ≤
          (Fintype.card V : ℝ) ^ (2 * ksssTrajectoryDimension index) / Fintype.card V *
            (t : ℝ) ^ ksssPowerRawVarianceExponent b k := by
  dsimp only
  let H : ℝ≥0 := t * Fintype.card V
  have hNpos : (0 : ℝ) < Fintype.card V := by exact_mod_cast (show 0 < Fintype.card V by omega)
  have hH : (H : ℝ) ≤ (t : ℝ) * Fintype.card V := by
    simp only [H, NNReal.coe_mul, NNReal.coe_natCast, le_refl]
  have hthreat (T : TripleOn V) (hT : T ∈ S.available) :
      ((greedyClosedThreats F S T).card : ℝ≥0) ≤ H := by
    apply NNReal.coe_le_coe.mp
    exact h.scalar_threat_upper hscalar hcrude hS hpack hcard hcover hE hA htime hNpos.le
      (by omega) hratio ha hab hcoeff hT
  have hcount (j c : ℕ) (hj : j ≤ q) (hc : c + 4 ≤ j) :
      ((greedyConfigurationClass (forbiddenFamilyOfOrder F j) S root c).card : ℝ) ≤
        (t : ℝ) * (Fintype.card V : ℝ) ^ (j - c - 3) := by
    exact h.configuration_count_le_ambient_power hE hA.le (by positivity) htime hscalar.clock_strict
      ha hab hNpos.le hratio hscalar.error_small j c (mem_Icc.mpr ⟨by omega, hj⟩) hc
      (hcoeff.configuration (crudeOrderIndexOfBudget j c hj hc)).1 hroot
  have hden := h.scalar_root_selector_lower hscalar hcrude hS hpack hcard hQ hcover hQcard
    hE hA htime hNpos ht ha hab hcoeff hroot
  have hc := i.budget
  have hj := i.order_le
  constructor
  · intro T hT
    have hTavail : T ∈ S.available := (mem_sdiff.mp hT).1
    cases hi : i.chosen with
    | zero =>
      have hraw := hcrude.dyadic_configuration_zero_jump i.order hj (by omega) H hN
        (by omega) hconst hH hS hpack hroot hT (hthreat T hTavail)
      simpa only [ksssTrajectoryValue, ksssTrajectoryDimension, hi, Nat.sub_zero] using hraw
    | succ c =>
      have hraw := hcrude.dyadic_configuration_succ_jump i.order c hj (by omega) H hN
        (by omega) hconst hH hS hpack hroot hT (hthreat T hTavail)
      have hz : i.order - 4 - (c + 1) = i.order - c - 5 := by omega
      simpa only [ksssTrajectoryValue, ksssTrajectoryDimension, hi, hz] using hraw
  · intro hR
    cases hi : i.chosen with
    | zero =>
      have hcurr := hcount i.order 0 hj (by omega)
      simp only [Nat.sub_zero] at hcurr
      have hraw := hcrude.dyadic_configuration_zero_variance i.order hj (by omega) H hN
        (by omega) hconst hqt hH hS hpack hroot hR hthreat hcurr hden
      simpa only [ksssTrajectoryValue, ksssTrajectoryDimension, ksssTrajectorySelectors,
        ksssPowerRawVarianceExponent, hi, Nat.sub_zero] using hraw
    | succ c =>
      have hcurr := hcount i.order (c + 1) hj (by omega)
      have hcurrExp : i.order - (c + 1) - 3 = i.order - c - 4 := by omega
      rw [hcurrExp] at hcurr
      have hraw := hcrude.dyadic_configuration_succ_variance i.order c hj (by omega) H hN
        (by omega) hconst hqt hH hS hpack hroot hR hthreat (hcount i.order c hj (by omega)) hcurr hden
      have hz : i.order - 4 - (c + 1) = i.order - c - 5 := by omega
      simpa only [ksssTrajectoryValue, ksssTrajectoryDimension, ksssTrajectorySelectors,
        ksssPowerRawVarianceExponent, hi, hz] using hraw

end

end Erdos207
