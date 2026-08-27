/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.KSSSScalarPowerBounds
import ErdosProblems.Erdos207.RootSelectorDenominatorBudget

/-! # Positive availability and selector counts at actual active states -/

namespace Erdos207

open Finset

noncomputable section

theorem KSSSOnTrajectories.scalar_availability_lower
    {V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {S : GreedyStateOn V} {q b B k : ℕ}
    {Q : Finset (Finset V)} {a : ℕ → ℝ} {E A time N t : ℝ}
    (h : KSSSOnTrajectories F S q Q a E A (N / t ^ ksssPowerErrorExponent b B) B time)
    (hscalar : KSSSScalarPowerBounds q b B k a E A time N t)
    (hQ : ∀ P ∈ Q, P.card = 2)
    (hcover : ∀ P : Finset V, P.card = 2 →
      (availableTrianglesContainingPair S P).Nonempty → P ∈ Q)
    (hQcard : (Q.card : ℝ) = E * ksssEdgeDensity E time)
    (hN : 0 ≤ N) (ht : 0 < t) :
    N ^ 3 / (4 * t ^ (5 * b + 1)) ≤ (S.available.card : ℝ) := by
  have hglobal := h.availability_error hQ hcover
  rw [hQcard] at hglobal
  have hL : 0 ≤ E * ksssEdgeDensity E time := by rw [← hQcard]; positivity
  exact availability_power_lower N t _ _ _ _ b hN ht hL hscalar.clock_lower
    hscalar.pair_lower hscalar.error_small hglobal

theorem KSSSOnTrajectories.scalar_pair_selector_lower
    {V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {S : GreedyStateOn V} {q b B k : ℕ}
    {Q : Finset (Finset V)} {a : ℕ → ℝ} {E A time N t : ℝ}
    (h : KSSSOnTrajectories F S q Q a E A (N / t ^ ksssPowerErrorExponent b B) B time)
    (hscalar : KSSSScalarPowerBounds q b B k a E A time N t)
    (hQ : ∀ P ∈ Q, P.card = 2)
    (hcover : ∀ P : Finset V, P.card = 2 →
      (availableTrianglesContainingPair S P).Nonempty → P ∈ Q)
    (hQcard : (Q.card : ℝ) = E * ksssEdgeDensity E time)
    (hN : 0 < N) (ht : 32 ≤ t) {P : Finset V} (hP : P ∈ Q) :
    N ^ 3 / (6 * t ^ (5 * b + 1)) ≤
      ((S.available \ availableTrianglesContainingPair S P).card : ℝ) := by
  have htpos : 0 < t := by linarith
  have hx : 0 < ksssPairTrajectory (ksssOrders q) a E A time :=
    (by positivity : (0 : ℝ) < N / t ^ (3 * b + 1)).trans_le hscalar.pair_lower
  have hglobal := h.availability_error hQ hcover
  rw [hQcard] at hglobal
  have hbudget := coupled_pair_denominator_budget
    (show 24 ≤ E * ksssEdgeDensity E time by linarith [hscalar.clock_base]) hx
    hscalar.error_small (Nat.cast_nonneg (availableTrianglesContainingPair S P).card)
    (h.1 P hP) hglobal hscalar.pair_clock_error
  have hsub : availableTrianglesContainingPair S P ⊆ S.available := by
    intro T hT
    exact (mem_availableTrianglesContainingPair_iff.mp hT).1
  have hcard : ((S.available \ availableTrianglesContainingPair S P).card : ℝ) =
      (S.available.card : ℝ) - (availableTrianglesContainingPair S P).card := by
    rw [card_sdiff_of_subset hsub, Nat.cast_sub (card_le_card hsub)]
  apply selector_power_lower N t _ _ _ b hN.le htpos hscalar.clock_lower hscalar.pair_lower
  rw [hcard]
  exact hbudget.1

theorem KSSSOnTrajectories.scalar_root_selector_lower
    {V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {S : GreedyStateOn V} {q b B k t : ℕ}
    {Q : Finset (Finset V)} {a coeff : ℕ → ℝ} {E A time N : ℝ}
    (h : KSSSOnTrajectories F S q Q a E A (N / (t : ℝ) ^ ksssPowerErrorExponent b B) B time)
    (hscalar : KSSSScalarPowerBounds q b B k a E A time N t)
    (hcrude : CrudeStateBounds F S q (dyadicCrudeThresholds V t k))
    (hS : GreedyInvariant F S) (hpack : ∀ D ∈ F, IsPackingOn D)
    (hcard : ∀ D ∈ F, 2 ≤ D.card → D.card + 2 ≤ q)
    (hQ : ∀ P ∈ Q, P.card = 2)
    (hcover : ∀ P : Finset V, P.card = 2 →
      (availableTrianglesContainingPair S P).Nonempty → P ∈ Q)
    (hQcard : (Q.card : ℝ) = E * ksssEdgeDensity E time)
    (hE : 0 < E) (hA : 0 < A) (htime : 0 ≤ time) (hN : 0 < N) (ht : 32 ≤ t)
    (ha : ∀ d ∈ ksssOrders q, 0 ≤ a d)
    (hab : ∀ d ∈ ksssOrders q, a d * E ^ d ≤ coeff d)
    (hcoeff : KSSSPowerCoefficientBounds q coeff B t)
    {root : TripleOn V} (hroot : root ∈ S.available) :
    N ^ 3 / (6 * (t : ℝ) ^ (5 * b + 1)) ≤
      ((S.available \ greedyClosedThreats F S root).card : ℝ) := by
  have ht1 : (1 : ℝ) ≤ t := by exact_mod_cast (show 1 ≤ t by omega)
  have htpos : (0 : ℝ) < t := by linarith
  have hb : ∀ d ∈ ksssOrders q, 0 ≤ coeff d := fun d hd ↦
    (mul_nonneg (ha d hd) (pow_nonneg hE.le d)).trans (hab d hd)
  have horders : ∀ d ∈ ksssOrders q, 1 ≤ d := fun d hd ↦ (mem_Icc.mp hd).1
  have hx := ksssPairTrajectory_pos (ksssOrders q) a hE hA hscalar.clock_strict
  have hp := ksssEdgeDensity_pos hE hscalar.clock_strict
  have hH := ksssThreatTrajectory_bounds (ksssOrders q) a coeff horders ha hab
    hE hA htime hscalar.clock_strict
  have hH0 : 0 ≤ ksssThreatTrajectory (ksssOrders q) a E A time := by linarith only [hx, hH.1]
  have hcommon : ((dyadicCrudeThresholds V t k).common : ℝ) ≤
      ksssErrorEnvelope E (N / (t : ℝ) ^ ksssPowerErrorExponent b B) B time := by
    change (t : ℝ) ^ k ≤ _
    exact (pow_le_pow_right₀ ht1 (Nat.le_succ k)).trans hscalar.overlap_error
  have hthreat := h.closed_threat_error hcrude hS hpack hcard hcover
    hscalar.error_two hcommon hroot
  have hglobal := h.availability_error hQ hcover
  rw [hQcard] at hglobal
  have hbudget := root_selector_denominator_budget F S root _ _ _ _
    (ksssThreatCoefficient (ksssOrders q) coeff) ((q : ℝ) + 5)
    (mul_pos hE hp) hx (ksssThreatCoefficient_nonneg (ksssOrders q) coeff hb)
    (by positivity) hscalar.error_small (hcoeff.threat.trans hscalar.clock_base)
    hglobal hthreat (by rw [abs_of_nonneg hH0]; exact hH.2) hscalar.pair_clock_error
  exact selector_power_lower N t _ _ _ b hN.le htpos hscalar.clock_lower
    hscalar.pair_lower hbudget.1

theorem finset_nonempty_of_real_card_lower {α : Type*} (S : Finset α) {r : ℝ}
    (hr : 0 < r) (h : r ≤ (S.card : ℝ)) : S.Nonempty := by
  have hpos : (0 : ℝ) < S.card := hr.trans_le h
  exact card_pos.mp (by exact_mod_cast hpos)

end

end Erdos207
