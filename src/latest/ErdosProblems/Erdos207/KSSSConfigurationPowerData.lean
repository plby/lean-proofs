/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.KSSSStateSelectorPower
import ErdosProblems.Erdos207.KSSSConfigurationSlopePower
import ErdosProblems.Erdos207.KSSSDeterministicIncrementPower

/-! # Discharging the configuration count and slope budgets -/

namespace Erdos207

open Finset

noncomputable section

theorem ksss_source_threat_power
    (q B : ℕ) (a coeff : ℕ → ℝ) (E A time N t : ℝ)
    (hE : 0 < E) (hA : 0 < A) (htime : 0 ≤ time) (hclock : 3 * time < E)
    (hN : 0 ≤ N) (hratio : A / E ≤ N)
    (ha : ∀ d ∈ ksssOrders q, 0 ≤ a d)
    (hab : ∀ d ∈ ksssOrders q, a d * E ^ d ≤ coeff d)
    (hcoeff : KSSSPowerCoefficientBounds q coeff B t) :
    0 ≤ ksssThreatTrajectory (ksssOrders q) a E A time ∧
      ksssThreatTrajectory (ksssOrders q) a E A time ≤ t * N := by
  have horders : ∀ d ∈ ksssOrders q, 1 ≤ d := fun d hd ↦ (mem_Icc.mp hd).1
  have hb : ∀ d ∈ ksssOrders q, 0 ≤ coeff d := fun d hd ↦
    (mul_nonneg (ha d hd) (pow_nonneg hE.le d)).trans (hab d hd)
  have hC := ksssThreatCoefficient_nonneg (ksssOrders q) coeff hb
  have hx := ksssPairTrajectory_pos (ksssOrders q) a hE hA hclock
  have hxN := ksssPairTrajectory_le_three_ratio (ksssOrders q) a E A time hE hA.le htime hclock ha
  have hH := ksssThreatTrajectory_bounds (ksssOrders q) a coeff horders ha hab hE hA htime hclock
  refine ⟨by linarith only [hx, hH.1], ?_⟩
  have hcoef : 3 * ksssThreatCoefficient (ksssOrders q) coeff ≤ t := by
    have hq : (0 : ℝ) ≤ q := Nat.cast_nonneg _
    linarith [hcoeff.threat]
  calc
    _ ≤ ksssThreatCoefficient (ksssOrders q) coeff * (3 * N) :=
      hH.2.trans (mul_le_mul_of_nonneg_left (by linarith only [hxN, hratio]) hC)
    _ = (3 * ksssThreatCoefficient (ksssOrders q) coeff) * N := by ring
    _ ≤ t * N := mul_le_mul_of_nonneg_right hcoef hN

theorem ksss_configuration_target_power_of_coefficients
    (q B : ℕ) (a coeff : ℕ → ℝ) (E A time N t : ℝ)
    (hE : 0 < E) (hA : 0 ≤ A) (htime : 0 ≤ time) (hclock : 3 * time < E)
    (hN : 0 ≤ N) (hratio : A / E ≤ N)
    (ha : ∀ d ∈ ksssOrders q, 0 ≤ a d)
    (hab : ∀ d ∈ ksssOrders q, a d * E ^ d ≤ coeff d)
    (hcoeff : KSSSPowerCoefficientBounds q coeff B t) (i : CrudeOrderIndex q 4) :
    ksssConfigurationTrajectory (ksssOrders q) a E A (i.order - 3) i.chosen time ≤
      t * N ^ (i.order - 3 - i.chosen) := by
  have hc := i.budget
  have hj := i.order_le
  have hd : i.order - 3 ∈ ksssOrders q := by simp only [ksssOrders, mem_Icc]; omega
  have hbound := ksssConfigurationTrajectory_le_ambient_power (ksssOrders q) a coeff E A time N
    (i.order - 3) i.chosen hE hA htime hclock ha (ha _ hd) (hab _ hd) (by omega) hratio
  have hcoef : ((i.order - 3).choose i.chosen : ℝ) * coeff (i.order - 3) ≤ t := by
    linarith [(hcoeff.configuration i).1]
  exact hbound.trans (mul_le_mul_of_nonneg_right hcoef (pow_nonneg hN _))

theorem ksss_configuration_slope_power_of_coefficients
    (q b B k : ℕ) (a coeff : ℕ → ℝ) (E A time N t : ℝ)
    (hscalar : KSSSScalarPowerBounds q b B k a E A time N t)
    (hE : 0 < E) (hA : 0 < A) (htime : 0 ≤ time)
    (hN : 0 < N) (ht : 6 ≤ t) (hqt : (q : ℝ) ≤ t) (hratio : A / E ≤ N)
    (ha : ∀ d ∈ ksssOrders q, 0 ≤ a d)
    (hab : ∀ d ∈ ksssOrders q, a d * E ^ d ≤ coeff d)
    (hcoeff : KSSSPowerCoefficientBounds q coeff B t) (i : CrudeOrderIndex q 4) :
    |ksssConfigurationSlope (ksssOrders q) a E A (i.order - 3) i.chosen time| ≤
      N ^ (i.order - 3 - i.chosen - 1) / N * t ^ (5 * b + 6) := by
  have hc := i.budget
  have hj := i.order_le
  have hd : i.order - 3 ∈ ksssOrders q := by simp only [ksssOrders, mem_Icc]; omega
  have hdT : ((i.order - 3 : ℕ) : ℝ) ≤ t := by
    calc
      _ ≤ (q : ℝ) := by exact_mod_cast (show i.order - 3 ≤ q by omega)
      _ ≤ t := hqt
  have horders : ∀ d ∈ ksssOrders q, 1 ≤ d := fun d hd ↦ (mem_Icc.mp hd).1
  have hH := ksss_source_threat_power q B a coeff E A time N t hE hA htime
    hscalar.clock_strict hN.le hratio ha hab hcoeff
  have hcurr := ksss_configuration_target_power_of_coefficients q B a coeff E A time N t
    hE hA.le htime hscalar.clock_strict hN.le hratio ha hab hcoeff i
  cases hi : i.chosen with
  | zero =>
    rw [hi] at hcurr
    simpa only [Nat.sub_zero] using ksssConfigurationSlope_zero_power (ksssOrders q) a E A time N t
      (i.order - 3) b hE hA htime hscalar.clock_strict horders (ha _ hd) (by omega) hN ht hdT
      (by simpa only [Nat.sub_zero] using hcurr) hH.1 hH.2 hscalar.target_floor
  | succ c =>
    rw [hi] at hcurr
    let iprev := crudeOrderIndexOfBudget i.order c hj (show c + 4 ≤ i.order by omega)
    have hprev := ksss_configuration_target_power_of_coefficients q B a coeff E A time N t
      hE hA.le htime hscalar.clock_strict hN.le hratio ha hab hcoeff iprev
    exact ksssConfigurationSlope_succ_power (ksssOrders q) a E A time N t (i.order - 3) c b
      hE hA htime hscalar.clock_strict horders (ha _ hd) (by omega) hN ht hdT
      hprev hcurr hH.1 hH.2 hscalar.target_floor

theorem KSSSOnTrajectories.scalar_threat_upper
    {V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {S : GreedyStateOn V} {q b B k t : ℕ}
    {Q : Finset (Finset V)} {a coeff : ℕ → ℝ} {E A time N : ℝ}
    (h : KSSSOnTrajectories F S q Q a E A (N / (t : ℝ) ^ ksssPowerErrorExponent b B) B time)
    (hscalar : KSSSScalarPowerBounds q b B k a E A time N t)
    (hcrude : CrudeStateBounds F S q (dyadicCrudeThresholds V t k))
    (hS : GreedyInvariant F S) (hpack : ∀ D ∈ F, IsPackingOn D)
    (hcard : ∀ D ∈ F, 2 ≤ D.card → D.card + 2 ≤ q)
    (hcover : ∀ P : Finset V, P.card = 2 →
      (availableTrianglesContainingPair S P).Nonempty → P ∈ Q)
    (hE : 0 < E) (hA : 0 < A) (htime : 0 ≤ time) (hN : 0 ≤ N) (ht : 1 ≤ t)
    (hratio : A / E ≤ N) (ha : ∀ d ∈ ksssOrders q, 0 ≤ a d)
    (hab : ∀ d ∈ ksssOrders q, a d * E ^ d ≤ coeff d)
    (hcoeff : KSSSPowerCoefficientBounds q coeff B t)
    {root : TripleOn V} (hroot : root ∈ S.available) :
    ((greedyClosedThreats F S root).card : ℝ) ≤ (t : ℝ) * N := by
  have ht1 : (1 : ℝ) ≤ t := by exact_mod_cast ht
  have hcommon : ((dyadicCrudeThresholds V t k).common : ℝ) ≤
      ksssErrorEnvelope E (N / (t : ℝ) ^ ksssPowerErrorExponent b B) B time := by
    change (t : ℝ) ^ k ≤ _
    exact (pow_le_pow_right₀ ht1 (Nat.le_succ k)).trans hscalar.overlap_error
  have herror := h.closed_threat_error hcrude hS hpack hcard hcover hscalar.error_two hcommon hroot
  have hb : ∀ d ∈ ksssOrders q, 0 ≤ coeff d := fun d hd ↦
    (mul_nonneg (ha d hd) (pow_nonneg hE.le d)).trans (hab d hd)
  have hC := ksssThreatCoefficient_nonneg (ksssOrders q) coeff hb
  have hcoef : 3 * (ksssThreatCoefficient (ksssOrders q) coeff + ((q : ℝ) + 5)) ≤ t := by
    have hq : (0 : ℝ) ≤ q := Nat.cast_nonneg _
    linarith [hcoeff.threat]
  exact ksss_closed_threat_count_le_ambient (ksssOrders q) a coeff E A _ time N _ ((q : ℝ) + 5) t B
    hE hA htime hscalar.clock_strict (fun d hd ↦ (mem_Icc.mp hd).1) ha hab hN
    (by positivity) hratio hscalar.error_small herror hcoef

end

end Erdos207
