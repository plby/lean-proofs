/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.KSSSPairKernelPower
import ErdosProblems.Erdos207.KSSSConfigurationKernelPower
import ErdosProblems.Erdos207.DyadicMomentFloor

/-! # The concrete active event and its indexed kernel estimates -/

namespace Erdos207

open Finset

noncomputable section

structure KSSSResidualGeometry
    {V : Type*} [Fintype V] [DecidableEq V]
    (Q₀ : Finset (Finset V)) (S : GreedyStateOn V) (E time : ℝ) : Prop where
  pair_card : ∀ P ∈ ksssResidualPairs Q₀ S, P.card = 2
  cover : ∀ P : Finset V, P.card = 2 →
    (availableTrianglesContainingPair S P).Nonempty → P ∈ ksssResidualPairs Q₀ S
  count : ((ksssResidualPairs Q₀ S).card : ℝ) = E * ksssEdgeDensity E time

def KSSSPowerActive
    {V : Type*} [Fintype V] [DecidableEq V]
    (F : ForbiddenFamilyOn V) (Q₀ : Finset (Finset V)) (q b B k t : ℕ)
    (a : ℕ → ℝ) (E A : ℝ) (time : ℕ) (S : GreedyStateOn V) : Prop :=
  KSSSResidualGeometry Q₀ S E time ∧
    KSSSOnTrajectories F S q (ksssResidualPairs Q₀ S) a E A
      ((Fintype.card V : ℝ) / (t : ℝ) ^ ksssPowerErrorExponent b B) B time ∧
    CrudeStateBounds F S q (dyadicCrudeThresholds V t k) ∧
    1 / (t : ℝ) ^ b ≤ ksssEdgeDensity E time

theorem KSSSPowerActive.available_floor
    {V : Type*} [Fintype V] [DecidableEq V]
    {q b B k t Rmin time : ℕ} {F : ForbiddenFamilyOn V} {Q₀ : Finset (Finset V)}
    {a coeff : ℕ → ℝ} {E A : ℝ} {S : GreedyStateOn V}
    (h : KSSSPowerActive F Q₀ q b B k t a E A time S)
    (hE : 0 < E) (hA : 0 < A) (hN : 1 ≤ Fintype.card V) (ht : 32 ≤ t)
    (hscale : t ^ ksssPowerDenominatorExponent q b B k Rmin ≤ Fintype.card V)
    (hEfloor : (Fintype.card V : ℝ) ^ 2 / (t : ℝ) ^ b ≤ E)
    (hratio : (Fintype.card V : ℝ) / (t : ℝ) ^ b ≤ A / E)
    (hratioUpper : A / E ≤ (Fintype.card V : ℝ))
    (ha : ∀ d ∈ ksssOrders q, 0 ≤ a d)
    (hab : ∀ d ∈ ksssOrders q, a d * E ^ d ≤ coeff d)
    (hcoeff : KSSSPowerCoefficientBounds q coeff B t) :
    dyadicMomentFloor (Fintype.card V) t (5 * b + 1) ≤ S.available.card := by
  have hscalar := ksss_scalar_power_bounds q b B k Rmin a coeff E A time (Fintype.card V) t
    hE hA (Nat.cast_nonneg _) (by exact_mod_cast hN) (by exact_mod_cast ht)
    (by exact_mod_cast hscale) hEfloor hratio hratioUpper h.2.2.2 ha hab hcoeff
  have hbound := h.2.1.scalar_availability_lower hscalar h.1.pair_card h.1.cover h.1.count
    (Nat.cast_nonneg _) (by exact_mod_cast (show 0 < t by omega))
  exact dyadicMomentFloor_le_available (Fintype.card V) t (5 * b + 1) S.available.card
    (by omega) hbound

theorem ksssPowerActive_kernelBounds
    {V : Type*} [Fintype V] [DecidableEq V]
    (q n b B k t Rmin : ℕ) (F : ForbiddenFamilyOn V) (Q₀ : Finset (Finset V))
    (a coeff : ℕ → ℝ) (E A sigma : ℝ)
    (hminimal : minimalForbiddenFamily F = F)
    (hpack : ∀ D ∈ F, IsPackingOn D) (hcard : ∀ D ∈ F, 2 ≤ D.card → D.card + 2 ≤ q)
    (hE : 0 < E) (hA : 0 < A) (hN : 1 ≤ Fintype.card V)
    (ht : 32 ≤ t) (hconst : 2 ^ q ≤ t) (hqt : q ≤ t) (hsigma : |sigma| = 1)
    (hscale : t ^ ksssPowerDenominatorExponent q b B k Rmin ≤ Fintype.card V)
    (hEfloor : (Fintype.card V : ℝ) ^ 2 / (t : ℝ) ^ b ≤ E)
    (hratio : (Fintype.card V : ℝ) / (t : ℝ) ^ b ≤ A / E)
    (hratioUpper : A / E ≤ (Fintype.card V : ℝ))
    (hfloor : ∀ i : ℕ, i < n → 1 / (t : ℝ) ^ b ≤ ksssEdgeDensity E i)
    (ha : ∀ d ∈ ksssOrders q, 0 ≤ a d)
    (hab : ∀ d ∈ ksssOrders q, a d * E ^ d ≤ coeff d)
    (hcoeff : KSSSPowerCoefficientBounds q coeff B t)
    (hB : 4 * q ≤ B)
    (hpairBudget : ksssPairDriftCoefficient q coeff + ksssPairTaylorCoefficient (ksssOrders q) coeff ≤
      3 * (B : ℝ))
    (hconfigBudget : ∀ i : CrudeOrderIndex q 4, ksssIndexedConfigurationDriftCoefficient q coeff i +
      ksssConfigurationTaylorCoefficient (ksssOrders q) coeff (i.order - 3) i.chosen ≤ 3 * (B : ℝ) / 2) :
    KSSSIndexedKernelPowerBounds q n F (KSSSPowerActive F Q₀ q b B k t a E A) Q₀ a E A
      ((Fintype.card V : ℝ) / (t : ℝ) ^ ksssPowerErrorExponent b B) B sigma
      (Fintype.card V) t (ksssPowerJumpExponent b k) (ksssPowerVarianceExponent b k) := by
  have hNreal : (1 : ℝ) ≤ Fintype.card V := by exact_mod_cast hN
  have htReal : (32 : ℝ) ≤ t := by exact_mod_cast ht
  have hscalar (i : ℕ) (hi : i < n) :
      KSSSScalarPowerBounds q b B k a E A i (Fintype.card V) t :=
    ksss_scalar_power_bounds q b B k Rmin a coeff E A i (Fintype.card V) t hE hA
      (Nat.cast_nonneg _) hNreal htReal (by exact_mod_cast hscale) hEfloor hratio hratioUpper
      (hfloor i hi) ha hab hcoeff
  apply ksssIndexedKernelPowerBounds_of_oneStep q n t b k F (KSSSPowerActive F Q₀ q b B k t a E A)
    Q₀ a E A _ B sigma (Fintype.card V)
  · intro time htime S _ hactive
    have hbound := hactive.2.1.scalar_availability_lower (hscalar time htime)
      hactive.1.pair_card hactive.1.cover hactive.1.count
      (Nat.cast_nonneg _) (by linarith : (0 : ℝ) < t)
    exact finset_nonempty_of_real_card_lower S.available (by positivity) hbound
  · intro time htime S hS hactive index htracked
    rcases index with P | ⟨i, root⟩
    · exact hactive.2.1.pair_oneStep_power (hscalar time htime) hactive.2.2.1 hS hpack hcard
        hactive.1.pair_card hactive.1.cover hactive.1.count hE hA (Nat.cast_nonneg _) hNreal hratioUpper
        ht hsigma ha hab hcoeff hpairBudget P htracked
    · exact hactive.2.1.configuration_oneStep_power (hscalar time htime) hactive.2.2.1 hminimal hS hpack hcard
        hactive.1.pair_card hactive.1.cover hactive.1.count hE hA (Nat.cast_nonneg _) hN hratioUpper
        ht hconst hqt hsigma hscale (hfloor time htime) hratio ha hab hcoeff hB hconfigBudget i htracked

end

end Erdos207
