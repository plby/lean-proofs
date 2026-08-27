/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.RegularizedInitialDegree
import ErdosProblems.Erdos207.KSSSPowerParameters
import ErdosProblems.Erdos207.KSSSDensityHorizon
import ErdosProblems.Erdos207.ExclusiveAbsorbers

/-! # Initial legality and numeric trajectory data for the actual regularized union -/

namespace Erdos207

open Finset

noncomputable section

theorem greedyInvariant_empty_chosen_of_min_two
    {V : Type*} [DecidableEq V] (F : ForbiddenFamilyOn V) (A : TripleSystemOn V)
    (hsize : ∀ C ∈ F, 2 ≤ C.card) :
    GreedyInvariant F ({chosen := ∅, available := A} : GreedyStateOn V) := by
  refine ⟨by simp [IsPackingOn], ?_, ?_⟩
  · intro C hC hCempty
    have hcard := card_le_card hCempty
    have htwo := hsize C hC
    simp only [card_empty] at hcard
    omega
  · intro T _
    refine ⟨by simp, by simpa only [insert_empty_eq] using isPackingOn_singleton T, ?_⟩
    intro C hC hCT
    have hcard := card_le_card hCT
    have htwo := hsize C hC
    simp only [insert_empty_eq, card_singleton] at hcard
    omega

theorem regularizedForbiddenUnion_initial_invariant
    {V I : Type*} [DecidableEq V] [DecidableEq I]
    (e : I ↪ TripleOn V) (q : ℕ) (Lstar : ℕ → Finset (Finset I))
    (huniform : ∀ j ∈ Icc 4 q, ∀ E ∈ Lstar j, E.card = j - 2) (A : TripleSystemOn V) :
    GreedyInvariant (regularizedForbiddenUnion e q Lstar) ({chosen := ∅, available := A} : GreedyStateOn V) :=
  greedyInvariant_empty_chosen_of_min_two _ A (fun C hC ↦ (regularizedForbiddenUnion_order e q Lstar huniform C hC).1)

theorem regularized_ksss_power_parameters
    {V I : Type*} [Fintype V] [Fintype I] [DecidableEq V] [DecidableEq I]
    (e : I ↪ TripleOn V) (q b B k t Rmin : ℕ) (Lstar : ℕ → Finset (Finset I))
    (huniform : ∀ j ∈ Icc 4 q, ∀ E ∈ Lstar j, E.card = j - 2)
    (havoid : ∀ j ∈ Icc 4 q, ∀ E ∈ Lstar j, ∀ C ∈ (Ico 4 j).biUnion Lstar, ¬ C ⊆ E)
    (hpacking : ∀ j ∈ Icc 4 q, ∀ E ∈ Lstar j, IsPackingOn (E.map e))
    (A E : ℝ) (coeff : ℕ → ℝ) (hA : 0 < A) (hE : 0 < E) (hN : 1 ≤ Fintype.card V)
    (ht : 32 ≤ t) (hbinomial : 2 ^ q ≤ t) (horder : q ≤ t)
    (hscale : t ^ ksssPowerDenominatorExponent q b B k Rmin ≤ Fintype.card V)
    (hEupper : E ≤ (Fintype.card V : ℝ) ^ 2)
    (hElower : (Fintype.card V : ℝ) ^ 2 / (t : ℝ) ^ b ≤ E)
    (hratioLower : (Fintype.card V : ℝ) / (t : ℝ) ^ b ≤ A / E)
    (hratioUpper : A / E ≤ (Fintype.card V : ℝ))
    (hdegree : ∀ d ∈ ksssOrders q, (finiteHypergraphMaxDegree (Lstar (d + 3)) : ℝ) ≤ coeff d * (A / E) ^ d)
    (hcoeff : KSSSPowerCoefficientBounds q coeff B t) (henvelope : 4 * q ≤ B)
    (hpair : ksssPairDriftCoefficient q coeff + ksssPairTaylorCoefficient (ksssOrders q) coeff ≤ 3 * (B : ℝ))
    (hconfiguration : ∀ i : CrudeOrderIndex q 4,
      ksssIndexedConfigurationDriftCoefficient q coeff i +
        ksssConfigurationTaylorCoefficient (ksssOrders q) coeff (i.order - 3) i.chosen ≤ 3 * (B : ℝ) / 2) :
    KSSSPowerParameters (regularizedForbiddenUnion e q Lstar) q
      (ksssDensityHorizon E (1 / (t : ℝ) ^ b)) b B k t Rmin
        (regularizedTrajectoryCoefficient Lstar A) coeff E A := by
  have ht1 : (1 : ℝ) ≤ t := by exact_mod_cast (show 1 ≤ t by omega)
  have htime := ksssDensityHorizon_power_bounds E t b (Fintype.card V) hE hEupper ht1
  exact ⟨regularizedForbiddenUnion_minimal e q Lstar huniform havoid,
    regularizedForbiddenUnion_packing e q Lstar hpacking,
    fun C hC _ ↦ (regularizedForbiddenUnion_order e q Lstar huniform C hC).2,
    hE, hA, hN, ht, hbinomial, horder, hscale, htime.1, hElower, hratioLower, hratioUpper, htime.2.1,
    fun d _ ↦ regularizedTrajectoryCoefficient_nonneg Lstar A hA.le d,
    fun d hd ↦ regularizedTrajectoryCoefficient_scaled_le Lstar A E (coeff d) d hA hE (hdegree d hd),
    hcoeff, henvelope, hpair, hconfiguration⟩

end

end Erdos207
