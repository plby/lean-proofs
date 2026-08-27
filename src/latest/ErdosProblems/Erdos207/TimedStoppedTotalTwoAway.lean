/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.GreedyDeletionIncidence
import ErdosProblems.Erdos207.TimedStoppedTwoAway

/-!
# Aggregate two-away control for a timed stopped process

Unlike a maximum two-away cutoff, the total number of ordered available
two-away incidences is a single random variable.  Its first moment is bounded
by summing the one-root moment estimate, and one application of Markov's
inequality controls it without a union bound over all triangles.
-/

namespace Erdos207

open Finset
open scoped BigOperators NNReal

noncomputable section

/-- Dropping availability restrictions on both endpoints only increases the
total two-away count. -/
lemma totalAvailableTwoAwayIncidences_le_sum_all
    {V : Type*} [Fintype V] [DecidableEq V]
    (F : ForbiddenFamilyOn V) (S : GreedyStateOn V) :
    totalAvailableTwoAwayIncidences F S ≤
      ∑ U : TripleOn V,
        (twoAwayForbiddenTriangles F S.chosen U).card := by
  calc
    totalAvailableTwoAwayIncidences F S =
        ∑ U ∈ S.available,
          (availableTwoAwayForbiddenTriangles F S U).card := by
      rw [show totalAvailableTwoAwayIncidences F S =
          ∑ U : S.available,
            (availableTwoAwayForbiddenTriangles F S U.1).card by rfl]
      rw [univ_eq_attach]
      exact sum_attach S.available
        (fun U ↦ (availableTwoAwayForbiddenTriangles F S U).card)
    _ ≤ ∑ U ∈ S.available,
        (twoAwayForbiddenTriangles F S.chosen U).card := by
      apply sum_le_sum
      intro U hU
      apply card_le_card
      exact inter_subset_right
    _ ≤ ∑ U ∈ (univ : Finset (TripleOn V)),
        (twoAwayForbiddenTriangles F S.chosen U).card := by
      exact sum_le_sum_of_subset (subset_univ S.available)
    _ = ∑ U : TripleOn V,
        (twoAwayForbiddenTriangles F S.chosen U).card := by simp

/-- The aggregate first-moment envelope obtained by summing the fixed-root
two-away moment estimate at moment order one. -/
def totalTwoAwayExpectationEnvelope
    {V : Type*} [Fintype V] [DecidableEq V]
    (q M : ℕ) (H : SimpleGraph V) (X : Finset V)
    (B : TripleSystemOn V) : ℝ≥0 :=
  (Fintype.card (TripleOn V) : ℝ≥0) *
    ((twoAwayMomentJointConstant q 1 : ℝ≥0) *
      ((2 : ℝ≥0) ^ twoAwayMomentUnionCutoff q 1 *
        (twoAwayThreatExtensionCoefficient q M H X B : ℕ)))

/-- First moment of the total available two-away incidence count under an
arbitrary timed stopped absorber-greedy law. -/
theorem timedStoppedAbsorberGreedy_totalTwoAwayExpectation_le
    {V : Type*} [Fintype V] [DecidableEq V]
    {q M n D : ℕ} {H : SimpleGraph V} {X : Finset V}
    {B A : TripleSystemOn V}
    (active : ℕ → GreedyStateOn V → Prop)
    (hA2 : HasAbsorberLocalization q M H X B)
    (hD : 0 < D)
    (hfloor : ∀ i S, active i S → D ≤ S.available.card)
    (hratio : (n : ℝ≥0) * (D : ℝ≥0)⁻¹ ≤
      (Fintype.card V + 1 : ℝ≥0)⁻¹) :
    (FiniteLaw.timedStoppedProcessLaw n
      (fun _ ↦ greedyKernel
        (absorberErdosForbiddenConfigurationsOn q B)) active
      (absorberGreedyInitialState
        (absorberErdosForbiddenConfigurationsOn q B) A)).expectation
      (fun z ↦ (totalAvailableTwoAwayIncidences
        (absorberErdosForbiddenConfigurationsOn q B) z.2 : ℝ≥0)) ≤
      totalTwoAwayExpectationEnvelope q M H X B := by
  let F := absorberErdosForbiddenConfigurationsOn q B
  let S₀ := absorberGreedyInitialState F A
  let L := FiniteLaw.timedStoppedProcessLaw n
    (fun _ ↦ greedyKernel F) active S₀
  let c : ℝ≥0 :=
    (twoAwayMomentJointConstant q 1 : ℝ≥0) *
      ((2 : ℝ≥0) ^ twoAwayMomentUnionCutoff q 1 *
        (twoAwayThreatExtensionCoefficient q M H X B : ℕ))
  calc
    L.expectation (fun z ↦
        (totalAvailableTwoAwayIncidences F z.2 : ℝ≥0)) ≤
      L.expectation (fun z ↦
        ∑ U : TripleOn V,
          ((twoAwayForbiddenTriangles F z.2.chosen U).card : ℝ≥0)) := by
      apply L.expectation_mono
      intro z
      exact_mod_cast totalAvailableTwoAwayIncidences_le_sum_all F z.2
    _ = ∑ U : TripleOn V,
        L.expectation (fun z ↦
          ((twoAwayForbiddenTriangles F z.2.chosen U).card : ℝ≥0)) := by
      unfold FiniteLaw.expectation
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro U _hU
      rw [← Finset.mul_sum]
    _ ≤ ∑ _U : TripleOn V, c := by
      apply sum_le_sum
      intro U _hU
      simpa only [pow_one, F, S₀, L, c] using
        (timedStoppedAbsorberGreedy_twoAwayMomentBound
          (K := 0) (s := 1) active U hA2 hD hfloor hratio)
    _ = totalTwoAwayExpectationEnvelope q M H X B := by
      simp [totalTwoAwayExpectationEnvelope, c]

/-- Markov tail for the aggregate available two-away incidence count. -/
theorem timedStoppedAbsorberGreedy_probability_totalTwoAway_gt_le
    {V : Type*} [Fintype V] [DecidableEq V]
    {q M n D I : ℕ} {H : SimpleGraph V} {X : Finset V}
    {B A : TripleSystemOn V}
    (active : ℕ → GreedyStateOn V → Prop)
    (hA2 : HasAbsorberLocalization q M H X B)
    (hD : 0 < D)
    (hfloor : ∀ i S, active i S → D ≤ S.available.card)
    (hratio : (n : ℝ≥0) * (D : ℝ≥0)⁻¹ ≤
      (Fintype.card V + 1 : ℝ≥0)⁻¹) :
    (FiniteLaw.timedStoppedProcessLaw n
      (fun _ ↦ greedyKernel
        (absorberErdosForbiddenConfigurationsOn q B)) active
      (absorberGreedyInitialState
        (absorberErdosForbiddenConfigurationsOn q B) A)).probability
      (fun z ↦ I < totalAvailableTwoAwayIncidences
        (absorberErdosForbiddenConfigurationsOn q B) z.2) ≤
      totalTwoAwayExpectationEnvelope q M H X B /
        ((I + 1 : ℕ) : ℝ≥0) := by
  let F := absorberErdosForbiddenConfigurationsOn q B
  let S₀ := absorberGreedyInitialState F A
  let L := FiniteLaw.timedStoppedProcessLaw n
    (fun _ ↦ greedyKernel F) active S₀
  let Y : FiniteLaw.TimedState (GreedyStateOn V) n → ℝ≥0 := fun z ↦
    (totalAvailableTwoAwayIncidences F z.2 : ℝ≥0)
  have hthreshold : (0 : ℝ≥0) < ((I + 1 : ℕ) : ℝ≥0) := by positivity
  have hevent : (fun z ↦ I < totalAvailableTwoAwayIncidences F z.2) =
      (fun z ↦ (((I + 1 : ℕ) : ℝ≥0) ≤ Y z)) := by
    funext z
    apply propext
    constructor
    · intro h
      change ((I + 1 : ℕ) : ℝ≥0) ≤
        (totalAvailableTwoAwayIncidences F z.2 : ℝ≥0)
      exact_mod_cast (show I + 1 ≤
        totalAvailableTwoAwayIncidences F z.2 by omega)
    · intro h
      change ((I + 1 : ℕ) : ℝ≥0) ≤
        (totalAvailableTwoAwayIncidences F z.2 : ℝ≥0) at h
      have hnat : I + 1 ≤ totalAvailableTwoAwayIncidences F z.2 := by
        exact_mod_cast h
      omega
  rw [show (fun z ↦ I < totalAvailableTwoAwayIncidences F z.2) =
      (fun z ↦ (((I + 1 : ℕ) : ℝ≥0) ≤ Y z)) by exact hevent]
  refine (L.probability_le_expectation_div Y hthreshold).trans ?_
  exact div_le_div_of_nonneg_right
    (by simpa only [L, F, S₀, Y] using
      (timedStoppedAbsorberGreedy_totalTwoAwayExpectation_le
        active hA2 hD hfloor hratio)) (by positivity)

end

end Erdos207
