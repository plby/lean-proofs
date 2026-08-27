/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.PairAggregateTwoAwayThreatWeight
import ErdosProblems.Erdos207.TimedStoppedJointInclusion
import ErdosProblems.Erdos207.EnvelopeStoppedTwoAway

/-! # Aggregate pair-star two-away moments for timed stopped laws -/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

def aggregatePairTwoAwayTail
    (q s K : ℕ) (kappa : ℝ≥0) : ℝ≥0 :=
  ((twoAwayMomentJointConstant q s : ℝ≥0) *
    (((2 : ℝ≥0) ^ twoAwayMomentUnionCutoff q s * kappa) ^ s)) /
      (((K + 1 : ℕ) : ℝ≥0) ^ s)

theorem timedStoppedAbsorberGreedy_pairStarTwoAwayIncidenceMomentBound
    {V : Type*} [Fintype V] [DecidableEq V]
    {q n s D : ℕ} {B A : TripleSystemOn V}
    (active : ℕ → GreedyStateOn V → Prop)
    (P : PairOn V) (kappa : ℝ≥0)
    (hkappa : HasExtensionBound
      (fun z : AggregatePairTwoAwayThreatWitness V
        (absorberErdosForbiddenConfigurationsOn q B) P ↦
          aggregatePairTwoAwayThreatRemainder z)
      (constantTripleWeight ((Fintype.card V + 1 : ℝ≥0)⁻¹)) kappa)
    (hD : 0 < D)
    (hfloor : ∀ i S, active i S → D ≤ S.available.card)
    (hratio : (n : ℝ≥0) * (D : ℝ≥0)⁻¹ ≤
      (Fintype.card V + 1 : ℝ≥0)⁻¹) :
    (FiniteLaw.timedStoppedProcessLaw n
      (fun _ ↦ greedyKernel
        (absorberErdosForbiddenConfigurationsOn q B)) active
      (absorberGreedyInitialState
        (absorberErdosForbiddenConfigurationsOn q B) A)).expectation
      (fun z ↦ (pairStarAvailableTwoAwayIncidences
        (absorberErdosForbiddenConfigurationsOn q B) z.2 P.1 : ℝ≥0) ^ s) ≤
      (twoAwayMomentJointConstant q s : ℝ≥0) *
        (((2 : ℝ≥0) ^ twoAwayMomentUnionCutoff q s * kappa) ^ s) := by
  let F := absorberErdosForbiddenConfigurationsOn q B
  let S0 := absorberGreedyInitialState F A
  let L := FiniteLaw.timedStoppedProcessLaw n
    (fun _ ↦ greedyKernel F) active S0
  apply pairStarAvailableTwoAwayIncidenceMomentBound L (fun z ↦ z.2)
    F P (constantTripleWeight ((Fintype.card V + 1 : ℝ≥0)⁻¹))
    (twoAwayMomentJointConstant q s : ℝ≥0) kappa
  · intro C hCF
    exact card_le_cutoff_of_mem_absorberErdosForbidden hCF
  · exact hkappa
  · intro T hTcard
    apply timedStoppedGreedyProcess_probability_subset_chosen_le_weight
      n F active D (twoAwayMomentUnionCutoff q s)
      ((Fintype.card V + 1 : ℝ≥0)⁻¹) hD hfloor hratio S0 T
    · simp [S0, absorberGreedyInitialState]
    · exact hTcard

theorem timedStoppedAbsorberGreedy_probability_pairStarTwoAwayIncidence_gt_le
    {V : Type*} [Fintype V] [DecidableEq V]
    {q n s D K : ℕ} {B A : TripleSystemOn V}
    (active : ℕ → GreedyStateOn V → Prop)
    (P : PairOn V) (kappa : ℝ≥0)
    (hkappa : HasExtensionBound
      (fun z : AggregatePairTwoAwayThreatWitness V
        (absorberErdosForbiddenConfigurationsOn q B) P ↦
          aggregatePairTwoAwayThreatRemainder z)
      (constantTripleWeight ((Fintype.card V + 1 : ℝ≥0)⁻¹)) kappa)
    (hD : 0 < D)
    (hfloor : ∀ i S, active i S → D ≤ S.available.card)
    (hratio : (n : ℝ≥0) * (D : ℝ≥0)⁻¹ ≤
      (Fintype.card V + 1 : ℝ≥0)⁻¹) :
    (FiniteLaw.timedStoppedProcessLaw n
      (fun _ ↦ greedyKernel
        (absorberErdosForbiddenConfigurationsOn q B)) active
      (absorberGreedyInitialState
        (absorberErdosForbiddenConfigurationsOn q B) A)).probability
      (fun z ↦ K < pairStarAvailableTwoAwayIncidences
        (absorberErdosForbiddenConfigurationsOn q B) z.2 P.1) ≤
      aggregatePairTwoAwayTail q s K kappa := by
  let F := absorberErdosForbiddenConfigurationsOn q B
  let S0 := absorberGreedyInitialState F A
  let L := FiniteLaw.timedStoppedProcessLaw n
    (fun _ ↦ greedyKernel F) active S0
  let Y : FiniteLaw.TimedState (GreedyStateOn V) n → ℝ≥0 := fun z ↦
    (pairStarAvailableTwoAwayIncidences F z.2 P.1 : ℝ≥0) ^ s
  have hthreshold : (0 : ℝ≥0) < (((K + 1 : ℕ) : ℝ≥0) ^ s) := by
    positivity
  have hmono : L.probability
      (fun z ↦ K < pairStarAvailableTwoAwayIncidences F z.2 P.1) ≤
      L.probability (fun z ↦ (((K + 1 : ℕ) : ℝ≥0) ^ s) ≤ Y z) := by
    apply L.probability_mono
    intro z hz
    apply pow_le_pow_left'
    exact_mod_cast (show K + 1 ≤
      pairStarAvailableTwoAwayIncidences F z.2 P.1 by omega)
  refine hmono.trans ?_
  refine (L.probability_le_expectation_div Y hthreshold).trans ?_
  apply (div_le_div_iff_of_pos_right hthreshold).2
  simpa [L, F, S0, aggregatePairTwoAwayTail] using
    (timedStoppedAbsorberGreedy_pairStarTwoAwayIncidenceMomentBound
      (s := s) active P kappa hkappa hD hfloor hratio)

theorem timedStoppedAbsorberGreedy_probability_not_pairStarTwoAwayIncidenceCutoff_le
    {V : Type*} [Fintype V] [DecidableEq V]
    {q n s D K : ℕ} {B A : TripleSystemOn V}
    (active : ℕ → GreedyStateOn V → Prop) (kappa : ℝ≥0)
    (hkappa : ∀ P : PairOn V, HasExtensionBound
      (fun z : AggregatePairTwoAwayThreatWitness V
        (absorberErdosForbiddenConfigurationsOn q B) P ↦
          aggregatePairTwoAwayThreatRemainder z)
      (constantTripleWeight ((Fintype.card V + 1 : ℝ≥0)⁻¹)) kappa)
    (hD : 0 < D)
    (hfloor : ∀ i S, active i S → D ≤ S.available.card)
    (hratio : (n : ℝ≥0) * (D : ℝ≥0)⁻¹ ≤
      (Fintype.card V + 1 : ℝ≥0)⁻¹) :
    (FiniteLaw.timedStoppedProcessLaw n
      (fun _ ↦ greedyKernel
        (absorberErdosForbiddenConfigurationsOn q B)) active
      (absorberGreedyInitialState
        (absorberErdosForbiddenConfigurationsOn q B) A)).probability
      (fun z ↦ ¬ HasPairStarTwoAwayIncidenceCutoff
        (absorberErdosForbiddenConfigurationsOn q B) K z.2) ≤
      (Fintype.card (PairOn V) : ℝ≥0) *
        aggregatePairTwoAwayTail q s K kappa := by
  let F := absorberErdosForbiddenConfigurationsOn q B
  let S0 := absorberGreedyInitialState F A
  let L := FiniteLaw.timedStoppedProcessLaw n
    (fun _ ↦ greedyKernel F) active S0
  let badAt : PairOn V → FiniteLaw.TimedState (GreedyStateOn V) n → Prop :=
    fun P z ↦ K < pairStarAvailableTwoAwayIncidences F z.2 P.1
  calc
    L.probability (fun z ↦ ¬ HasPairStarTwoAwayIncidenceCutoff F K z.2) ≤
        L.probability (fun z ↦ ∃ P : PairOn V, badAt P z) := by
      apply L.probability_mono
      intro z hz
      rw [HasPairStarTwoAwayIncidenceCutoff] at hz
      push Not at hz
      obtain ⟨P, hP, hbad⟩ := hz
      exact ⟨⟨P, hP⟩, hbad⟩
    _ ≤ ∑ P ∈ (univ : Finset (PairOn V)), L.probability (badAt P) := by
      simpa using L.probability_exists_le (univ : Finset (PairOn V)) badAt
    _ ≤ ∑ _P ∈ (univ : Finset (PairOn V)),
        aggregatePairTwoAwayTail q s K kappa := by
      apply sum_le_sum
      intro P _hP
      simpa [L, F, S0, badAt] using
        (timedStoppedAbsorberGreedy_probability_pairStarTwoAwayIncidence_gt_le
          (K := K) (s := s) active P kappa (hkappa P) hD hfloor hratio)
    _ = (Fintype.card (PairOn V) : ℝ≥0) *
        aggregatePairTwoAwayTail q s K kappa := by simp

theorem timedStoppedAbsorberGreedy_probability_not_pairStarTwoAwayIncidenceCutoff_le_absorber
    {V : Type*} [Fintype V] [DecidableEq V]
    {q n s D K : ℕ} {B A : TripleSystemOn V}
    (active : ℕ → GreedyStateOn V → Prop)
    (hD : 0 < D)
    (hfloor : ∀ i S, active i S → D ≤ S.available.card)
    (hratio : (n : ℝ≥0) * (D : ℝ≥0)⁻¹ ≤
      (Fintype.card V + 1 : ℝ≥0)⁻¹) :
    (FiniteLaw.timedStoppedProcessLaw n
      (fun _ ↦ greedyKernel
        (absorberErdosForbiddenConfigurationsOn q B)) active
      (absorberGreedyInitialState
        (absorberErdosForbiddenConfigurationsOn q B) A)).probability
      (fun z ↦ ¬ HasPairStarTwoAwayIncidenceCutoff
        (absorberErdosForbiddenConfigurationsOn q B) K z.2) ≤
      (Fintype.card (PairOn V) : ℝ≥0) *
        aggregatePairTwoAwayTail q s K
          ((aggregatePairTwoAwayThreatExtensionCoefficient q B : ℕ) *
            (Fintype.card V + 1 : ℝ≥0) ^ 2) := by
  apply timedStoppedAbsorberGreedy_probability_not_pairStarTwoAwayIncidenceCutoff_le
    active ((aggregatePairTwoAwayThreatExtensionCoefficient q B : ℕ) *
      (Fintype.card V + 1 : ℝ≥0) ^ 2)
  · intro P
    exact absorberAggregatePairTwoAwayThreatRemainder_hasExtensionBound
  · exact hD
  · exact hfloor
  · exact hratio

end

end Erdos207
