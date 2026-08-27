/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.ScaledExtensionWeight
import ErdosProblems.Erdos207.TimedStoppedPairTwoAway
import ErdosProblems.Erdos207.TimedStoppedTwoAway
import ErdosProblems.Erdos207.TimedStoppedPairAggregateTwoAway
import ErdosProblems.Erdos207.TimedStoppedTotalTwoAway

/-!
# Stopped absorber tails at a scaled selection hazard

These are the three union bounds used by the long initial phase, with its
actual cumulative point hazard.  The older specializations fixed that hazard
at the ambient inverse scale; the power-vortex phase only gives it up to a
fixed-base polynomial factor.
-/

namespace Erdos207

open Finset
open scoped BigOperators NNReal

noncomputable section

theorem timedStoppedAbsorberGreedy_probability_not_pairTwoAwayCutoff_le_local_scaled
    {V : Type*} [Fintype V] [DecidableEq V]
    {q n s D K : ℕ} {B A : TripleSystemOn V}
    (active : ℕ → GreedyStateOn V → Prop)
    (rate scale : ℝ≥0) (hscale : 1 ≤ scale)
    (hscaleRate : rate ≤ scale * (Fintype.card V + 1 : ℝ≥0)⁻¹)
    (hD : 0 < D)
    (hfloor : ∀ i S, active i S → D ≤ S.available.card)
    (hratio : (n : ℝ≥0) * (D : ℝ≥0)⁻¹ ≤ rate) :
    (FiniteLaw.timedStoppedProcessLaw n
      (fun _ ↦ greedyKernel
        (absorberErdosForbiddenConfigurationsOn q B)) active
      (absorberGreedyInitialState
        (absorberErdosForbiddenConfigurationsOn q B) A)).probability
      (fun z ↦ ¬ HasPairTwoAwayCutoff
        (absorberErdosForbiddenConfigurationsOn q B) K z.2) ≤
      (Fintype.card (TripleOn V) : ℝ≥0) *
        (Fintype.card (PairOn V) : ℝ≥0) *
          pairTwoAwayTail q s K
            (scale ^ q *
              (pairTwoAwayThreatExtensionCoefficient q B : ℕ)) := by
  let F := absorberErdosForbiddenConfigurationsOn q B
  let S₀ := absorberGreedyInitialState F A
  let L := FiniteLaw.timedStoppedProcessLaw n
    (fun _ ↦ greedyKernel F) active S₀
  let kappa : ℝ≥0 := scale ^ q *
    (pairTwoAwayThreatExtensionCoefficient q B : ℕ)
  let badAt : (TripleOn V × PairOn V) →
      FiniteLaw.TimedState (GreedyStateOn V) n → Prop :=
    fun x z ↦ K < (pairTwoAwayForbiddenTriangles F z.2.chosen x.1 x.2).card
  have hfixed : ∀ x : TripleOn V × PairOn V,
      L.probability (badAt x) ≤ pairTwoAwayTail q s K kappa := by
    intro x
    let Y : FiniteLaw.TimedState (GreedyStateOn V) n → ℝ≥0 := fun z ↦
      ((pairTwoAwayForbiddenTriangles F z.2.chosen x.1 x.2).card : ℝ≥0) ^ s
    have hthreshold : (0 : ℝ≥0) < (((K + 1 : ℕ) : ℝ≥0) ^ s) := by
      positivity
    have hmono : L.probability (badAt x) ≤
        L.probability (fun z ↦ (((K + 1 : ℕ) : ℝ≥0) ^ s) ≤ Y z) := by
      apply L.probability_mono
      intro z hz
      apply pow_le_pow_left'
      exact_mod_cast (show K + 1 ≤
        (pairTwoAwayForbiddenTriangles F z.2.chosen x.1 x.2).card by
          change K < _ at hz
          omega)
    refine hmono.trans ((L.probability_le_expectation_div Y hthreshold).trans ?_)
    apply (div_le_div_iff_of_pos_right hthreshold).2
    have hmoment : L.expectation Y ≤
        (twoAwayMomentJointConstant q s : ℝ≥0) *
          (((2 : ℝ≥0) ^ twoAwayMomentUnionCutoff q s * kappa) ^ s) := by
      apply pairTwoAwayForbiddenMomentBound L (fun z ↦ z.2.chosen) F
        x.1 x.2 (constantTripleWeight rate)
        (twoAwayMomentJointConstant q s : ℝ≥0) kappa
      · exact fun C hC ↦ card_le_cutoff_of_mem_absorberErdosForbidden hC
      · exact absorberPairTwoAwayThreatRemainder_hasExtensionBound_scaled
          rate scale hscale hscaleRate
      · intro T hTcard
        apply timedStoppedGreedyProcess_probability_subset_chosen_le_weight
          n F active D (twoAwayMomentUnionCutoff q s) rate hD hfloor hratio
          S₀ T
        · simp [S₀, absorberGreedyInitialState]
        · exact hTcard
    simpa [pairTwoAwayTail, kappa] using hmoment
  calc
    L.probability (fun z ↦ ¬ HasPairTwoAwayCutoff F K z.2) ≤
        L.probability (fun z ↦ ∃ x : TripleOn V × PairOn V, badAt x z) := by
      apply L.probability_mono
      intro z hz
      rw [HasPairTwoAwayCutoff] at hz
      push Not at hz
      obtain ⟨U, _hUavailable, P, hP, _hPU, hbad⟩ := hz
      let P' : PairOn V := ⟨P, hP⟩
      refine ⟨(U, P'), ?_⟩
      have hle := available_pair_nonPairTwoAway_card_le_witnesses F z.2 U P'
      have hsubset :
          availableTrianglesContainingPair z.2 P ∩
              nonPairTwoAwayForbiddenTriangles F z.2.chosen U ⊆
            pairTwoAwayForbiddenTriangles F z.2.chosen U P' := by
        intro T hT
        obtain ⟨hTa, hTtwo⟩ := mem_inter.mp hT
        exact mem_inter.mpr
          ⟨mem_universeTriplesContainingPair_iff.mpr
            (mem_availableTrianglesContainingPair_iff.mp hTa).2, hTtwo⟩
      have hcard := card_le_card hsubset
      simpa [badAt, P'] using lt_of_lt_of_le hbad hcard
    _ ≤ ∑ x ∈ (univ : Finset (TripleOn V × PairOn V)),
        L.probability (badAt x) := by
      simpa using L.probability_exists_le
        (univ : Finset (TripleOn V × PairOn V)) badAt
    _ ≤ ∑ _x ∈ (univ : Finset (TripleOn V × PairOn V)),
        pairTwoAwayTail q s K kappa := by
      apply sum_le_sum
      intro x _hx
      exact hfixed x
    _ = (Fintype.card (TripleOn V) : ℝ≥0) *
        (Fintype.card (PairOn V) : ℝ≥0) *
          pairTwoAwayTail q s K kappa := by simp

theorem timedStoppedAbsorberGreedy_probability_not_twoAwayCutoff_le_scaled
    {V : Type*} [Fintype V] [DecidableEq V]
    {q M K n s D : ℕ} {H : SimpleGraph V} {X : Finset V}
    {B A : TripleSystemOn V}
    (active : ℕ → GreedyStateOn V → Prop)
    (hA2 : HasAbsorberLocalization q M H X B)
    (rate scale : ℝ≥0) (hscale : 1 ≤ scale)
    (hscaleRate : rate ≤ scale * (Fintype.card V + 1 : ℝ≥0)⁻¹)
    (hD : 0 < D)
    (hfloor : ∀ i S, active i S → D ≤ S.available.card)
    (hratio : (n : ℝ≥0) * (D : ℝ≥0)⁻¹ ≤ rate) :
    (FiniteLaw.timedStoppedProcessLaw n
      (fun _ ↦ greedyKernel
        (absorberErdosForbiddenConfigurationsOn q B)) active
      (absorberGreedyInitialState
        (absorberErdosForbiddenConfigurationsOn q B) A)).probability
      (fun z ↦ ¬ HasTwoAwayCutoff
        (absorberErdosForbiddenConfigurationsOn q B) K z.2) ≤
      (Fintype.card (TripleOn V) : ℝ≥0) *
        pairTwoAwayTail q s K
          (scale ^ q * (twoAwayThreatExtensionCoefficient q M H X B : ℕ)) := by
  let F := absorberErdosForbiddenConfigurationsOn q B
  let S₀ := absorberGreedyInitialState F A
  let L := FiniteLaw.timedStoppedProcessLaw n
    (fun _ ↦ greedyKernel F) active S₀
  let kappa : ℝ≥0 := scale ^ q *
    (twoAwayThreatExtensionCoefficient q M H X B : ℕ)
  let badAt : TripleOn V →
      FiniteLaw.TimedState (GreedyStateOn V) n → Prop :=
    fun U z ↦ K < (twoAwayForbiddenTriangles F z.2.chosen U).card
  have hfixed : ∀ U : TripleOn V,
      L.probability (badAt U) ≤ pairTwoAwayTail q s K kappa := by
    intro U
    let Y : FiniteLaw.TimedState (GreedyStateOn V) n → ℝ≥0 := fun z ↦
      ((twoAwayForbiddenTriangles F z.2.chosen U).card : ℝ≥0) ^ s
    have hthreshold : (0 : ℝ≥0) < (((K + 1 : ℕ) : ℝ≥0) ^ s) := by
      positivity
    have hmono : L.probability (badAt U) ≤
        L.probability (fun z ↦ (((K + 1 : ℕ) : ℝ≥0) ^ s) ≤ Y z) := by
      apply L.probability_mono
      intro z hz
      apply pow_le_pow_left'
      exact_mod_cast (show K + 1 ≤
        (twoAwayForbiddenTriangles F z.2.chosen U).card by
          change K < _ at hz
          omega)
    refine hmono.trans ((L.probability_le_expectation_div Y hthreshold).trans ?_)
    apply (div_le_div_iff_of_pos_right hthreshold).2
    have hmoment : L.expectation Y ≤
        (twoAwayMomentJointConstant q s : ℝ≥0) *
          (((2 : ℝ≥0) ^ twoAwayMomentUnionCutoff q s * kappa) ^ s) := by
      apply twoAwayForbiddenMomentBound L (fun z ↦ z.2.chosen) F U
        (constantTripleWeight rate)
        (twoAwayMomentJointConstant q s : ℝ≥0) kappa
      · exact fun C hC ↦ card_le_cutoff_of_mem_absorberErdosForbidden hC
      · exact absorberTwoAwayThreatRemainder_hasExtensionBound_scaled
          hA2 rate scale hscale hscaleRate
      · intro T hTcard
        apply timedStoppedGreedyProcess_probability_subset_chosen_le_weight
          n F active D (twoAwayMomentUnionCutoff q s) rate hD hfloor hratio
          S₀ T
        · simp [S₀, absorberGreedyInitialState]
        · exact hTcard
    simpa [pairTwoAwayTail, kappa] using hmoment
  calc
    L.probability (fun z ↦ ¬ HasTwoAwayCutoff F K z.2) ≤
        L.probability (fun z ↦ ∃ U : TripleOn V, badAt U z) := by
      apply L.probability_mono
      intro z hz
      rw [HasTwoAwayCutoff] at hz
      push Not at hz
      obtain ⟨U, _hUavailable, hU⟩ := hz
      exact ⟨U, by simpa [badAt] using hU⟩
    _ ≤ ∑ U ∈ (univ : Finset (TripleOn V)),
        L.probability (badAt U) := by
      simpa using L.probability_exists_le (univ : Finset (TripleOn V)) badAt
    _ ≤ ∑ _U ∈ (univ : Finset (TripleOn V)),
        pairTwoAwayTail q s K kappa := by
      apply sum_le_sum
      intro U _hU
      exact hfixed U
    _ = (Fintype.card (TripleOn V) : ℝ≥0) *
        pairTwoAwayTail q s K kappa := by simp

theorem timedStoppedAbsorberGreedy_probability_not_pairStarTwoAwayIncidenceCutoff_le_scaled
    {V : Type*} [Fintype V] [DecidableEq V]
    {q n s D K : ℕ} {B A : TripleSystemOn V}
    (active : ℕ → GreedyStateOn V → Prop)
    (rate scale : ℝ≥0) (hscale : 1 ≤ scale)
    (hscaleRate : rate ≤ scale * (Fintype.card V + 1 : ℝ≥0)⁻¹)
    (hD : 0 < D)
    (hfloor : ∀ i S, active i S → D ≤ S.available.card)
    (hratio : (n : ℝ≥0) * (D : ℝ≥0)⁻¹ ≤ rate) :
    (FiniteLaw.timedStoppedProcessLaw n
      (fun _ ↦ greedyKernel
        (absorberErdosForbiddenConfigurationsOn q B)) active
      (absorberGreedyInitialState
        (absorberErdosForbiddenConfigurationsOn q B) A)).probability
      (fun z ↦ ¬ HasPairStarTwoAwayIncidenceCutoff
        (absorberErdosForbiddenConfigurationsOn q B) K z.2) ≤
      (Fintype.card (PairOn V) : ℝ≥0) *
        aggregatePairTwoAwayTail q s K
          (scale ^ q *
            ((aggregatePairTwoAwayThreatExtensionCoefficient q B : ℕ) *
              (Fintype.card V + 1 : ℝ≥0) ^ 2)) := by
  let F := absorberErdosForbiddenConfigurationsOn q B
  let S₀ := absorberGreedyInitialState F A
  let L := FiniteLaw.timedStoppedProcessLaw n
    (fun _ ↦ greedyKernel F) active S₀
  let kappa : ℝ≥0 := scale ^ q *
    ((aggregatePairTwoAwayThreatExtensionCoefficient q B : ℕ) *
      (Fintype.card V + 1 : ℝ≥0) ^ 2)
  let badAt : PairOn V →
      FiniteLaw.TimedState (GreedyStateOn V) n → Prop :=
    fun P z ↦ K < pairStarAvailableTwoAwayIncidences F z.2 P.1
  have hfixed : ∀ P : PairOn V,
      L.probability (badAt P) ≤ aggregatePairTwoAwayTail q s K kappa := by
    intro P
    let Y : FiniteLaw.TimedState (GreedyStateOn V) n → ℝ≥0 := fun z ↦
      (pairStarAvailableTwoAwayIncidences F z.2 P.1 : ℝ≥0) ^ s
    have hthreshold : (0 : ℝ≥0) < (((K + 1 : ℕ) : ℝ≥0) ^ s) := by
      positivity
    have hmono : L.probability (badAt P) ≤
        L.probability (fun z ↦ (((K + 1 : ℕ) : ℝ≥0) ^ s) ≤ Y z) := by
      apply L.probability_mono
      intro z hz
      apply pow_le_pow_left'
      exact_mod_cast (show K + 1 ≤
        pairStarAvailableTwoAwayIncidences F z.2 P.1 by
          change K < _ at hz
          omega)
    refine hmono.trans ((L.probability_le_expectation_div Y hthreshold).trans ?_)
    apply (div_le_div_iff_of_pos_right hthreshold).2
    have hmoment : L.expectation Y ≤
        (twoAwayMomentJointConstant q s : ℝ≥0) *
          (((2 : ℝ≥0) ^ twoAwayMomentUnionCutoff q s * kappa) ^ s) := by
      apply pairStarAvailableTwoAwayIncidenceMomentBound L (fun z ↦ z.2) F P
        (constantTripleWeight rate)
        (twoAwayMomentJointConstant q s : ℝ≥0) kappa
      · exact fun C hC ↦ card_le_cutoff_of_mem_absorberErdosForbidden hC
      · exact
          absorberAggregatePairTwoAwayThreatRemainder_hasExtensionBound_scaled
            rate scale hscale hscaleRate
      · intro T hTcard
        apply timedStoppedGreedyProcess_probability_subset_chosen_le_weight
          n F active D (twoAwayMomentUnionCutoff q s) rate hD hfloor hratio
          S₀ T
        · simp [S₀, absorberGreedyInitialState]
        · exact hTcard
    simpa [aggregatePairTwoAwayTail, kappa] using hmoment
  calc
    L.probability
        (fun z ↦ ¬ HasPairStarTwoAwayIncidenceCutoff F K z.2) ≤
        L.probability (fun z ↦ ∃ P : PairOn V, badAt P z) := by
      apply L.probability_mono
      intro z hz
      rw [HasPairStarTwoAwayIncidenceCutoff] at hz
      push Not at hz
      obtain ⟨P, hP, hbad⟩ := hz
      exact ⟨⟨P, hP⟩, hbad⟩
    _ ≤ ∑ P ∈ (univ : Finset (PairOn V)),
        L.probability (badAt P) := by
      simpa using L.probability_exists_le (univ : Finset (PairOn V)) badAt
    _ ≤ ∑ _P ∈ (univ : Finset (PairOn V)),
        aggregatePairTwoAwayTail q s K kappa := by
      apply sum_le_sum
      intro P _hP
      exact hfixed P
    _ = (Fintype.card (PairOn V) : ℝ≥0) *
        aggregatePairTwoAwayTail q s K kappa := by simp

def scaledTotalTwoAwayExpectationEnvelope
    {V : Type*} [Fintype V] [DecidableEq V]
    (q M : ℕ) (H : SimpleGraph V) (X : Finset V)
    (B : TripleSystemOn V) (scale : ℝ≥0) : ℝ≥0 :=
  (Fintype.card (TripleOn V) : ℝ≥0) *
    ((twoAwayMomentJointConstant q 1 : ℝ≥0) *
      ((2 : ℝ≥0) ^ twoAwayMomentUnionCutoff q 1 *
        (scale ^ q *
          (twoAwayThreatExtensionCoefficient q M H X B : ℕ))))

theorem timedStoppedAbsorberGreedy_probability_totalTwoAway_gt_le_scaled
    {V : Type*} [Fintype V] [DecidableEq V]
    {q M n D I : ℕ} {H : SimpleGraph V} {X : Finset V}
    {B A : TripleSystemOn V}
    (active : ℕ → GreedyStateOn V → Prop)
    (hA2 : HasAbsorberLocalization q M H X B)
    (rate scale : ℝ≥0) (hscale : 1 ≤ scale)
    (hscaleRate : rate ≤ scale * (Fintype.card V + 1 : ℝ≥0)⁻¹)
    (hD : 0 < D)
    (hfloor : ∀ i S, active i S → D ≤ S.available.card)
    (hratio : (n : ℝ≥0) * (D : ℝ≥0)⁻¹ ≤ rate) :
    (FiniteLaw.timedStoppedProcessLaw n
      (fun _ ↦ greedyKernel
        (absorberErdosForbiddenConfigurationsOn q B)) active
      (absorberGreedyInitialState
        (absorberErdosForbiddenConfigurationsOn q B) A)).probability
      (fun z ↦ I < totalAvailableTwoAwayIncidences
        (absorberErdosForbiddenConfigurationsOn q B) z.2) ≤
      scaledTotalTwoAwayExpectationEnvelope q M H X B scale /
        ((I + 1 : ℕ) : ℝ≥0) := by
  let F := absorberErdosForbiddenConfigurationsOn q B
  let S₀ := absorberGreedyInitialState F A
  let L := FiniteLaw.timedStoppedProcessLaw n
    (fun _ ↦ greedyKernel F) active S₀
  let kappa : ℝ≥0 := scale ^ q *
    (twoAwayThreatExtensionCoefficient q M H X B : ℕ)
  let c : ℝ≥0 :=
    (twoAwayMomentJointConstant q 1 : ℝ≥0) *
      ((2 : ℝ≥0) ^ twoAwayMomentUnionCutoff q 1 * kappa)
  have hexpectation : L.expectation (fun z ↦
      (totalAvailableTwoAwayIncidences F z.2 : ℝ≥0)) ≤
      scaledTotalTwoAwayExpectationEnvelope q M H X B scale := by
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
        have hmoment := twoAwayForbiddenMomentBound L
          (fun z ↦ z.2.chosen) F U (constantTripleWeight rate)
          (twoAwayMomentJointConstant q 1 : ℝ≥0) kappa
          (fun C hC ↦ card_le_cutoff_of_mem_absorberErdosForbidden hC)
          (absorberTwoAwayThreatRemainder_hasExtensionBound_scaled
            hA2 rate scale hscale hscaleRate)
          (fun T hTcard ↦
            timedStoppedGreedyProcess_probability_subset_chosen_le_weight
              n F active D (twoAwayMomentUnionCutoff q 1) rate hD hfloor
              hratio S₀ T (by simp [S₀, absorberGreedyInitialState])
              hTcard)
        simpa only [pow_one, twoAwayMomentUnionCutoff, one_mul, c] using hmoment
      _ = scaledTotalTwoAwayExpectationEnvelope q M H X B scale := by
        simp [scaledTotalTwoAwayExpectationEnvelope, c, kappa]
  let Y : FiniteLaw.TimedState (GreedyStateOn V) n → ℝ≥0 := fun z ↦
    (totalAvailableTwoAwayIncidences F z.2 : ℝ≥0)
  have hthreshold : (0 : ℝ≥0) < ((I + 1 : ℕ) : ℝ≥0) := by
    positivity
  have hevent : (fun z ↦ I < totalAvailableTwoAwayIncidences F z.2) =
      (fun z ↦ (((I + 1 : ℕ) : ℝ≥0) ≤ Y z)) := by
    funext z
    apply propext
    constructor <;> intro hz
    · change ((I + 1 : ℕ) : ℝ≥0) ≤
        (totalAvailableTwoAwayIncidences F z.2 : ℝ≥0)
      exact_mod_cast (show I + 1 ≤
        totalAvailableTwoAwayIncidences F z.2 by omega)
    · change ((I + 1 : ℕ) : ℝ≥0) ≤
        (totalAvailableTwoAwayIncidences F z.2 : ℝ≥0) at hz
      have hnat : I + 1 ≤ totalAvailableTwoAwayIncidences F z.2 := by
        exact_mod_cast hz
      omega
  rw [hevent]
  refine (L.probability_le_expectation_div Y hthreshold).trans ?_
  exact div_le_div_of_nonneg_right
    (by simpa only [Y] using hexpectation) (by positivity)

end

end Erdos207
