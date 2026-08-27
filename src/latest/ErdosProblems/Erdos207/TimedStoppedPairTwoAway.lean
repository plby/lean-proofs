/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.PairTwoAwayAbsorberBound
import ErdosProblems.Erdos207.TimedStoppedJointInclusion
import ErdosProblems.Erdos207.EnvelopeStoppedTwoAway

/-! # Pair-local two-away moments for timed stopped greedy laws -/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

def pairTwoAwayTail (q s K : ℕ) (κ : ℝ≥0) : ℝ≥0 :=
  ((twoAwayMomentJointConstant q s : ℝ≥0) *
    (((2 : ℝ≥0) ^ twoAwayMomentUnionCutoff q s * κ) ^ s)) /
      (((K + 1 : ℕ) : ℝ≥0) ^ s)

/-- Fixed-selector, fixed-pair moment under an abstract pair-local extension
bound. -/
theorem timedStoppedAbsorberGreedy_pairTwoAwayMomentBound
    {V : Type*} [Fintype V] [DecidableEq V]
    {q n s D : ℕ} {B A : TripleSystemOn V}
    (active : ℕ → GreedyStateOn V → Prop)
    (U : TripleOn V) (P : PairOn V) (κ : ℝ≥0)
    (hκ : HasExtensionBound
      (fun z : PairTwoAwayThreatWitness V
        (absorberErdosForbiddenConfigurationsOn q B) U P ↦
          pairTwoAwayThreatRemainder z)
      (constantTripleWeight ((Fintype.card V + 1 : ℝ≥0)⁻¹)) κ)
    (hD : 0 < D)
    (hfloor : ∀ i S, active i S → D ≤ S.available.card)
    (hratio : (n : ℝ≥0) * (D : ℝ≥0)⁻¹ ≤
      (Fintype.card V + 1 : ℝ≥0)⁻¹) :
    (FiniteLaw.timedStoppedProcessLaw n
      (fun _ ↦ greedyKernel
        (absorberErdosForbiddenConfigurationsOn q B)) active
      (absorberGreedyInitialState
        (absorberErdosForbiddenConfigurationsOn q B) A)).expectation
      (fun z ↦ ((pairTwoAwayForbiddenTriangles
        (absorberErdosForbiddenConfigurationsOn q B)
        z.2.chosen U P).card : ℝ≥0) ^ s) ≤
      (twoAwayMomentJointConstant q s : ℝ≥0) *
        (((2 : ℝ≥0) ^ twoAwayMomentUnionCutoff q s * κ) ^ s) := by
  let F := absorberErdosForbiddenConfigurationsOn q B
  let S₀ := absorberGreedyInitialState F A
  let L := FiniteLaw.timedStoppedProcessLaw n
    (fun _ ↦ greedyKernel F) active S₀
  apply pairTwoAwayForbiddenMomentBound L (fun z ↦ z.2.chosen) F U P
    (constantTripleWeight ((Fintype.card V + 1 : ℝ≥0)⁻¹))
    (twoAwayMomentJointConstant q s : ℝ≥0) κ
  · intro C hCF
    exact card_le_cutoff_of_mem_absorberErdosForbidden hCF
  · exact hκ
  · intro T hTcard
    apply timedStoppedGreedyProcess_probability_subset_chosen_le_weight
      n F active D (twoAwayMomentUnionCutoff q s)
      ((Fintype.card V + 1 : ℝ≥0)⁻¹) hD hfloor hratio S₀ T
    · simp [S₀, absorberGreedyInitialState]
    · exact hTcard

/-- Markov tail for one selector/pair index. -/
theorem timedStoppedAbsorberGreedy_probability_pairTwoAway_gt_le
    {V : Type*} [Fintype V] [DecidableEq V]
    {q n s D K : ℕ} {B A : TripleSystemOn V}
    (active : ℕ → GreedyStateOn V → Prop)
    (U : TripleOn V) (P : PairOn V) (κ : ℝ≥0)
    (hκ : HasExtensionBound
      (fun z : PairTwoAwayThreatWitness V
        (absorberErdosForbiddenConfigurationsOn q B) U P ↦
          pairTwoAwayThreatRemainder z)
      (constantTripleWeight ((Fintype.card V + 1 : ℝ≥0)⁻¹)) κ)
    (hD : 0 < D)
    (hfloor : ∀ i S, active i S → D ≤ S.available.card)
    (hratio : (n : ℝ≥0) * (D : ℝ≥0)⁻¹ ≤
      (Fintype.card V + 1 : ℝ≥0)⁻¹) :
    (FiniteLaw.timedStoppedProcessLaw n
      (fun _ ↦ greedyKernel
        (absorberErdosForbiddenConfigurationsOn q B)) active
      (absorberGreedyInitialState
        (absorberErdosForbiddenConfigurationsOn q B) A)).probability
      (fun z ↦ K < (pairTwoAwayForbiddenTriangles
        (absorberErdosForbiddenConfigurationsOn q B)
        z.2.chosen U P).card) ≤
      pairTwoAwayTail q s K κ := by
  let F := absorberErdosForbiddenConfigurationsOn q B
  let S₀ := absorberGreedyInitialState F A
  let L := FiniteLaw.timedStoppedProcessLaw n
    (fun _ ↦ greedyKernel F) active S₀
  let Y : FiniteLaw.TimedState (GreedyStateOn V) n → ℝ≥0 := fun z ↦
    ((pairTwoAwayForbiddenTriangles F z.2.chosen U P).card : ℝ≥0) ^ s
  have hthreshold : (0 : ℝ≥0) < (((K + 1 : ℕ) : ℝ≥0) ^ s) := by
    positivity
  have hmono : L.probability
      (fun z ↦ K < (pairTwoAwayForbiddenTriangles F z.2.chosen U P).card) ≤
      L.probability (fun z ↦ (((K + 1 : ℕ) : ℝ≥0) ^ s) ≤ Y z) := by
    apply L.probability_mono
    intro z hz
    apply pow_le_pow_left'
    exact_mod_cast (show K + 1 ≤
      (pairTwoAwayForbiddenTriangles F z.2.chosen U P).card by omega)
  refine hmono.trans ?_
  have hmarkov := L.probability_le_expectation_div Y hthreshold
  refine hmarkov.trans ?_
  apply (div_le_div_iff_of_pos_right hthreshold).2
  simpa [L, F, S₀, pairTwoAwayTail] using
    (timedStoppedAbsorberGreedy_pairTwoAwayMomentBound
      (s := s) active U P κ hκ hD hfloor hratio)

/-- Union bound over all selectors and all vertex pairs. -/
theorem timedStoppedAbsorberGreedy_probability_not_pairTwoAwayCutoff_le
    {V : Type*} [Fintype V] [DecidableEq V]
    {q n s D K : ℕ} {B A : TripleSystemOn V}
    (active : ℕ → GreedyStateOn V → Prop) (κ : ℝ≥0)
    (hκ : ∀ U : TripleOn V, ∀ P : PairOn V,
      HasExtensionBound
        (fun z : PairTwoAwayThreatWitness V
          (absorberErdosForbiddenConfigurationsOn q B) U P ↦
            pairTwoAwayThreatRemainder z)
        (constantTripleWeight ((Fintype.card V + 1 : ℝ≥0)⁻¹)) κ)
    (hD : 0 < D)
    (hfloor : ∀ i S, active i S → D ≤ S.available.card)
    (hratio : (n : ℝ≥0) * (D : ℝ≥0)⁻¹ ≤
      (Fintype.card V + 1 : ℝ≥0)⁻¹) :
    (FiniteLaw.timedStoppedProcessLaw n
      (fun _ ↦ greedyKernel
        (absorberErdosForbiddenConfigurationsOn q B)) active
      (absorberGreedyInitialState
        (absorberErdosForbiddenConfigurationsOn q B) A)).probability
      (fun z ↦ ¬ HasPairTwoAwayCutoff
        (absorberErdosForbiddenConfigurationsOn q B) K z.2) ≤
      (Fintype.card (TripleOn V) : ℝ≥0) *
        (Fintype.card (PairOn V) : ℝ≥0) *
          pairTwoAwayTail q s K κ := by
  let F := absorberErdosForbiddenConfigurationsOn q B
  let S₀ := absorberGreedyInitialState F A
  let L := FiniteLaw.timedStoppedProcessLaw n
    (fun _ ↦ greedyKernel F) active S₀
  let badAt : (TripleOn V × PairOn V) →
      FiniteLaw.TimedState (GreedyStateOn V) n → Prop :=
    fun x z ↦ K < (pairTwoAwayForbiddenTriangles F z.2.chosen x.1 x.2).card
  calc
    L.probability (fun z ↦ ¬ HasPairTwoAwayCutoff F K z.2) ≤
        L.probability (fun z ↦ ∃ x : TripleOn V × PairOn V, badAt x z) := by
      apply L.probability_mono
      intro z hz
      rw [HasPairTwoAwayCutoff] at hz
      push_neg at hz
      obtain ⟨U, _hUavailable, P, hP, _hPU, hbad⟩ := hz
      let P' : PairOn V := ⟨P, hP⟩
      refine ⟨(U, P'), ?_⟩
      have hle := available_pair_nonPairTwoAway_card_le_witnesses F z.2 U P'
      have himage := card_pairTwoAwayForbiddenTriangles_le_witnesses
        (F := F) (A := z.2.chosen) (U := U) (P := P')
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
        pairTwoAwayTail q s K κ := by
      apply sum_le_sum
      intro x _hx
      simpa [L, F, S₀, badAt] using
        (timedStoppedAbsorberGreedy_probability_pairTwoAway_gt_le
          (K := K) (s := s) active x.1 x.2 κ (hκ x.1 x.2)
            hD hfloor hratio)
    _ = (Fintype.card (TripleOn V) : ℝ≥0) *
        (Fintype.card (PairOn V) : ℝ≥0) *
          pairTwoAwayTail q s K κ := by simp

/-- The concrete pair-local cutoff bound supplied by the exact absorber-bank
decomposition.  Its extension coefficient is independent of ambient padding.
-/
theorem timedStoppedAbsorberGreedy_probability_not_pairTwoAwayCutoff_le_local
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
      (fun z ↦ ¬ HasPairTwoAwayCutoff
        (absorberErdosForbiddenConfigurationsOn q B) K z.2) ≤
      (Fintype.card (TripleOn V) : ℝ≥0) *
        (Fintype.card (PairOn V) : ℝ≥0) *
          pairTwoAwayTail q s K
            (pairTwoAwayThreatExtensionCoefficient q B : ℕ) := by
  apply timedStoppedAbsorberGreedy_probability_not_pairTwoAwayCutoff_le
    active (pairTwoAwayThreatExtensionCoefficient q B : ℕ)
  · intro U P
    exact absorberPairTwoAwayThreatRemainder_hasExtensionBound
  · exact hD
  · exact hfloor
  · exact hratio

end

end Erdos207
