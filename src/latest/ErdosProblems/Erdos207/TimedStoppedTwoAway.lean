/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.TimedStoppedJointInclusion
import ErdosProblems.Erdos207.EnvelopeStoppedTwoAway

/-!
# Two-away control for an arbitrary timed stopped greedy law

The A2 extension estimate only needs a joint-inclusion bound for the selected
triangles.  A uniform active-region availability floor supplies that bound for
any timed stopping predicate, so the existing moment, Markov, and finite-union
argument transfers verbatim.
-/

namespace Erdos207

open Finset
open scoped BigOperators NNReal

noncomputable section

/-- Moment bound for a fixed two-away root in a timed stopped process. -/
theorem timedStoppedAbsorberGreedy_twoAwayMomentBound
    {V : Type*} [Fintype V] [DecidableEq V]
    {q M K n s D : ℕ} {H : SimpleGraph V} {X : Finset V}
    {B A : TripleSystemOn V}
    (active : ℕ → GreedyStateOn V → Prop) (U : TripleOn V)
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
      (fun z ↦ ((twoAwayForbiddenTriangles
        (absorberErdosForbiddenConfigurationsOn q B)
        z.2.chosen U).card : ℝ≥0) ^ s) ≤
      (twoAwayMomentJointConstant q s : ℝ≥0) *
        (((2 : ℝ≥0) ^ twoAwayMomentUnionCutoff q s *
          (twoAwayThreatExtensionCoefficient q M H X B : ℕ)) ^ s) := by
  let F := absorberErdosForbiddenConfigurationsOn q B
  let S₀ := absorberGreedyInitialState F A
  let L := FiniteLaw.timedStoppedProcessLaw n
    (fun _ ↦ greedyKernel F) active S₀
  apply twoAwayForbiddenMomentBound L (fun z ↦ z.2.chosen) F U
    (constantTripleWeight ((Fintype.card V + 1 : ℝ≥0)⁻¹))
    (twoAwayMomentJointConstant q s : ℝ≥0)
    (twoAwayThreatExtensionCoefficient q M H X B : ℕ)
  · intro C hCF
    exact card_le_cutoff_of_mem_absorberErdosForbidden hCF
  · exact absorberTwoAwayThreatRemainder_hasExtensionBound hA2
  · intro T hTcard
    apply timedStoppedGreedyProcess_probability_subset_chosen_le_weight
      n F active D (twoAwayMomentUnionCutoff q s)
      ((Fintype.card V + 1 : ℝ≥0)⁻¹) hD hfloor hratio S₀ T
    · simp [S₀, absorberGreedyInitialState]
    · exact hTcard

/-- Markov tail for one fixed root triangle. -/
theorem timedStoppedAbsorberGreedy_probability_twoAway_gt_le
    {V : Type*} [Fintype V] [DecidableEq V]
    {q M K n s D : ℕ} {H : SimpleGraph V} {X : Finset V}
    {B A : TripleSystemOn V}
    (active : ℕ → GreedyStateOn V → Prop) (U : TripleOn V)
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
      (fun z ↦ K < (twoAwayForbiddenTriangles
        (absorberErdosForbiddenConfigurationsOn q B)
        z.2.chosen U).card) ≤
      envelopeTwoAwayTail q M s H X B K := by
  let F := absorberErdosForbiddenConfigurationsOn q B
  let S₀ := absorberGreedyInitialState F A
  let L := FiniteLaw.timedStoppedProcessLaw n
    (fun _ ↦ greedyKernel F) active S₀
  let Y : FiniteLaw.TimedState (GreedyStateOn V) n → ℝ≥0 := fun z ↦
    ((twoAwayForbiddenTriangles F z.2.chosen U).card : ℝ≥0) ^ s
  have hthreshold : (0 : ℝ≥0) < (((K + 1 : ℕ) : ℝ≥0) ^ s) := by
    positivity
  have hmono : L.probability
      (fun z ↦ K < (twoAwayForbiddenTriangles F z.2.chosen U).card) ≤
      L.probability (fun z ↦ (((K + 1 : ℕ) : ℝ≥0) ^ s) ≤ Y z) := by
    apply L.probability_mono
    intro z hz
    apply pow_le_pow_left'
    exact_mod_cast (show K + 1 ≤
      (twoAwayForbiddenTriangles F z.2.chosen U).card by omega)
  refine hmono.trans ?_
  have hmarkov := L.probability_le_expectation_div Y hthreshold
  refine hmarkov.trans ?_
  apply (div_le_div_iff_of_pos_right hthreshold).2
  simpa [L, F, S₀, envelopeTwoAwayTail] using
    (timedStoppedAbsorberGreedy_twoAwayMomentBound
      (K := K) (s := s) active U hA2 hD hfloor hratio)

/-- Finite union bound for failure of the two-away cutoff in the terminal
timed state. -/
theorem timedStoppedAbsorberGreedy_probability_not_twoAwayCutoff_le
    {V : Type*} [Fintype V] [DecidableEq V]
    {q M K n s D : ℕ} {H : SimpleGraph V} {X : Finset V}
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
      (fun z ↦ ¬ HasTwoAwayCutoff
        (absorberErdosForbiddenConfigurationsOn q B) K z.2) ≤
      (Fintype.card (TripleOn V) : ℝ≥0) *
        envelopeTwoAwayTail q M s H X B K := by
  let F := absorberErdosForbiddenConfigurationsOn q B
  let S₀ := absorberGreedyInitialState F A
  let L := FiniteLaw.timedStoppedProcessLaw n
    (fun _ ↦ greedyKernel F) active S₀
  let badAt : TripleOn V → FiniteLaw.TimedState (GreedyStateOn V) n → Prop :=
    fun U z ↦ K < (twoAwayForbiddenTriangles F z.2.chosen U).card
  calc
    L.probability (fun z ↦ ¬ HasTwoAwayCutoff F K z.2) ≤
        L.probability (fun z ↦ ∃ U : TripleOn V, badAt U z) := by
      apply L.probability_mono
      intro z hz
      rw [HasTwoAwayCutoff] at hz
      push_neg at hz
      obtain ⟨U, _hUavailable, hU⟩ := hz
      exact ⟨U, by simpa [badAt] using hU⟩
    _ ≤ ∑ U ∈ (univ : Finset (TripleOn V)),
        L.probability (badAt U) := by
      simpa using L.probability_exists_le
        (univ : Finset (TripleOn V)) badAt
    _ ≤ ∑ _U ∈ (univ : Finset (TripleOn V)),
        envelopeTwoAwayTail q M s H X B K := by
      apply sum_le_sum
      intro U _hU
      simpa [L, F, S₀, badAt] using
        (timedStoppedAbsorberGreedy_probability_twoAway_gt_le
          (K := K) (s := s) active U hA2 hD hfloor hratio)
    _ = (Fintype.card (TripleOn V) : ℝ≥0) *
        envelopeTwoAwayTail q M s H X B K := by simp

end

end Erdos207
