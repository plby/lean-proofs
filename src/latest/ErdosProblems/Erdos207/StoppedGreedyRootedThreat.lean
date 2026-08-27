/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.StoppedGreedyJointInclusion
import ErdosProblems.Erdos207.RootedThreatWellSpread
import ErdosProblems.Erdos207.RootedThreatExtraction

/-!
# Rooted-threat moments for the stopped constrained-greedy process

This is the first concrete probabilistic application of the absorber
well-spreadness theorem.  A threshold ratio at most `(n+1)⁻¹` supplies the
joint-inclusion hypothesis, and the finite moment/union argument controls all
rooted forbidden-configuration counts simultaneously.
-/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

/-- Maximum number of selected triangles appearing in an `s`-tuple of
rooted remainders when forbidden outside parts have size at most `q`. -/
def rootedMomentUnionCutoff (q s : ℕ) : ℕ := s * (q - 1)

/-- The uniform joint-inclusion constant supplied by the stopped-process
factorial bound at the rooted moment cutoff. -/
def rootedMomentJointConstant (q s : ℕ) : ℕ :=
  (rootedMomentUnionCutoff q s).factorial

/-- Concrete rooted moment estimate for the stopped absorber-constrained
greedy law. -/
theorem stoppedAbsorberGreedy_rootedActiveMomentBound
    {V : Type*} [Fintype V] [DecidableEq V]
    {q M D fuel s : ℕ} {H : SimpleGraph V} {X : Finset V}
    {B A : TripleSystemOn V} {u v : V}
    (hA2 : HasAbsorberLocalization q M H X B) (huv : u ≠ v)
    (hD : 0 < D)
    (hratio : (fuel : ℝ≥0) * (D : ℝ≥0)⁻¹ ≤
      (Fintype.card V + 1 : ℝ≥0)⁻¹) :
    (stoppedGreedyProcessLaw
        (absorberErdosForbiddenConfigurationsOn q B) D fuel
        (absorberGreedyInitialState
          (absorberErdosForbiddenConfigurationsOn q B) A)).expectation
      (fun S ↦ ((rootedActiveForbiddenConfigurations
        (absorberErdosForbiddenConfigurationsOn q B)
        S.chosen u v).card : ℝ≥0) ^ s) ≤
      (rootedMomentJointConstant q s : ℝ≥0) *
        (((2 : ℝ≥0) ^ rootedMomentUnionCutoff q s *
          ((Fintype.card V *
            rootedThreatExtensionCoefficient q M H X B : ℕ) : ℝ≥0)) ^ s) := by
  let F := absorberErdosForbiddenConfigurationsOn q B
  let S₀ := absorberGreedyInitialState F A
  let L := stoppedGreedyProcessLaw F D fuel S₀
  apply rootedActiveMomentBound L (fun S ↦ S.chosen) F u v
    (constantTripleWeight ((Fintype.card V + 1 : ℝ≥0)⁻¹))
    (rootedMomentJointConstant q s : ℝ≥0)
    ((Fintype.card V *
      rootedThreatExtensionCoefficient q M H X B : ℕ) : ℝ≥0)
  · intro C hCF
    exact card_le_cutoff_of_mem_absorberErdosForbidden hCF
  · exact absorberRootedThreatRemainder_hasExtensionBound hA2 huv
  · intro T hTcard
    apply stoppedGreedyProcess_probability_subset_chosen_le_weight
      F D fuel (rootedMomentUnionCutoff q s) hD
      ((Fintype.card V + 1 : ℝ≥0)⁻¹) hratio S₀ T
    · simp [S₀, absorberGreedyInitialState]
    · exact hTcard

/-- Markov's inequality converts the concrete rooted moment estimate into a
one-pair upper-tail estimate. -/
theorem stoppedAbsorberGreedy_probability_rootedActive_ge_le
    {V : Type*} [Fintype V] [DecidableEq V]
    {q M D fuel s : ℕ} {H : SimpleGraph V} {X : Finset V}
    {B A : TripleSystemOn V} (e : DistinctPair V) (a : ℝ≥0)
    (hA2 : HasAbsorberLocalization q M H X B)
    (hD : 0 < D) (ha : 0 < a)
    (hratio : (fuel : ℝ≥0) * (D : ℝ≥0)⁻¹ ≤
      (Fintype.card V + 1 : ℝ≥0)⁻¹) :
    (stoppedGreedyProcessLaw
        (absorberErdosForbiddenConfigurationsOn q B) D fuel
        (absorberGreedyInitialState
          (absorberErdosForbiddenConfigurationsOn q B) A)).probability
      (fun S ↦ a ≤ (rootedActiveForbiddenConfigurations
        (absorberErdosForbiddenConfigurationsOn q B)
        S.chosen e.1.1 e.1.2).card) ≤
      ((rootedMomentJointConstant q s : ℝ≥0) *
        (((2 : ℝ≥0) ^ rootedMomentUnionCutoff q s *
          ((Fintype.card V *
            rootedThreatExtensionCoefficient q M H X B : ℕ) : ℝ≥0)) ^ s)) /
        a ^ s := by
  let F := absorberErdosForbiddenConfigurationsOn q B
  let S₀ := absorberGreedyInitialState F A
  let L := stoppedGreedyProcessLaw F D fuel S₀
  let Xroot : GreedyStateOn V → ℝ≥0 := fun S ↦
    ((rootedActiveForbiddenConfigurations F S.chosen
      e.1.1 e.1.2).card : ℝ≥0) ^ s
  have hmono : L.probability
      (fun S ↦ a ≤ (rootedActiveForbiddenConfigurations F S.chosen
        e.1.1 e.1.2).card) ≤
      L.probability (fun S ↦ a ^ s ≤ Xroot S) := by
    apply L.probability_mono
    intro S hS
    exact pow_le_pow_left' hS s
  refine hmono.trans ?_
  have hmarkov := L.probability_le_expectation_div Xroot (pow_pos ha s)
  refine hmarkov.trans ?_
  apply (div_le_div_iff_of_pos_right (pow_pos ha s)).2
  exact stoppedAbsorberGreedy_rootedActiveMomentBound
    hA2 e.2 hD hratio

/-- Under the explicit moment smallness inequality, one stopped trajectory
simultaneously controls the rooted active count at every distinct ordered
pair. -/
theorem exists_stoppedAbsorberGreedy_all_rootedActive_lt
    {V : Type*} [Fintype V] [DecidableEq V]
    {q M D fuel s : ℕ} {H : SimpleGraph V} {X : Finset V}
    {B A : TripleSystemOn V} (a : ℝ≥0)
    (hA2 : HasAbsorberLocalization q M H X B)
    (hD : 0 < D) (ha : 0 < a)
    (hratio : (fuel : ℝ≥0) * (D : ℝ≥0)⁻¹ ≤
      (Fintype.card V + 1 : ℝ≥0)⁻¹)
    (hsmall : (Fintype.card (DistinctPair V) : ℝ≥0) *
      (((rootedMomentJointConstant q s : ℝ≥0) *
        (((2 : ℝ≥0) ^ rootedMomentUnionCutoff q s *
          ((Fintype.card V *
            rootedThreatExtensionCoefficient q M H X B : ℕ) : ℝ≥0)) ^ s)) /
        a ^ s) < 1) :
    ∃ S : GreedyStateOn V, ∀ e : DistinctPair V,
      ((rootedActiveForbiddenConfigurations
        (absorberErdosForbiddenConfigurationsOn q B)
        S.chosen e.1.1 e.1.2).card : ℝ≥0) < a := by
  let F := absorberErdosForbiddenConfigurationsOn q B
  let S₀ := absorberGreedyInitialState F A
  let L := stoppedGreedyProcessLaw F D fuel S₀
  apply exists_all_rootedActive_lt_of_moment L (fun S ↦ S.chosen) F
    (constantTripleWeight ((Fintype.card V + 1 : ℝ≥0)⁻¹))
    (rootedMomentJointConstant q s : ℝ≥0)
    ((Fintype.card V *
      rootedThreatExtensionCoefficient q M H X B : ℕ) : ℝ≥0)
    a ha
  · intro C hCF
    exact card_le_cutoff_of_mem_absorberErdosForbidden hCF
  · intro e
    exact absorberRootedThreatRemainder_hasExtensionBound hA2 e.2
  · intro T hTcard
    apply stoppedGreedyProcess_probability_subset_chosen_le_weight
      F D fuel (rootedMomentUnionCutoff q s) hD
      ((Fintype.card V + 1 : ℝ≥0)⁻¹) hratio S₀ T
    · simp [S₀, absorberGreedyInitialState]
    · exact hTcard
  · exact hsmall

end

end Erdos207
