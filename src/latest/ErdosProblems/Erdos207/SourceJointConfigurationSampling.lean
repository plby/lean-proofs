/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.JointConfigurationCountTails
import ErdosProblems.Erdos207.SourceRandomMixedSampling

/-! # Source augmentation count tails for adaptive joint-inclusion laws -/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

def HasSourceConfigurationJointBound
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    (W : Vortex V ell) (j : ℕ) (delta : ℝ≥0)
    (L : FiniteLaw (TripleSystemOn V → Bool)) : Prop :=
  ∀ U, L.probability (fun ω ↦ ∀ E ∈ U, ω E = true) ≤
    setWeight (fun _ ↦ sourceRandomConfigurationProbability W.terminalSize delta j) U

namespace SourceRandomConfigurationParameters

variable {V : Type*} [Fintype V] [DecidableEq V] {ell j s : ℕ}
  {W : Vortex V ell} {delta a : ℝ≥0}

theorem joint_root_failure (P : SourceRandomConfigurationParameters W j delta a s)
    (L : FiniteLaw (TripleSystemOn V → Bool)) (hjoint : HasSourceConfigurationJointBound W j delta L)
    (R : TripleSystemOn V) (hR : R.Nonempty) (hRcard : R.card ≤ j - 2) :
    L.probability (fun ω ↦ a * (W.terminalSize : ℝ≥0) ^ (j - vortexRootExponent j R.card) <
      ((familyExtensions (sampleTerminalConfigurations W j ω) R).card : ℝ≥0)) ≤ ((2 : ℝ≥0) ^ s)⁻¹ := by
  have hmu := randomConfiguration_actual_root_mean_le W R delta P.terminal P.order hR hRcard
  have hb := randomConfiguration_scaled_threshold_budgets W.terminalSize _ delta a _ s
    (by exact_mod_cast P.terminal) hmu P.amplitude P.deviation
  simp only [sampleTerminalConfigurations, familyExtensions_sample_eq_filter]
  exact joint_filter_card_gt_le_dyadic L _ hjoint _ _ s hb.1 hb.2

theorem joint_pair_failure (P : SourceRandomConfigurationParameters W j delta a s)
    (L : FiniteLaw (TripleSystemOn V → Bool)) (hjoint : HasSourceConfigurationJointBound W j delta L)
    (T T' : TripleOn V) :
    L.probability (fun ω ↦ a * (W.terminalSize : ℝ≥0) ^ (j - 4) <
      ((distinctEqualRemainderPairs (sampleTerminalConfigurations W j ω) T T').card : ℝ≥0)) ≤
        ((2 : ℝ≥0) ^ s)⁻¹ := by
  let mu := (sourceRandomConfigurationProbability W.terminalSize delta j) ^ 2 *
    (distinctEqualRemainderPairs (terminalRandomConfigurations W j) T T').card
  have hmu : mu ≤ delta * (W.terminalSize : ℝ≥0) ^ (j - 4) := by
    have hsmall := randomConfiguration_actual_pair_mean_le_one W T T' delta P.terminal P.order P.delta_square
    exact hsmall.trans (one_le_mul_of_one_le_of_one_le P.delta_one
      (one_le_pow₀ (by exact_mod_cast P.terminal : (1 : ℝ≥0) ≤ W.terminalSize)))
  have hb := randomConfiguration_scaled_threshold_budgets W.terminalSize mu delta a (j - 4) s
    (by exact_mod_cast P.terminal) hmu P.amplitude P.deviation
  exact joint_sampledConfigurationPairs_card_gt_le_dyadic L _ hjoint
    (terminalRandomConfigurations W j) T T' _ s hb.1 hb.2

theorem joint_order_four_failure (P : SourceRandomConfigurationParameters W j delta a s)
    (L : FiniteLaw (TripleSystemOn V → Bool)) (hjoint : HasSourceConfigurationJointBound W j delta L)
    (hj : j = 4) (T : TripleOn V) (Q : VortexPairOn V) :
    L.probability (fun ω ↦ a <
      ((W.terminalPairExtensions (sampleTerminalConfigurations W j ω) T Q).card : ℝ≥0)) ≤
        ((2 : ℝ≥0) ^ s)⁻¹ := by
  subst j
  have hmu := randomConfiguration_actual_order_four_mean_le W T Q delta P.terminal
  have hmean := (mul_le_mul_of_nonneg_left hmu (by norm_num : (0 : ℝ≥0) ≤ 4)).trans P.amplitude
  simp only [sampleTerminalConfigurations, W.terminalPairExtensions_sample_eq_filter]
  exact joint_filter_card_gt_le_dyadic L _ hjoint _ a s hmean P.deviation

theorem joint_old_new_failure (P : SourceRandomConfigurationParameters W j delta a s)
    (L : FiniteLaw (TripleSystemOn V → Bool)) (hjoint : HasSourceConfigurationJointBound W j delta L)
    (F : ForbiddenFamilyOn V) (y z : ℝ≥0) (hF : SourceVortexWellSpread W j F y z)
    (hdeltaY : delta * y ≤ W.terminalSize) (T T' : TripleOn V) :
    L.probability (fun ω ↦ a * (W.terminalSize : ℝ≥0) ^ (j - 4) <
      ((crossDistinctConfigurationPairs F (sampleTerminalConfigurations W j ω) T T').card : ℝ≥0)) ≤
        ((2 : ℝ≥0) ^ s)⁻¹ := by
  let C := crossDistinctConfigurationPairs F (terminalRandomConfigurations W j) T T'
  let mu := sourceRandomConfigurationProbability W.terminalSize delta j * C.card
  have hmu : mu ≤ delta * (W.terminalSize : ℝ≥0) ^ (j - 4) := by
    have hsmall := randomConfiguration_actual_old_new_mean_le_one W F T T' delta y z hF hdeltaY
    exact hsmall.trans (one_le_mul_of_one_le_of_one_le P.delta_one
      (one_le_pow₀ (by exact_mod_cast P.terminal : (1 : ℝ≥0) ≤ W.terminalSize)))
  have hb := randomConfiguration_scaled_threshold_budgets W.terminalSize mu delta a (j - 4) s
    (by exact_mod_cast P.terminal) hmu P.amplitude P.deviation
  have hinj : Set.InjOn (fun C : TripleSystemOn V × TripleSystemOn V ↦ C.2) (C : Set _) := by
    intro C hC D hD heq
    exact distinctEqualRemainderPairs_snd_injOn (F ∪ terminalRandomConfigurations W j) T T'
      (crossDistinctConfigurationPairs_subset_union F (terminalRandomConfigurations W j) T T' hC)
      (crossDistinctConfigurationPairs_subset_union F (terminalRandomConfigurations W j) T T' hD) heq
  simp only [sampleTerminalConfigurations, crossDistinctConfigurationPairs_sample_right]
  exact joint_injective_filter_card_gt_le_dyadic L _ hjoint C (fun C ↦ C.2) hinj _ s hb.1 hb.2

theorem joint_new_old_failure (P : SourceRandomConfigurationParameters W j delta a s)
    (L : FiniteLaw (TripleSystemOn V → Bool)) (hjoint : HasSourceConfigurationJointBound W j delta L)
    (F : ForbiddenFamilyOn V) (y z : ℝ≥0) (hF : SourceVortexWellSpread W j F y z)
    (hdeltaY : delta * y ≤ W.terminalSize) (T T' : TripleOn V) :
    L.probability (fun ω ↦ a * (W.terminalSize : ℝ≥0) ^ (j - 4) <
      ((crossDistinctConfigurationPairs (sampleTerminalConfigurations W j ω) F T T').card : ℝ≥0)) ≤
        ((2 : ℝ≥0) ^ s)⁻¹ := by
  let C := crossDistinctConfigurationPairs (terminalRandomConfigurations W j) F T T'
  let mu := sourceRandomConfigurationProbability W.terminalSize delta j * C.card
  have hmu : mu ≤ delta * (W.terminalSize : ℝ≥0) ^ (j - 4) := by
    have hsmall := randomConfiguration_actual_new_old_mean_le_one W F T T' delta y z hF hdeltaY
    exact hsmall.trans (one_le_mul_of_one_le_of_one_le P.delta_one
      (one_le_pow₀ (by exact_mod_cast P.terminal : (1 : ℝ≥0) ≤ W.terminalSize)))
  have hb := randomConfiguration_scaled_threshold_budgets W.terminalSize mu delta a (j - 4) s
    (by exact_mod_cast P.terminal) hmu P.amplitude P.deviation
  have hinj : Set.InjOn (fun C : TripleSystemOn V × TripleSystemOn V ↦ C.1) (C : Set _) := by
    intro C hC D hD heq
    exact distinctEqualRemainderPairs_fst_injOn (terminalRandomConfigurations W j ∪ F) T T'
      (crossDistinctConfigurationPairs_subset_union (terminalRandomConfigurations W j) F T T' hC)
      (crossDistinctConfigurationPairs_subset_union (terminalRandomConfigurations W j) F T T' hD) heq
  simp only [sampleTerminalConfigurations, crossDistinctConfigurationPairs_sample_left]
  exact joint_injective_filter_card_gt_le_dyadic L _ hjoint C (fun C ↦ C.1) hinj _ s hb.1 hb.2

end SourceRandomConfigurationParameters

end

end Erdos207
