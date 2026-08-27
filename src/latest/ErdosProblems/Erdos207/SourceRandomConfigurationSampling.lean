/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.RandomConfigurationActualMeans
import ErdosProblems.Erdos207.RealCountCutoff

/-! # One actual product law for source random configuration augmentation -/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

def sampleTerminalConfigurations
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    (W : Vortex V ell) (j : ℕ) (ω : TripleSystemOn V → Bool) : ForbiddenFamilyOn V :=
  (terminalRandomConfigurations W j).filter fun C ↦ ω C = true

structure SourceRandomConfigurationParameters
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    (W : Vortex V ell) (j : ℕ) (delta a : ℝ≥0) (s : ℕ) : Prop where
  order : 4 ≤ j
  terminal : 0 < W.terminalSize
  delta_one : 1 ≤ delta
  delta_square : delta ^ 2 ≤ W.terminalSize
  amplitude : 4 * delta ≤ a
  deviation : (4 * s : ℕ) ≤ (a : ℝ≥0)

namespace SourceRandomConfigurationParameters

variable {V : Type*} [Fintype V] [DecidableEq V] {ell j s : ℕ}
  {W : Vortex V ell} {delta a : ℝ≥0}

theorem probability_le_one (P : SourceRandomConfigurationParameters W j delta a s) :
    sourceRandomConfigurationProbability W.terminalSize delta j ≤ 1 := by
  exact sourceRandomConfigurationProbability_le_one W.terminalSize delta j
    (by exact_mod_cast P.terminal) P.delta_one P.delta_square P.order

def law (P : SourceRandomConfigurationParameters W j delta a s) : FiniteLaw (TripleSystemOn V → Bool) :=
  FiniteLaw.independentBits (fun _ ↦ sourceRandomConfigurationProbability W.terminalSize delta j)
    (fun _ ↦ P.probability_le_one)

theorem sample_terminal (P : SourceRandomConfigurationParameters W j delta a s)
    (ω : TripleSystemOn V → Bool) : IsTerminalConfigurationFamily W (sampleTerminalConfigurations W j ω) :=
  (terminalRandomConfigurations_isTerminal W).mono (filter_subset _ _)

theorem sample_uniform (P : SourceRandomConfigurationParameters W j delta a s)
    (ω : TripleSystemOn V → Bool) (C : TripleSystemOn V) (hC : C ∈ sampleTerminalConfigurations W j ω) :
    C.card = j - 2 ∧ IsPackingOn C :=
  terminalRandomConfigurations_uniform W C (mem_filter.mp hC).1

theorem root_failure (P : SourceRandomConfigurationParameters W j delta a s)
    (R : TripleSystemOn V) (hR : R.Nonempty) (hRcard : R.card ≤ j - 2) :
    P.law.probability (fun ω ↦ a * (W.terminalSize : ℝ≥0) ^ (j - vortexRootExponent j R.card) <
      ((familyExtensions (sampleTerminalConfigurations W j ω) R).card : ℝ≥0)) ≤ ((2 : ℝ≥0) ^ s)⁻¹ := by
  have hmu := randomConfiguration_actual_root_mean_le W R delta P.terminal P.order hR hRcard
  have hb := randomConfiguration_scaled_threshold_budgets W.terminalSize _ delta a _ s
    (by exact_mod_cast P.terminal) hmu P.amplitude P.deviation
  simp only [law, sampleTerminalConfigurations, familyExtensions_sample_eq_filter]
  exact independentBits_probability_filter_card_gt_le_dyadic _ _ _ P.probability_le_one s hb.1 hb.2

theorem pair_failure (P : SourceRandomConfigurationParameters W j delta a s) (T T' : TripleOn V) :
    P.law.probability (fun ω ↦ a * (W.terminalSize : ℝ≥0) ^ (j - 4) <
      ((distinctEqualRemainderPairs (sampleTerminalConfigurations W j ω) T T').card : ℝ≥0)) ≤ ((2 : ℝ≥0) ^ s)⁻¹ := by
  let mu := (sourceRandomConfigurationProbability W.terminalSize delta j) ^ 2 *
    (distinctEqualRemainderPairs (terminalRandomConfigurations W j) T T').card
  have hmu : mu ≤ delta * (W.terminalSize : ℝ≥0) ^ (j - 4) := by
    have hsmall := randomConfiguration_actual_pair_mean_le_one W T T' delta P.terminal P.order P.delta_square
    exact hsmall.trans (one_le_mul_of_one_le_of_one_le P.delta_one
      (one_le_pow₀ (by exact_mod_cast P.terminal : (1 : ℝ≥0) ≤ W.terminalSize)))
  have hb := randomConfiguration_scaled_threshold_budgets W.terminalSize mu delta a (j - 4) s
    (by exact_mod_cast P.terminal) hmu P.amplitude P.deviation
  apply FiniteLaw.probability_natCast_gt_le_dyadic P.law _ mu _ s ?_ hb.1 hb.2
  intro k hk hs
  exact independentBits_probability_sampledConfigurationPairs_card_ge_le_dyadic
    (terminalRandomConfigurations W j) T T' _ P.probability_le_one k s
    (by simpa only [mu, NNReal.coe_mul, NNReal.coe_pow, NNReal.coe_natCast] using hk) hs

theorem order_four_failure (P : SourceRandomConfigurationParameters W j delta a s) (hj : j = 4)
    (T : TripleOn V) (Q : VortexPairOn V) :
    P.law.probability (fun ω ↦ a <
      ((W.terminalPairExtensions (sampleTerminalConfigurations W j ω) T Q).card : ℝ≥0)) ≤ ((2 : ℝ≥0) ^ s)⁻¹ := by
  subst j
  have hmu := randomConfiguration_actual_order_four_mean_le W T Q delta P.terminal
  have hmean := (mul_le_mul_of_nonneg_left hmu (by norm_num : (0 : ℝ≥0) ≤ 4)).trans P.amplitude
  simp only [law, sampleTerminalConfigurations, W.terminalPairExtensions_sample_eq_filter]
  exact independentBits_probability_filter_card_gt_le_dyadic _ _ a P.probability_le_one s hmean P.deviation

end SourceRandomConfigurationParameters

end

end Erdos207
