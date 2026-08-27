/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.SourceRandomConfigurationSampling

/-! # Both mixed-pair tails on the same source random-configuration law -/

namespace Erdos207.SourceRandomConfigurationParameters

open Finset
open scoped NNReal

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V] {ell j s : ℕ}
  {W : Vortex V ell} {delta a : ℝ≥0}

theorem old_new_failure (P : SourceRandomConfigurationParameters W j delta a s)
    (F : ForbiddenFamilyOn V) (y z : ℝ≥0) (hF : SourceVortexWellSpread W j F y z)
    (hdeltaY : delta * y ≤ W.terminalSize) (T T' : TripleOn V) :
    P.law.probability (fun ω ↦ a * (W.terminalSize : ℝ≥0) ^ (j - 4) <
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
  apply FiniteLaw.probability_natCast_gt_le_dyadic P.law _ mu _ s ?_ hb.1 hb.2
  intro k hk hs
  simp only [law, sampleTerminalConfigurations, crossDistinctConfigurationPairs_sample_right]
  exact independentBits_probability_secondSelectedPairs_card_ge_le_dyadic
    (F ∪ terminalRandomConfigurations W j) T T' C
    (crossDistinctConfigurationPairs_subset_union F (terminalRandomConfigurations W j) T T')
    _ P.probability_le_one k s (by simpa only [mu, NNReal.coe_mul, NNReal.coe_natCast] using hk) hs

theorem new_old_failure (P : SourceRandomConfigurationParameters W j delta a s)
    (F : ForbiddenFamilyOn V) (y z : ℝ≥0) (hF : SourceVortexWellSpread W j F y z)
    (hdeltaY : delta * y ≤ W.terminalSize) (T T' : TripleOn V) :
    P.law.probability (fun ω ↦ a * (W.terminalSize : ℝ≥0) ^ (j - 4) <
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
  apply FiniteLaw.probability_natCast_gt_le_dyadic P.law _ mu _ s ?_ hb.1 hb.2
  intro k hk hs
  simp only [law, sampleTerminalConfigurations, crossDistinctConfigurationPairs_sample_left]
  exact independentBits_probability_firstSelectedPairs_card_ge_le_dyadic
    (terminalRandomConfigurations W j ∪ F) T T' C
    (crossDistinctConfigurationPairs_subset_union (terminalRandomConfigurations W j) F T T')
    _ P.probability_le_one k s (by simpa only [mu, NNReal.coe_mul, NNReal.coe_natCast] using hk) hs

end

end Erdos207.SourceRandomConfigurationParameters
