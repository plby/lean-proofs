/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.CrossConfigurationPairs
import ErdosProblems.Erdos207.RandomConfigurationMeanBudgets

/-! # Source-probability mean bounds for the actual finite candidate classes -/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

theorem randomConfiguration_actual_root_mean_le
    {V : Type*} [Fintype V] [DecidableEq V] {ell j : ℕ}
    (W : Vortex V ell) (R : TripleSystemOn V) (delta : ℝ≥0)
    (hn : 0 < W.terminalSize) (hj : 4 ≤ j) (hR : R.Nonempty) (hRcard : R.card ≤ j - 2) :
    sourceRandomConfigurationProbability W.terminalSize delta j * (familyExtensions (terminalRandomConfigurations W j) R).card ≤
      delta * (W.terminalSize : ℝ≥0) ^ (j - vortexRootExponent j R.card) := by
  have hn1 : (1 : ℝ≥0) ≤ W.terminalSize := by exact_mod_cast hn
  have hcount : ((familyExtensions (terminalRandomConfigurations W j) R).card : ℝ≥0) ≤
      ((W.terminalSize : ℝ≥0) ^ 3) ^ (j - 2 - R.card) := by
    exact_mod_cast card_familyExtensions_terminalRandomConfigurations_le W R
  exact (mul_le_mul_of_nonneg_left hcount zero_le).trans
    (sourceRandomConfiguration_root_mean_le W.terminalSize delta j R.card hn1 hj (card_pos.mpr hR) hRcard)

theorem randomConfiguration_actual_pair_mean_le_one
    {V : Type*} [Fintype V] [DecidableEq V] {ell j : ℕ}
    (W : Vortex V ell) (T T' : TripleOn V) (delta : ℝ≥0)
    (hn : 0 < W.terminalSize) (hj : 4 ≤ j) (hdeltaSq : delta ^ 2 ≤ W.terminalSize) :
    (sourceRandomConfigurationProbability W.terminalSize delta j) ^ 2 *
      (distinctEqualRemainderPairs (terminalRandomConfigurations W j) T T').card ≤ 1 := by
  have hn1 : (1 : ℝ≥0) ≤ W.terminalSize := by exact_mod_cast hn
  have hcount : ((distinctEqualRemainderPairs (terminalRandomConfigurations W j) T T').card : ℝ≥0) ≤
      ((W.terminalSize : ℝ≥0) ^ 3) ^ (j - 3) := by
    exact_mod_cast card_distinctPairs_terminalRandomConfigurations_le W T T'
  exact (mul_le_mul_of_nonneg_left hcount zero_le).trans
    (sourceRandomConfiguration_pair_mean_le_one W.terminalSize delta j hn1 hdeltaSq hj)

theorem randomConfiguration_actual_old_new_mean_le_one
    {V : Type*} [Fintype V] [DecidableEq V] {ell j : ℕ}
    (W : Vortex V ell) (F : ForbiddenFamilyOn V) (T T' : TripleOn V) (delta y z : ℝ≥0)
    (hF : SourceVortexWellSpread W j F y z) (hdeltaY : delta * y ≤ W.terminalSize) :
    sourceRandomConfigurationProbability W.terminalSize delta j *
      (crossDistinctConfigurationPairs F (terminalRandomConfigurations W j) T T').card ≤ 1 := by
  have hn1 : (1 : ℝ≥0) ≤ W.terminalSize := by exact_mod_cast hF.terminal_nonempty
  have hcount : ((crossDistinctConfigurationPairs F (terminalRandomConfigurations W j) T T').card : ℝ≥0) ≤
      (W.profiledExtensions F {T} 0).card := by
    exact_mod_cast card_crossDistinctPairs_le_first_zero_profile W F (terminalRandomConfigurations W j) T T'
      (terminalRandomConfigurations_isTerminal W)
  have hsource := hF.singleton_extensions T 0
  rw [W.sourceProfileScale_zero] at hsource
  calc
    _ ≤ sourceRandomConfigurationProbability W.terminalSize delta j *
        (y * (W.terminalSize : ℝ≥0) ^ (j - 3)) := mul_le_mul_of_nonneg_left (hcount.trans hsource) zero_le
    _ = sourceRandomConfigurationProbability W.terminalSize delta j * y * (W.terminalSize : ℝ≥0) ^ (j - 3) := by ring
    _ ≤ 1 := sourceRandomConfiguration_mixed_mean_le_one W.terminalSize delta y j hn1 hdeltaY hF.order

theorem randomConfiguration_actual_new_old_mean_le_one
    {V : Type*} [Fintype V] [DecidableEq V] {ell j : ℕ}
    (W : Vortex V ell) (F : ForbiddenFamilyOn V) (T T' : TripleOn V) (delta y z : ℝ≥0)
    (hF : SourceVortexWellSpread W j F y z) (hdeltaY : delta * y ≤ W.terminalSize) :
    sourceRandomConfigurationProbability W.terminalSize delta j *
      (crossDistinctConfigurationPairs (terminalRandomConfigurations W j) F T T').card ≤ 1 := by
  have hn1 : (1 : ℝ≥0) ≤ W.terminalSize := by exact_mod_cast hF.terminal_nonempty
  have hcount : ((crossDistinctConfigurationPairs (terminalRandomConfigurations W j) F T T').card : ℝ≥0) ≤
      (W.profiledExtensions F {T'} 0).card := by
    exact_mod_cast card_crossDistinctPairs_le_second_zero_profile W (terminalRandomConfigurations W j) F T T'
      (terminalRandomConfigurations_isTerminal W)
  have hsource := hF.singleton_extensions T' 0
  rw [W.sourceProfileScale_zero] at hsource
  calc
    _ ≤ sourceRandomConfigurationProbability W.terminalSize delta j *
        (y * (W.terminalSize : ℝ≥0) ^ (j - 3)) := mul_le_mul_of_nonneg_left (hcount.trans hsource) zero_le
    _ = sourceRandomConfigurationProbability W.terminalSize delta j * y * (W.terminalSize : ℝ≥0) ^ (j - 3) := by ring
    _ ≤ 1 := sourceRandomConfiguration_mixed_mean_le_one W.terminalSize delta y j hn1 hdeltaY hF.order

theorem randomConfiguration_actual_order_four_mean_le
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    (W : Vortex V ell) (T : TripleOn V) (P : VortexPairOn V) (delta : ℝ≥0)
    (hn : 0 < W.terminalSize) :
    sourceRandomConfigurationProbability W.terminalSize delta 4 *
      (W.terminalPairExtensions (terminalRandomConfigurations W 4) T P).card ≤ delta := by
  have hn1 : (1 : ℝ≥0) ≤ W.terminalSize := by exact_mod_cast hn
  have hcount : ((W.terminalPairExtensions (terminalRandomConfigurations W 4) T P).card : ℝ≥0) ≤ W.terminalSize := by
    exact_mod_cast card_terminalPairExtensions_randomCandidates_le W T P
  exact (mul_le_mul_of_nonneg_left hcount zero_le).trans
    (sourceRandomConfiguration_order_four_mean_le W.terminalSize delta hn1)

theorem randomConfiguration_scaled_threshold_budgets
    (n mu delta a : ℝ≥0) (d s : ℕ) (hn : 1 ≤ n)
    (hmu : mu ≤ delta * n ^ d) (ha : 4 * delta ≤ a) (hs : (4 * s : ℕ) ≤ (a : ℝ≥0)) :
    4 * mu ≤ a * n ^ d ∧ (4 * s : ℕ) ≤ (a * n ^ d : ℝ≥0) := by
  constructor
  · calc
      4 * mu ≤ 4 * (delta * n ^ d) := mul_le_mul_of_nonneg_left hmu zero_le
      _ = (4 * delta) * n ^ d := by ring
      _ ≤ a * n ^ d := mul_le_mul_of_nonneg_right ha zero_le
  · apply hs.trans
    calc
      a = a * 1 := (mul_one _).symm
      _ ≤ _ := mul_le_mul_of_nonneg_left (one_le_pow₀ hn) zero_le

end

end Erdos207
