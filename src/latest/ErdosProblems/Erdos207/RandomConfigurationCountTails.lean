/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.TerminalPairCandidateCount

/-! # Actual sampling tails for the three random configuration counts -/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

theorem independentBits_probability_filter_card_ge_le_dyadic
    {I : Type*} [Fintype I] [DecidableEq I] (S : Finset I)
    (p : ℝ≥0) (hp : p ≤ 1) (k s : ℕ)
    (hk : 4 * ((p : ℝ) * S.card) ≤ k) (hs : 4 * s ≤ k) :
    (FiniteLaw.independentBits (fun _ : I ↦ p) (fun _ ↦ hp)).probability
      (fun ω ↦ k ≤ (S.filter fun x ↦ ω x = true).card) ≤ ((2 : ℝ≥0) ^ s)⁻¹ := by
  have heq : ∀ ω : I → Bool, S.filter (fun x ↦ ω x = true) = activeBlocks (fun x ↦ ({x} : Finset I)) S ω := by
    intro ω
    ext x
    simp only [mem_filter, mem_activeBlocks_iff, IsBlockActive, mem_singleton, forall_eq]
  simp_rw [heq]
  exact independentBits_probability_activeBlocks_card_ge_le_dyadic
    (fun _ : I ↦ p) (fun _ ↦ hp) (fun x ↦ {x}) S
    (singleton_blocks_pairwiseDisjoint_of_injOn S id (fun _ _ _ _ h ↦ h)) p hp
    (fun _ _ ↦ by simp [blockProbability]) k s hk hs

theorem familyExtensions_sample_eq_filter
    {V : Type*} [Fintype V] [DecidableEq V]
    (F : ForbiddenFamilyOn V) (R : TripleSystemOn V) (ω : TripleSystemOn V → Bool) :
    familyExtensions (F.filter fun C ↦ ω C = true) R =
      (familyExtensions F R).filter fun C ↦ ω C = true := by
  ext C
  simp only [mem_familyExtensions_iff, mem_filter]
  tauto

theorem Vortex.terminalPairExtensions_sample_eq_filter
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    (W : Vortex V ell) (F : ForbiddenFamilyOn V) (T : TripleOn V) (P : VortexPairOn V)
    (ω : TripleSystemOn V → Bool) :
    W.terminalPairExtensions (F.filter fun C ↦ ω C = true) T P =
      (W.terminalPairExtensions F T P).filter fun C ↦ ω C = true := by
  ext C
  simp only [W.mem_terminalPairExtensions_iff, mem_filter]
  tauto

theorem probability_randomConfiguration_extensions_ge_le_dyadic
    {V : Type*} [Fintype V] [DecidableEq V] {ell j : ℕ}
    (W : Vortex V ell) (R : TripleSystemOn V) (p : ℝ≥0) (hp : p ≤ 1) (k s : ℕ)
    (hk : 4 * ((p : ℝ) * ((W.terminalSize : ℝ) ^ 3) ^ (j - 2 - R.card)) ≤ k)
    (hs : 4 * s ≤ k) :
    (FiniteLaw.independentBits (fun _ : TripleSystemOn V ↦ p) (fun _ ↦ hp)).probability
      (fun ω ↦ k ≤ (familyExtensions ((terminalRandomConfigurations W j).filter fun C ↦ ω C = true) R).card) ≤
        ((2 : ℝ≥0) ^ s)⁻¹ := by
  simp_rw [familyExtensions_sample_eq_filter]
  apply independentBits_probability_filter_card_ge_le_dyadic _ p hp k s ?_ hs
  apply le_trans ?_ hk
  have hcount : ((familyExtensions (terminalRandomConfigurations W j) R).card : ℝ) ≤
      ((W.terminalSize : ℝ) ^ 3) ^ (j - 2 - R.card) := by
    exact_mod_cast card_familyExtensions_terminalRandomConfigurations_le W R
  exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hcount p.coe_nonneg) (by norm_num)

theorem probability_randomConfiguration_terminalPair_ge_le_dyadic
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    (W : Vortex V ell) (T : TripleOn V) (P : VortexPairOn V) (p : ℝ≥0) (hp : p ≤ 1) (k s : ℕ)
    (hk : 4 * ((p : ℝ) * W.terminalSize) ≤ k) (hs : 4 * s ≤ k) :
    (FiniteLaw.independentBits (fun _ : TripleSystemOn V ↦ p) (fun _ ↦ hp)).probability
      (fun ω ↦ k ≤ (W.terminalPairExtensions
        ((terminalRandomConfigurations W 4).filter fun C ↦ ω C = true) T P).card) ≤
          ((2 : ℝ≥0) ^ s)⁻¹ := by
  simp_rw [W.terminalPairExtensions_sample_eq_filter]
  apply independentBits_probability_filter_card_ge_le_dyadic _ p hp k s ?_ hs
  apply le_trans ?_ hk
  have hcount : ((W.terminalPairExtensions (terminalRandomConfigurations W 4) T P).card : ℝ) ≤ W.terminalSize := by
    exact_mod_cast card_terminalPairExtensions_randomCandidates_le W T P
  exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hcount p.coe_nonneg) (by norm_num)

theorem probability_randomConfiguration_pairs_ge_le_dyadic
    {V : Type*} [Fintype V] [DecidableEq V] {ell j : ℕ}
    (W : Vortex V ell) (T T' : TripleOn V) (p : ℝ≥0) (hp : p ≤ 1) (k s : ℕ)
    (hk : 4 * ((p : ℝ) ^ 2 * ((W.terminalSize : ℝ) ^ 3) ^ (j - 3)) ≤ k)
    (hs : 4 * s ≤ k) :
    (FiniteLaw.independentBits (fun _ : TripleSystemOn V ↦ p) (fun _ ↦ hp)).probability
      (fun ω ↦ k ≤ (distinctEqualRemainderPairs
        ((terminalRandomConfigurations W j).filter fun C ↦ ω C = true) T T').card) ≤
          ((2 : ℝ≥0) ^ s)⁻¹ := by
  apply independentBits_probability_sampledConfigurationPairs_card_ge_le_dyadic _ T T' p hp k s ?_ hs
  apply le_trans ?_ hk
  have hcount : ((distinctEqualRemainderPairs (terminalRandomConfigurations W j) T T').card : ℝ) ≤
      ((W.terminalSize : ℝ) ^ 3) ^ (j - 3) := by
    exact_mod_cast card_distinctPairs_terminalRandomConfigurations_le W T T'
  exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hcount (sq_nonneg _)) (by norm_num)

end

end Erdos207
