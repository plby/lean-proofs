/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.SourceRandomGoodCounts

/-! # Increment counts retained independently of the original spread coefficient -/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

structure SourceAugmentationCounts
    {V : Type*} [Fintype V] [DecidableEq V]
    (j n : ℕ) (F G : ForbiddenFamilyOn V) (a : ℝ≥0) : Prop where
  uniform : ∀ E ∈ G, E.card = j - 2 ∧ IsPackingOn E
  roots : ∀ R : TripleSystemOn V, R.Nonempty → R.card ≤ j - 2 →
    ((familyExtensions G R).card : ℝ≥0) ≤ a * (n : ℝ≥0) ^ (j - vortexRootExponent j R.card)
  pairs : ∀ T T' : TripleOn V,
    ((distinctEqualRemainderPairs G T T').card : ℝ≥0) ≤ a * (n : ℝ≥0) ^ (j - 4)
  old_new : ∀ T T' : TripleOn V,
    ((crossDistinctConfigurationPairs F G T T').card : ℝ≥0) ≤ a * (n : ℝ≥0) ^ (j - 4)
  new_old : ∀ T T' : TripleOn V,
    ((crossDistinctConfigurationPairs G F T T').card : ℝ≥0) ≤ a * (n : ℝ≥0) ^ (j - 4)

theorem SourceRandomCountsGood.augmentationCounts
    {V : Type*} [Fintype V] [DecidableEq V] {ell j : ℕ}
    {W : Vortex V ell} {F : ForbiddenFamilyOn V} {a : ℝ≥0}
    {omega : TripleSystemOn V → Bool} (hgood : SourceRandomCountsGood W j F a omega) :
    SourceAugmentationCounts j W.terminalSize F (sampleTerminalConfigurations W j omega) a := by
  refine ⟨fun E hE ↦ terminalRandomConfigurations_uniform W E (mem_filter.mp hE).1,
    ?_, fun T T' ↦ (hgood.2.1 T T').1, fun T T' ↦ (hgood.2.1 T T').2.1,
    fun T T' ↦ (hgood.2.1 T T').2.2⟩
  intro R hR hRcard
  by_cases hsub : R ⊆ triplesSupportedOn (W.U (Fin.last ell))
  · exact hgood.1 R (mem_subsetsUpToCard_iff.mpr ⟨hsub, hRcard⟩) hR
  · rw [familyExtensions_sample_eq_empty_of_not_terminal_root W R omega hsub]
    simp

theorem SourceAugmentationCounts.mono
    {V : Type*} [Fintype V] [DecidableEq V] {j n : ℕ}
    {F G G' : ForbiddenFamilyOn V} {a : ℝ≥0}
    (h : SourceAugmentationCounts j n F G a) (hsub : G' ⊆ G) :
    SourceAugmentationCounts j n F G' a := by
  refine ⟨fun E hE ↦ h.uniform E (hsub hE), ?_, ?_, ?_, ?_⟩
  · intro R hR hRcard
    have hc : ((familyExtensions G' R).card : ℝ≥0) ≤ (familyExtensions G R).card := by
      exact_mod_cast card_le_card (filter_subset_filter _ hsub)
    exact hc.trans (h.roots R hR hRcard)
  · intro T T'
    have hc : ((distinctEqualRemainderPairs G' T T').card : ℝ≥0) ≤ (distinctEqualRemainderPairs G T T').card := by
      apply Nat.cast_le.mpr
      apply card_le_card
      intro p hp
      obtain ⟨h1, h2, hne, hT, hT', hrem⟩ := mem_distinctEqualRemainderPairs_iff.mp hp
      exact mem_distinctEqualRemainderPairs_iff.mpr ⟨hsub h1, hsub h2, hne, hT, hT', hrem⟩
    exact hc.trans (h.pairs T T')
  · intro T T'
    have hc : ((crossDistinctConfigurationPairs F G' T T').card : ℝ≥0) ≤
        (crossDistinctConfigurationPairs F G T T').card := by
      apply Nat.cast_le.mpr
      apply card_le_card
      intro p hp
      obtain ⟨h1, h2, hne, hT, hT', hrem⟩ := mem_crossDistinctConfigurationPairs_iff.mp hp
      exact mem_crossDistinctConfigurationPairs_iff.mpr ⟨h1, hsub h2, hne, hT, hT', hrem⟩
    exact hc.trans (h.old_new T T')
  · intro T T'
    have hc : ((crossDistinctConfigurationPairs G' F T T').card : ℝ≥0) ≤
        (crossDistinctConfigurationPairs G F T T').card := by
      apply Nat.cast_le.mpr
      apply card_le_card
      intro p hp
      obtain ⟨h1, h2, hne, hT, hT', hrem⟩ := mem_crossDistinctConfigurationPairs_iff.mp hp
      exact mem_crossDistinctConfigurationPairs_iff.mpr ⟨hsub h1, h2, hne, hT, hT', hrem⟩
    exact hc.trans (h.new_old T T')

end

end Erdos207
