/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.CrudeStateConsequences
import ErdosProblems.Erdos207.GreedyConfigurationJump

/-! # Configuration jumps from the first, second, and third crude cutoffs -/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

def crudeConfigurationLossCutoff (K : CrudeThresholds) (H : ℝ≥0) (j c : ℕ) : ℝ≥0 :=
  if c + 4 = j then 3 * K.pair + K.common else H * K.rooted j c

namespace CrudeStateBounds

variable {V : Type*} [Fintype V] [DecidableEq V]
  {F : ForbiddenFamilyOn V} {S : GreedyStateOn V} {q : ℕ} {K : CrudeThresholds}

theorem configuration_gain
    (h : CrudeStateBounds F S q K) (j c : ℕ) (hj : j ≤ q) (hc : c + 5 ≤ j)
    {root T : TripleOn V} (hroot : root ∈ S.available)
    (hT : T ∈ S.available \ greedyClosedThreats F S root) :
    ((greedyConfigurationGains F (forbiddenFamilyOfOrder F j) S root c T).card : ℝ≥0) ≤ K.rooted j c := by
  have hne : root ≠ T := by
    intro he
    subst T
    exact (mem_sdiff.mp hT).2 (mem_greedyClosedThreats_self F S hroot)
  have hsub := greedyConfigurationGains_subset_twoRootClass
    (F := F) (J := forbiddenFamilyOfOrder F j) (c := c) hroot (mem_sdiff.mp hT).1
  have hcount : ((greedyConfigurationGains F (forbiddenFamilyOfOrder F j) S root c T).card : ℝ≥0) ≤
      (greedyRootedConfigurationClass (forbiddenFamilyOfOrder F j) S {root, T} c).card := by
    exact_mod_cast card_le_card hsub
  exact hcount.trans (h.rooted j c root T hj hc hne).le

theorem configuration_nonterminal_loss
    (h : CrudeStateBounds F S q K) (j c : ℕ) (hj : j ≤ q) (hc : c + 5 ≤ j)
    (H : ℝ≥0) (hS : GreedyInvariant F S) {root T : TripleOn V}
    (hroot : root ∈ S.available) (hT : T ∈ S.available \ greedyClosedThreats F S root)
    (hthreat : ((greedyClosedThreats F S T).card : ℝ≥0) ≤ H) :
    ((greedyConfigurationLosses F (forbiddenFamilyOfOrder F j) S root c T).card : ℝ≥0) ≤
      H * K.rooted j c := by
  have hsub := greedyConfigurationLosses_subset_threat_twoRootClasses
    (J := forbiddenFamilyOfOrder F j) (c := c) hS hroot hT
  calc
    _ ≤ ∑ U ∈ (greedyClosedThreats F S T).erase root,
        ((greedyRootedConfigurationClass (forbiddenFamilyOfOrder F j) S {root, U} c).card : ℝ≥0) := by
      exact_mod_cast (card_le_card hsub).trans (card_biUnion_le)
    _ ≤ ∑ _U ∈ (greedyClosedThreats F S T).erase root, K.rooted j c := by
      apply sum_le_sum
      intro U hU
      exact (h.rooted j c root U hj hc (Ne.symm (mem_erase.mp hU).1)).le
    _ = ((greedyClosedThreats F S T).erase root).card * K.rooted j c := by simp
    _ ≤ (greedyClosedThreats F S T).card * K.rooted j c := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact_mod_cast card_le_card (erase_subset root (greedyClosedThreats F S T))
    _ ≤ H * K.rooted j c := mul_le_mul_of_nonneg_right hthreat (by positivity)

theorem configuration_loss
    (h : CrudeStateBounds F S q K) (j c : ℕ) (hj : j ≤ q) (hc : c + 4 ≤ j)
    (H : ℝ≥0) (hS : GreedyInvariant F S) (hpack : ∀ E ∈ F, IsPackingOn E)
    {root T : TripleOn V} (hroot : root ∈ S.available)
    (hT : T ∈ S.available \ greedyClosedThreats F S root)
    (hthreat : ((greedyClosedThreats F S T).card : ℝ≥0) ≤ H) :
    ((greedyConfigurationLosses F (forbiddenFamilyOfOrder F j) S root c T).card : ℝ≥0) ≤
      crudeConfigurationLossCutoff K H j c := by
  unfold crudeConfigurationLossCutoff
  split_ifs with he
  · have hce : c = j - 4 := by omega
    rw [hce]
    exact h.terminal_loss hS hpack hroot hT j (by omega)
  · exact h.configuration_nonterminal_loss j c hj (by omega) H hS hroot hT hthreat

theorem configuration_succ_jump
    (h : CrudeStateBounds F S q K) (j c : ℕ) (hj : j ≤ q) (hc : c + 5 ≤ j)
    (H : ℝ≥0) (hS : GreedyInvariant F S) (hpack : ∀ E ∈ F, IsPackingOn E)
    {root T : TripleOn V} (hroot : root ∈ S.available)
    (hT : T ∈ S.available \ greedyClosedThreats F S root)
    (hthreat : ((greedyClosedThreats F S T).card : ℝ≥0) ≤ H) :
    |((greedyConfigurationClass (forbiddenFamilyOfOrder F j) (greedyStep F S T) root (c + 1)).card : ℝ) -
      (greedyConfigurationClass (forbiddenFamilyOfOrder F j) S root (c + 1)).card| ≤
        max (K.rooted j c : ℝ) (crudeConfigurationLossCutoff K H j (c + 1) : ℝ) := by
  rw [greedyConfigurationClass_increment_succ c hS (mem_sdiff.mp hT).1]
  have hg : ((greedyConfigurationGains F (forbiddenFamilyOfOrder F j) S root c T).card : ℝ) ≤ K.rooted j c := by
    exact_mod_cast h.configuration_gain j c hj hc hroot hT
  have hl : ((greedyConfigurationLosses F (forbiddenFamilyOfOrder F j) S root (c + 1) T).card : ℝ) ≤
      crudeConfigurationLossCutoff K H j (c + 1) := by
    exact_mod_cast h.configuration_loss j (c + 1) hj (by omega) H hS hpack hroot hT hthreat
  have hgmax := hg.trans (le_max_left _ (crudeConfigurationLossCutoff K H j (c + 1) : ℝ))
  have hlmax := hl.trans (le_max_right (K.rooted j c : ℝ) _)
  have hg0 : (0 : ℝ) ≤ (greedyConfigurationGains F (forbiddenFamilyOfOrder F j) S root c T).card := Nat.cast_nonneg _
  have hl0 : (0 : ℝ) ≤ (greedyConfigurationLosses F (forbiddenFamilyOfOrder F j) S root (c + 1) T).card := Nat.cast_nonneg _
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem configuration_zero_jump
    (h : CrudeStateBounds F S q K) (j : ℕ) (hj : j ≤ q) (hc : 4 ≤ j)
    (H : ℝ≥0) (hS : GreedyInvariant F S) (hpack : ∀ E ∈ F, IsPackingOn E)
    {root T : TripleOn V} (hroot : root ∈ S.available)
    (hT : T ∈ S.available \ greedyClosedThreats F S root)
    (hthreat : ((greedyClosedThreats F S T).card : ℝ≥0) ≤ H) :
    |((greedyConfigurationClass (forbiddenFamilyOfOrder F j) (greedyStep F S T) root 0).card : ℝ) -
      (greedyConfigurationClass (forbiddenFamilyOfOrder F j) S root 0).card| ≤
        (crudeConfigurationLossCutoff K H j 0 : ℝ) := by
  rw [greedyConfigurationClass_increment_zero hS (mem_sdiff.mp hT).1, abs_neg,
    abs_of_nonneg (Nat.cast_nonneg _)]
  exact_mod_cast h.configuration_loss j 0 hj hc H hS hpack hroot hT hthreat

end CrudeStateBounds

end

end Erdos207
