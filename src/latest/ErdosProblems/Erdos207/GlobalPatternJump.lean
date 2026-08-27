/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.PatternLocalizedJump
import ErdosProblems.Erdos207.CrudeStateConsequences

/-! # The outer-level pattern jump follows from the existing global crude event -/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

def localizedTwoAwayToPair
    {V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {T : TripleOn V} {a b : V} {U : Finset V}
    (hpack : ∀ C ∈ F, IsPackingOn C) (hab : a ≠ b)
    (w : LocalizedTwoAwayWitness V F T a b U) :
    PairTwoAwayThreatWitness V F T ⟨{a, b}, by simp [hab]⟩ := by
  refine ⟨w.1, insert_subset w.2.1 (singleton_subset_iff.mpr w.2.2.1), ?_⟩
  intro hshare
  have hlo := mem_triplesSharingPair_iff.mp hshare
  have hhi := (hpack w.1.1.1 w.1.2.1).inter_card_le_one
    w.1.2.2.2.1 w.1.2.2.1 w.1.2.2.2.2.symm
  omega

theorem localizedTwoAwayToPair_injective
    {V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {T : TripleOn V} {a b : V} {U : Finset V}
    (hpack : ∀ C ∈ F, IsPackingOn C) (hab : a ≠ b) :
    Function.Injective (localizedTwoAwayToPair (T := T) (U := U) hpack hab) := by
  intro w z h
  apply Subtype.ext
  change (localizedTwoAwayToPair hpack hab w).1 = (localizedTwoAwayToPair hpack hab z).1
  exact congrArg (fun p : PairTwoAwayThreatWitness V F T ⟨{a, b}, by simp [hab]⟩ ↦ p.1) h

theorem localizedTwoAway_selectedCount_le_pair
    {V : Type*} [Fintype V] [DecidableEq V]
    (F : ForbiddenFamilyOn V) (T : TripleOn V) {a b : V} (U : Finset V) (A : TripleSystemOn V)
    (hpack : ∀ C ∈ F, IsPackingOn C) (hab : a ≠ b) :
    selectedCount (fun w : LocalizedTwoAwayWitness V F T a b U ↦ localizedTwoAwayRemainder w) A ≤
      selectedCount (fun w : PairTwoAwayThreatWitness V F T ⟨{a, b}, by simp [hab]⟩ ↦ pairTwoAwayThreatRemainder w) A := by
  unfold selectedCount
  exact sum_le_sum_of_injective_code (localizedTwoAwayToPair hpack hab)
    (localizedTwoAwayToPair_injective hpack hab) _ _ (fun _ ↦ le_rfl)

theorem CrudeStateBounds.pattern_loss_bound
    {V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {S : GreedyStateOn V} {q : ℕ} {K : CrudeThresholds}
    (h : CrudeStateBounds F S q K) (hS : GreedyInvariant F S)
    (hpack : ∀ C ∈ F, IsPackingOn C) (Q : SimpleGraph V) (U : Finset V)
    (T : TripleOn V) (hT : T ∈ patternSurvivalSelectors Q S) :
    ((patternExtensionLoss F Q U S T).card : ℝ≥0) ≤ 3 + (graphEdges Q).card * K.pair := by
  apply patternExtensionLoss_card_le_localized_cutoff hS Q U T hT K.pair
  intro e
  exact (localizedTwoAway_selectedCount_le_pair F T U S.chosen hpack
    (out_fst_ne_snd_of_mem_graphEdges e.2)).trans (h.pair T _).le

theorem global_pattern_loss_relative_scale
    (N t m : ℝ) (r k : ℕ) (ht : 1 ≤ t) (hm : 0 ≤ m)
    (hcoeff : 3 + m ≤ t) (hsize : t ^ (r + k + 1) ≤ N) :
    3 + m * t ^ k ≤ N / t ^ r := by
  have htpos : 0 < t := by linarith
  have hpow : 1 ≤ t ^ k := one_le_pow₀ ht
  calc
    _ ≤ (3 + m) * t ^ k := by nlinarith only [hpow]
    _ ≤ t * t ^ k := mul_le_mul_of_nonneg_right hcoeff (pow_nonneg htpos.le k)
    _ = t ^ (k + 1) := by rw [pow_succ]; ring
    _ ≤ N / t ^ r := by
      apply (le_div_iff₀ (pow_pos htpos r)).mpr
      have heq : t ^ (k + 1) * t ^ r = t ^ (r + k + 1) := by rw [← pow_add]; congr 1; omega
      simpa only [heq] using hsize

end

end Erdos207
