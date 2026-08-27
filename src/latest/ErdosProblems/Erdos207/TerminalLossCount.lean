/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.TerminalLossWitnesses
import ErdosProblems.Erdos207.RootedThreatAbsorberBound

/-! # A multiplicity-preserving terminal loss bound -/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

theorem card_pairInsideSelector
    {V : Type*} [Fintype V] [DecidableEq V] (T : TripleOn V) :
    Fintype.card (PairInsideSelector T) = 3 := by
  let e : PairInsideSelector T ≃ T.1.powersetCard 2 :=
    { toFun := fun P ↦ ⟨P.1.1, mem_powersetCard.mpr ⟨P.2, P.1.2⟩⟩
      invFun := fun P ↦ ⟨⟨P.1, (mem_powersetCard.mp P.2).2⟩, (mem_powersetCard.mp P.2).1⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }
  rw [Fintype.card_congr e, Fintype.card_coe, card_powersetCard, T.2]
  norm_num

theorem selectedCount_terminalLossWitness_eq
    {V : Type*} [Fintype V] [DecidableEq V]
    (F : ForbiddenFamilyOn V) (root T : TripleOn V) (A : TripleSystemOn V) :
    selectedCount (terminalLossWitnessRemainder (F := F) (root := root) (T := T)) A =
      (∑ P : PairInsideSelector T,
        selectedCount (fun w : PairTwoAwayThreatWitness V F root P.1 ↦ pairTwoAwayThreatRemainder w) A) +
      selectedCount (fun w : CommonThreatWitness F F root T ↦ w.remainder) A := by
  unfold selectedCount TerminalLossWitness
  rw [Fintype.sum_sum_type, Fintype.sum_sigma]
  rfl

theorem terminal_configuration_losses_card_le_selectedCount
    {V : Type*} [Fintype V] [DecidableEq V]
    {F J : ForbiddenFamilyOn V} {S : GreedyStateOn V} {root T : TripleOn V} {c : ℕ}
    (hS : GreedyInvariant F S) (hroot : root ∈ S.available)
    (hT : T ∈ S.available \ greedyClosedThreats F S root)
    (hJ : J ⊆ F) (hpack : ∀ C ∈ J, IsPackingOn C) (hcard : ∀ C ∈ J, C.card = c + 2) :
    ((greedyConfigurationLosses F J S root c T).card : ℝ≥0) ≤
      (∑ P : PairInsideSelector T,
        selectedCount (fun w : PairTwoAwayThreatWitness V F root P.1 ↦ pairTwoAwayThreatRemainder w) S.chosen) +
      selectedCount (fun w : CommonThreatWitness F F root T ↦ w.remainder) S.chosen := by
  classical
  have hex : ∀ C : greedyConfigurationLosses F J S root c T,
      ∃ w : TerminalLossWitness V F root T,
        terminalLossWitnessFirst w = C.1 ∧ terminalLossWitnessRemainder w ⊆ S.chosen := by
    intro C
    have hCJ := (mem_greedyConfigurationClass.mp (mem_sdiff.mp C.2).1).1
    exact exists_terminalLossWitness_of_loss hS hroot hT hJ (hpack C.1 hCJ) (hcard C.1 hCJ) C.2
  let code := fun C : greedyConfigurationLosses F J S root c T ↦ (hex C).choose
  have hcode : ∀ C, terminalLossWitnessFirst (code C) = C.1 := fun C ↦ (hex C).choose_spec.1
  have hrem : ∀ C, terminalLossWitnessRemainder (code C) ⊆ S.chosen := fun C ↦ (hex C).choose_spec.2
  have hinj : Function.Injective code := by
    intro C D h
    apply Subtype.ext
    exact (hcode C).symm.trans ((congrArg terminalLossWitnessFirst h).trans (hcode D))
  have h := sum_le_sum_of_injective_code code hinj (fun _ ↦ 1)
    (fun w ↦ if terminalLossWitnessRemainder w ⊆ S.chosen then 1 else 0) (by
      intro C
      rw [if_pos (hrem C)])
  have h' : ((greedyConfigurationLosses F J S root c T).card : ℝ≥0) ≤
      selectedCount (terminalLossWitnessRemainder (F := F) (root := root) (T := T)) S.chosen := by
    simpa only [selectedCount, sum_const, card_univ, Fintype.card_coe, nsmul_eq_mul, mul_one] using h
  exact h'.trans_eq (selectedCount_terminalLossWitness_eq F root T S.chosen)

theorem terminal_configuration_losses_card_le_moment_cutoffs
    {V : Type*} [Fintype V] [DecidableEq V]
    {F J : ForbiddenFamilyOn V} {S : GreedyStateOn V} {root T : TripleOn V} {c : ℕ}
    (hS : GreedyInvariant F S) (hroot : root ∈ S.available)
    (hT : T ∈ S.available \ greedyClosedThreats F S root)
    (hJ : J ⊆ F) (hpack : ∀ C ∈ J, IsPackingOn C) (hcard : ∀ C ∈ J, C.card = c + 2)
    (P Q : ℝ≥0)
    (hpair : ∀ p : PairInsideSelector T,
      selectedCount (fun w : PairTwoAwayThreatWitness V F root p.1 ↦ pairTwoAwayThreatRemainder w) S.chosen ≤ P)
    (hcommon : selectedCount (fun w : CommonThreatWitness F F root T ↦ w.remainder) S.chosen ≤ Q) :
    ((greedyConfigurationLosses F J S root c T).card : ℝ≥0) ≤ 3 * P + Q := by
  refine (terminal_configuration_losses_card_le_selectedCount hS hroot hT hJ hpack hcard).trans ?_
  apply add_le_add _ hcommon
  calc
    _ ≤ ∑ _p : PairInsideSelector T, P := sum_le_sum fun p _ ↦ hpair p
    _ = _ := by simp only [sum_const, card_univ, card_pairInsideSelector, nsmul_eq_mul]; norm_num

end

end Erdos207
