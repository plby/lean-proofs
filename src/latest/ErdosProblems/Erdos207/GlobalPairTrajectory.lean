/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.AvailabilityUpperTrajectory
import ErdosProblems.Erdos207.DriftErrorArithmetic
import ErdosProblems.Erdos207.GreedyClosedThreats

/-! # Recovering global availability and selector denominators from pair trajectories -/

namespace Erdos207

open Finset

noncomputable section

theorem sum_pairSet_card_available
    {V : Type*} [Fintype V] [DecidableEq V]
    (S : GreedyStateOn V) (Q : Finset (Finset V))
    (hQ : ∀ P ∈ Q, P.card = 2)
    (hcover : ∀ P : Finset V, P.card = 2 → (availableTrianglesContainingPair S P).Nonempty → P ∈ Q) :
    ∑ P ∈ Q, (availableTrianglesContainingPair S P).card = 3 * S.available.card := by
  have hsub : Q ⊆ (univ : Finset V).powersetCard 2 := by
    intro P hP
    exact mem_powersetCard.mpr ⟨subset_univ _, hQ P hP⟩
  have hzero : ∀ P ∈ (univ : Finset V).powersetCard 2, P ∉ Q →
      (availableTrianglesContainingPair S P).card = 0 := by
    intro P hP hn
    by_contra h
    exact hn (hcover P (mem_powersetCard.mp hP).2 (card_ne_zero.mp h))
  exact (sum_subset hsub hzero).trans (sum_allPairs_card_availableTrianglesContainingPair S)

theorem abs_available_sub_pair_trajectory_le
    {V : Type*} [Fintype V] [DecidableEq V]
    (S : GreedyStateOn V) (Q : Finset (Finset V)) (x epsilon : ℝ)
    (hQ : ∀ P ∈ Q, P.card = 2)
    (hcover : ∀ P : Finset V, P.card = 2 → (availableTrianglesContainingPair S P).Nonempty → P ∈ Q)
    (hpair : ∀ P ∈ Q, |((availableTrianglesContainingPair S P).card : ℝ) - x| ≤ epsilon) :
    |(S.available.card : ℝ) - Q.card * x / 3| ≤ Q.card * epsilon / 3 := by
  have hs := abs_sum_sub_card_mul_le_sum_error Q
    (fun P ↦ ((availableTrianglesContainingPair S P).card : ℝ)) (fun _ ↦ epsilon) x hpair
  have he : (∑ P ∈ Q, ((availableTrianglesContainingPair S P).card : ℝ)) =
      3 * (S.available.card : ℝ) := by exact_mod_cast sum_pairSet_card_available S Q hQ hcover
  rw [he, sum_const, nsmul_eq_mul] at hs
  have hid : (S.available.card : ℝ) - Q.card * x / 3 =
      (3 * (S.available.card : ℝ) - Q.card * x) / 3 := by ring
  rw [hid, abs_div, show |(3 : ℝ)| = 3 by norm_num]
  exact div_le_div_of_nonneg_right hs (by norm_num)

theorem residualPairSet_covers_available
    {V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {S : GreedyStateOn V} (Q₀ : Finset (Finset V))
    (hS : GreedyInvariant F S)
    (hcover : ∀ T ∈ S.available, ∀ P : Finset V, P.card = 2 → P ⊆ T.1 → P ∈ Q₀)
    {P : Finset V} (hP : P.card = 2) (hstar : (availableTrianglesContainingPair S P).Nonempty) :
    P ∈ Q₀ \ chosenPairFinsets S := by
  obtain ⟨T, hT⟩ := hstar
  have ht := mem_availableTrianglesContainingPair_iff.mp hT
  refine mem_sdiff.mpr ⟨hcover T ht.1 P hP ht.2, ?_⟩
  intro hchosen
  have he := availableTrianglesContainingPair_eq_empty_of_mem_chosenPairFinsets hS hchosen
  rw [he] at hT
  simpa using hT

theorem residualPairSet_card_add_chosen
    {V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {S : GreedyStateOn V} (Q₀ : Finset (Finset V))
    (hS : GreedyInvariant F S) (hchosen : chosenPairFinsets S ⊆ Q₀) :
    (Q₀ \ chosenPairFinsets S).card + 3 * S.chosen.card = Q₀.card := by
  have h := card_sdiff_add_card_eq_card hchosen
  rw [card_chosenPairFinsets_of_isPackingOn hS.1] at h
  exact h

theorem abs_rootPreserving_card_sub_target_le
    {V : Type*} [Fintype V] [DecidableEq V]
    (F : ForbiddenFamilyOn V) (S : GreedyStateOn V) (T : TripleOn V)
    (A H epsilonA epsilonH : ℝ)
    (hA : |(S.available.card : ℝ) - A| ≤ epsilonA)
    (hH : |((greedyClosedThreats F S T).card : ℝ) - H| ≤ epsilonH) :
    |((S.available \ greedyClosedThreats F S T).card : ℝ) - A| ≤ epsilonA + |H| + epsilonH := by
  have hsub : greedyClosedThreats F S T ⊆ S.available := inter_subset_left
  rw [card_sdiff_of_subset hsub, Nat.cast_sub (card_le_card hsub)]
  have hh : |((greedyClosedThreats F S T).card : ℝ)| ≤ |H| + epsilonH := by
    have he : ((greedyClosedThreats F S T).card : ℝ) =
        (((greedyClosedThreats F S T).card : ℝ) - H) + H := by ring
    calc
      _ = |(((greedyClosedThreats F S T).card : ℝ) - H) + H| := congrArg abs he
      _ ≤ |((greedyClosedThreats F S T).card : ℝ) - H| + |H| := abs_add_le _ _
      _ ≤ _ := by linarith
  have hid : (S.available.card : ℝ) - (greedyClosedThreats F S T).card - A =
      ((S.available.card : ℝ) - A) - (greedyClosedThreats F S T).card := by ring
  rw [hid]
  exact (abs_sub _ _).trans ((add_le_add hA hh).trans_eq (by ring))

end

end Erdos207
