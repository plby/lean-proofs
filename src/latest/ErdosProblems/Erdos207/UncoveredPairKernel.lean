/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.AvailabilityUpperTrajectory
import ErdosProblems.Erdos207.GreedyClosedThreatDrift

/-! # Pair survival means remaining uncovered, even if its available star is empty -/

namespace Erdos207

open Finset

noncomputable section

def PairUncovered
    {V : Type*} [Fintype V] [DecidableEq V] (P : Finset V) (S : GreedyStateOn V) : Prop :=
  P ∉ chosenPairFinsets S

instance pairUncoveredDecidable
    {V : Type*} [Fintype V] [DecidableEq V] (P : Finset V) (S : GreedyStateOn V) :
    Decidable (PairUncovered P S) := inferInstanceAs (Decidable (P ∉ chosenPairFinsets S))

theorem pairUncovered_greedyStep_iff
    {V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {S : GreedyStateOn V} {P : Finset V} {T : TripleOn V}
    (hP : P.card = 2) (huncovered : PairUncovered P S) (hT : T ∈ S.available) :
    PairUncovered P (greedyStep F S T) ↔ T ∉ availableTrianglesContainingPair S P := by
  constructor
  · intro h hstar
    exact h (mem_chosenPairFinsets_iff.mpr ⟨T, mem_insert_self _ _,
      (mem_availableTrianglesContainingPair_iff.mp hstar).2, hP⟩)
  · intro h hcovered
    obtain ⟨U, hU, hPU, hPcard⟩ := mem_chosenPairFinsets_iff.mp hcovered
    change U ∈ insert T S.chosen at hU
    rcases mem_insert.mp hU with rfl | hU
    · exact h (mem_availableTrianglesContainingPair_iff.mpr ⟨hT, hPU⟩)
    · exact huncovered (mem_chosenPairFinsets_iff.mpr ⟨U, hU, hPU, hPcard⟩)

theorem greedyKernel_supported_pairCovered
    {V : Type*} [Fintype V] [DecidableEq V]
    (F : ForbiddenFamilyOn V) (S : GreedyStateOn V) (P : Finset V)
    (hcovered : ¬ PairUncovered P S) :
    (greedyKernel F S).SupportedOn (fun S' ↦ ¬ PairUncovered P S') := by
  intro S' hmass
  rcases greedyKernel_supported_step_or_self F S S' hmass with rfl | ⟨T, _, rfl⟩
  · exact hcovered
  · intro hnew
    apply hcovered
    intro hP
    obtain ⟨U, hU, hPU, hPcard⟩ := mem_chosenPairFinsets_iff.mp hP
    exact hnew (mem_chosenPairFinsets_iff.mpr ⟨U, mem_insert_of_mem hU, hPU, hPcard⟩)

theorem greedyKernel_expectationReal_pairUncovered
    {V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {S : GreedyStateOn V} (P : Finset V)
    (hP : P.card = 2) (huncovered : PairUncovered P S) (hA : S.available.Nonempty)
    (φ : GreedyStateOn V → ℝ) :
    (greedyKernel F S).expectationReal (fun S' ↦ if PairUncovered P S' then φ S' else 0) =
      (S.available.card : ℝ)⁻¹ *
        ∑ T ∈ S.available \ availableTrianglesContainingPair S P, φ (greedyStep F S T) := by
  rw [greedyKernel_expectationReal_of_nonempty F S hA]
  congr 1
  calc
    (∑ T : S.available,
        if PairUncovered P (greedyStep F S T.1) then φ (greedyStep F S T.1) else 0) =
        ∑ T : S.available,
          if T.1 ∉ availableTrianglesContainingPair S P then φ (greedyStep F S T.1) else 0 := by
      apply sum_congr rfl
      intro T _
      simp only [pairUncovered_greedyStep_iff hP huncovered T.2]
    _ = ∑ T ∈ S.available,
        if T ∉ availableTrianglesContainingPair S P then φ (greedyStep F S T) else 0 := by
      rw [Finset.univ_eq_attach]
      simpa only using! sum_attach S.available
        (fun T ↦ if T ∉ availableTrianglesContainingPair S P then φ (greedyStep F S T) else 0)
    _ = _ := by rw [sdiff_eq_filter, sum_filter]

theorem greedyKernel_expectationReal_pairUncovered_eq_restricted
    {V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {S : GreedyStateOn V} (P : Finset V)
    (hP : P.card = 2) (huncovered : PairUncovered P S) (hA : S.available.Nonempty)
    (hR : (S.available \ availableTrianglesContainingPair S P).Nonempty)
    (φ : GreedyStateOn V → ℝ) :
    (greedyKernel F S).expectationReal (fun S' ↦ if PairUncovered P S' then φ S' else 0) =
      ((S.available \ availableTrianglesContainingPair S P).card : ℝ) / S.available.card *
        (restrictedGreedyKernel F S (S.available \ availableTrianglesContainingPair S P) hR).expectationReal φ := by
  rw [greedyKernel_expectationReal_pairUncovered P hP huncovered hA,
    restrictedGreedyKernel_expectationReal]
  have hRpos : (0 : ℝ) < (S.available \ availableTrianglesContainingPair S P).card := by
    exact_mod_cast card_pos.mpr hR
  field_simp

theorem greedyKernel_expectationReal_pairUncovered_le_of_restricted
    {V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {S : GreedyStateOn V} (P : Finset V)
    (hP : P.card = 2) (huncovered : PairUncovered P S) (hA : S.available.Nonempty)
    (φ : GreedyStateOn V → ℝ) (v : ℝ) (hv : 0 ≤ v)
    (hbound : ∀ hR : (S.available \ availableTrianglesContainingPair S P).Nonempty,
      (restrictedGreedyKernel F S (S.available \ availableTrianglesContainingPair S P) hR).expectationReal φ ≤ v) :
    (greedyKernel F S).expectationReal (fun S' ↦ if PairUncovered P S' then φ S' else 0) ≤ v := by
  by_cases hR : (S.available \ availableTrianglesContainingPair S P).Nonempty
  · rw [greedyKernel_expectationReal_pairUncovered_eq_restricted P hP huncovered hA hR]
    have hApos : (0 : ℝ) < S.available.card := by exact_mod_cast card_pos.mpr hA
    have hratio : ((S.available \ availableTrianglesContainingPair S P).card : ℝ) / S.available.card ≤ 1 := by
      apply (div_le_one hApos).mpr
      exact_mod_cast card_le_card (sdiff_subset :
        S.available \ availableTrianglesContainingPair S P ⊆ S.available)
    calc
      _ ≤ (((S.available \ availableTrianglesContainingPair S P).card : ℝ) / S.available.card) * v :=
        mul_le_mul_of_nonneg_left (hbound hR) (by positivity)
      _ ≤ 1 * v := mul_le_mul_of_nonneg_right hratio hv
      _ = v := one_mul v
  · rw [greedyKernel_expectationReal_pairUncovered P hP huncovered hA,
      not_nonempty_iff_eq_empty.mp hR, sum_empty, mul_zero]
    exact hv

end

end Erdos207
