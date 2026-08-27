/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.GainDefectWitness
import ErdosProblems.Erdos207.MinimalGainDefect
import ErdosProblems.Erdos207.RootedThreatAbsorberBound

/-! # Encoding actual noncontained gain defects into fourth-moment witnesses -/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

def greedyGainDefectPairs
    {V : Type*} [Fintype V] [DecidableEq V]
    (J G : ForbiddenFamilyOn V) (S : GreedyStateOn V) (T : TripleOn V) (c : ℕ) :
    Finset (TripleSystemOn V × TripleSystemOn V) := by
  classical
  exact (greedyConfigurationClass J S T c ×ˢ G).filter fun p ↦
    p.2 ∈ greedyConfigurationRedundantWitnesses G S p.1 ∧ ¬ p.2 ⊆ p.1

def greedyGainDefectPairWitness
    {V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} (J G : ForbiddenFamilyOn V) (S : GreedyStateOn V)
    (T : TripleOn V) (c m : ℕ) (hS : GreedyInvariant F S) (hT : T ∈ S.available)
    (hJ : ∀ E ∈ J, E.card = m) (p : greedyGainDefectPairs J G S T c) :
    GainDefectWitness J G T (m - c - 1) := by
  classical
  have hd := mem_filter.mp p.2
  have hC := (mem_product.mp hd.1).1
  have hclass := mem_greedyConfigurationClass.mp hC
  have hD := mem_filter.mp hd.2.1
  have hTA : T ∈ p.1.1 ∩ S.available := mem_inter.mpr ⟨hclass.2.1, hT⟩
  refine ⟨p.1.1, p.1.2, (p.1.1 ∩ S.available).erase T, hclass.1, hD.1,
    hclass.2.1, ?_, ?_, ?_, hd.2.2⟩
  · intro U hU
    have hu := mem_erase.mp hU
    exact mem_erase.mpr ⟨hu.1, (mem_inter.mp hu.2).1⟩
  · rw [card_erase_of_mem hTA]
    have hc := greedyConfigurationClass_available_card hS hC
    rw [hJ p.1.1 hclass.1] at hc
    omega
  · rw [insert_erase hTA]
    have he : p.1.2 ∩ (p.1.1 ∩ S.available) = p.1.2 ∩ S.available := by
      apply Subset.antisymm
      · intro U hU
        exact mem_inter.mpr ⟨(mem_inter.mp hU).1, (mem_inter.mp (mem_inter.mp hU).2).2⟩
      · intro U hU
        exact mem_inter.mpr ⟨(mem_inter.mp hU).1, hD.2.2.2.1 hU⟩
    rw [he]
    exact hD.2.2.1

theorem greedyGainDefectPairWitness_remainder_subset
    {V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} (J G : ForbiddenFamilyOn V) (S : GreedyStateOn V)
    (T : TripleOn V) (c m : ℕ) (hS : GreedyInvariant F S) (hT : T ∈ S.available)
    (hJ : ∀ E ∈ J, E.card = m) (p : greedyGainDefectPairs J G S T c) :
    (greedyGainDefectPairWitness J G S T c m hS hT hJ p).remainder ⊆ S.chosen := by
  classical
  have hd := mem_filter.mp p.2
  have hclass := mem_greedyConfigurationClass.mp (mem_product.mp hd.1).1
  have hD := mem_filter.mp hd.2.1
  have hTA : T ∈ p.1.1 ∩ S.available := mem_inter.mpr ⟨hclass.2.1, hT⟩
  rw [GainDefectWitness.remainder_eq_sdiff]
  change (p.1.1 ∪ p.1.2) \ insert T ((p.1.1 ∩ S.available).erase T) ⊆ S.chosen
  rw [insert_erase hTA]
  intro U hU
  obtain ⟨hUC, hnot⟩ := mem_sdiff.mp hU
  rcases mem_union.mp hUC with hfirst | hsecond
  · rcases mem_union.mp (hclass.2.2.2 hfirst) with hchosen | havail
    · exact hchosen
    · exact (hnot (mem_inter.mpr ⟨hfirst, havail⟩)).elim
  · apply hD.2.2.2.2 (mem_sdiff.mpr ⟨hsecond, ?_⟩)
    intro havail
    exact hnot (hD.2.2.2.1 (mem_inter.mpr ⟨hsecond, havail⟩))

theorem greedyGainDefectPairWitness_injective
    {V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} (J G : ForbiddenFamilyOn V) (S : GreedyStateOn V)
    (T : TripleOn V) (c m : ℕ) (hS : GreedyInvariant F S) (hT : T ∈ S.available)
    (hJ : ∀ E ∈ J, E.card = m) :
    Function.Injective (greedyGainDefectPairWitness J G S T c m hS hT hJ) := by
  intro p u h
  apply Subtype.ext
  exact Prod.ext (congrArg (fun w ↦ w.first) h) (congrArg (fun w ↦ w.second) h)

theorem greedyGainDefectPairs_card_le_selectedCount
    {V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} (J G : ForbiddenFamilyOn V) (S : GreedyStateOn V)
    (T : TripleOn V) (c m : ℕ) (hS : GreedyInvariant F S) (hT : T ∈ S.available)
    (hJ : ∀ E ∈ J, E.card = m) :
    ((greedyGainDefectPairs J G S T c).card : ℝ≥0) ≤
      selectedCount (fun w : GainDefectWitness J G T (m - c - 1) ↦ w.remainder) S.chosen := by
  classical
  have h := sum_le_sum_of_injective_code
    (greedyGainDefectPairWitness J G S T c m hS hT hJ)
    (greedyGainDefectPairWitness_injective J G S T c m hS hT hJ)
    (fun _ ↦ 1) (fun w ↦ if w.remainder ⊆ S.chosen then 1 else 0) (by
      intro p
      rw [if_pos (greedyGainDefectPairWitness_remainder_subset J G S T c m hS hT hJ p)])
  simpa only [selectedCount, sum_const, card_univ, Fintype.card_coe, nsmul_eq_mul, mul_one] using h

/-- Root-indexed counts are only tracked while the root is available. -/
def greedyActiveGainDefectCount
    {V : Type*} [Fintype V] [DecidableEq V]
    (J G : ForbiddenFamilyOn V) (S : GreedyStateOn V) (T : TripleOn V) (c : ℕ) : ℕ :=
  if T ∈ S.available then (greedyGainDefectPairs J G S T c).card else 0

theorem greedyActiveGainDefectCount_le_selectedCount
    {V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} (J G : ForbiddenFamilyOn V) (S : GreedyStateOn V)
    (T : TripleOn V) (c m : ℕ) (hS : GreedyInvariant F S) (hJ : ∀ E ∈ J, E.card = m) :
    (greedyActiveGainDefectCount J G S T c : ℝ≥0) ≤
      selectedCount (fun w : GainDefectWitness J G T (m - c - 1) ↦ w.remainder) S.chosen := by
  by_cases hT : T ∈ S.available
  · simp only [greedyActiveGainDefectCount, if_pos hT]
    exact greedyGainDefectPairs_card_le_selectedCount J G S T c m hS hT hJ
  · simp only [greedyActiveGainDefectCount, if_neg hT, Nat.cast_zero]
    exact zero_le

theorem card_greedyGainDefectPairs_eq_sum_of_noncontainment
    {V : Type*} [Fintype V] [DecidableEq V]
    (J G : ForbiddenFamilyOn V) (S : GreedyStateOn V) (T : TripleOn V) (c : ℕ)
    (hnot : ∀ C ∈ greedyConfigurationClass J S T c,
      ∀ D ∈ greedyConfigurationRedundantWitnesses G S C, ¬ D ⊆ C) :
    (greedyGainDefectPairs J G S T c).card =
      ∑ C ∈ greedyConfigurationClass J S T c, (greedyConfigurationRedundantWitnesses G S C).card := by
  classical
  unfold greedyGainDefectPairs
  rw [card_eq_sum_ones, sum_filter, sum_product]
  apply sum_congr rfl
  intro C hC
  calc
    _ = ∑ D ∈ G, if D ∈ greedyConfigurationRedundantWitnesses G S C then (1 : ℕ) else 0 := by
      apply sum_congr rfl
      intro D _
      by_cases hD : D ∈ greedyConfigurationRedundantWitnesses G S C
      · simp [hD, hnot C hC D hD]
      · simp only [hD, false_and, if_false]
    _ = _ := by
      rw [← sum_filter, sum_const, nsmul_eq_mul, mul_one]
      have he : {D ∈ G | D ∈ greedyConfigurationRedundantWitnesses G S C} =
          greedyConfigurationRedundantWitnesses G S C := by
        ext D
        simp only [mem_filter]
        exact and_iff_right_of_imp (fun h ↦ (mem_filter.mp h).1)
      simp only [he, Nat.cast_id]

theorem card_greedyGainDefectPairs_minimal_eq_sum
    {V : Type*} [Fintype V] [DecidableEq V]
    (F J : ForbiddenFamilyOn V) (S : GreedyStateOn V) (T : TripleOn V) (c : ℕ)
    (hJ : J ⊆ minimalForbiddenFamily F) :
    (greedyGainDefectPairs J (minimalForbiddenFamily F) S T c).card =
      ∑ C ∈ greedyConfigurationClass J S T c,
        (greedyConfigurationRedundantWitnesses (minimalForbiddenFamily F) S C).card := by
  apply card_greedyGainDefectPairs_eq_sum_of_noncontainment
  intro C hC D hD
  exact redundantWitness_not_subset_of_minimal (hJ (mem_greedyConfigurationClass.mp hC).1) hD

end

end Erdos207
