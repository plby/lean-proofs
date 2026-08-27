/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.AbsorberUniformRootCount

/-! # The singleton-root saving for a nonempty absorber-bank part -/

namespace Erdos207

open Finset

noncomputable section

def derivedAbsorberConfigurations
    {V : Type*} [Fintype V] [DecidableEq V]
    (q j : ℕ) (B : TripleSystemOn V) : ForbiddenFamilyOn V := by
  classical
  exact (absorberInducedConfigurationsOn q j B).filter fun S ↦
    ∃ r, 5 ≤ r ∧ r ≤ q ∧ ∃ E : TripleSystemOn V,
      IsErdosConfigOn r E ∧ E \ B = S ∧ (E ∩ B).Nonempty

theorem card_exactBankOutsideExtensions_singleton_le_of_bank_nonempty
    {V : Type*} [Fintype V] [DecidableEq V]
    {r j : ℕ} {B K : TripleSystemOn V} (T : TripleOn V)
    (hr : 5 ≤ r) (hj : 4 ≤ j) (hK : K.Nonempty) :
    (exactBankOutsideExtensions r j B {T} K).card ≤
      (2 ^ (r ^ 3) * (r + 1)) * (Fintype.card V + 1) ^ (j - 4) := by
  by_cases hne : (exactBankOutsideExtensions r j B {T} K).Nonempty
  · obtain ⟨S, hS⟩ := hne
    have hjr := exactBank_index_order_le (by omega) hS
    have hKcard := exactBankOutsideExtensions_bank_card (by omega) (by omega) hjr hS
    have hKpos := card_pos.mpr hK
    have hrootcard : (({T} ∪ ∅) ∪ K).card = 1 + (r - j) := by
      rw [union_empty, exactBankOutsideExtensions_root_union_card hS, card_singleton, hKcard]
    have hne' : (familyExtensions (exactBankOutsideExtensions r j B {T} K) ∅).Nonempty := by
      simpa [familyExtensions] using (show (exactBankOutsideExtensions r j B {T} K).Nonempty
        from ⟨S, hS⟩)
    have hroot2 : 2 ≤ (({T} ∪ ∅) ∪ K).card := by rw [hrootcard]; omega
    have hrootsmall : (({T} ∪ ∅) ∪ K).card ≤ r - 3 := by rw [hrootcard]; omega
    have hb := card_familyExtensions_exactBankOutsideExtensions_le_strong hr hne' hroot2 hrootsmall
    have hexp : r - ((({T} ∪ ∅) ∪ K).card + 3) = j - 4 := by rw [hrootcard]; omega
    simpa only [familyExtensions, empty_subset, filter_true, hexp] using hb
  · rw [not_nonempty_iff_eq_empty.mp hne]
    simp

theorem card_familyExtensions_derivedAbsorber_singleton_le
    {V : Type*} [Fintype V] [DecidableEq V]
    (q j : ℕ) (B : TripleSystemOn V) (T : TripleOn V) (hj : 4 ≤ j) :
    (familyExtensions (derivedAbsorberConfigurations q j B) {T}).card ≤
      pairExactBankExtensionCoefficient q B * (Fintype.card V + 1) ^ (j - 4) := by
  classical
  let cover := univ.biUnion fun r : (Icc 5 q : Finset ℕ) ↦
    univ.biUnion fun K : subsetsUpToCard B q ↦
      if K.1.Nonempty then exactBankOutsideExtensions r.1 j B {T} K.1 else ∅
  have hsub : familyExtensions (derivedAbsorberConfigurations q j B) {T} ⊆ cover := by
    intro S hS
    obtain ⟨hderived, hTS⟩ := mem_familyExtensions_iff.mp hS
    obtain ⟨hSF, r, hr5, hrq, E, hE, hEout, hbank⟩ := mem_filter.mp hderived
    have hcard := absorberInducedConfigurationsOn_fixed_card S hSF
    have hK : E ∩ B ∈ subsetsUpToCard B q := by
      apply mem_subsetsUpToCard_iff.mpr
      refine ⟨inter_subset_right, ?_⟩
      have hc := card_le_card (inter_subset_left : E ∩ B ⊆ E)
      rw [hE.1.1] at hc
      omega
    apply mem_biUnion.mpr
    refine ⟨⟨r, mem_Icc.mpr ⟨hr5, hrq⟩⟩, mem_univ _, ?_⟩
    apply mem_biUnion.mpr
    refine ⟨⟨E ∩ B, hK⟩, mem_univ _, ?_⟩
    rw [if_pos hbank]
    exact mem_exactBankOutsideExtensions_iff.mpr ⟨hcard, hTS, E, hE, hEout, rfl⟩
  calc
    _ ≤ cover.card := card_le_card hsub
    _ ≤ ∑ r : (Icc 5 q : Finset ℕ), ∑ K : subsetsUpToCard B q,
        (if K.1.Nonempty then exactBankOutsideExtensions r.1 j B {T} K.1 else ∅).card :=
      card_biUnion_le.trans (sum_le_sum fun _ _ ↦ card_biUnion_le)
    _ ≤ ∑ r : (Icc 5 q : Finset ℕ), ∑ _K : subsetsUpToCard B q,
        (2 ^ (r.1 ^ 3) * (r.1 + 1)) * (Fintype.card V + 1) ^ (j - 4) := by
      apply sum_le_sum
      intro r _
      apply sum_le_sum
      intro K _
      split_ifs with hK
      · exact card_exactBankOutsideExtensions_singleton_le_of_bank_nonempty
          T (mem_Icc.mp r.2).1 hj hK
      · simp
    _ = _ := by simp only [pairExactBankExtensionCoefficient, sum_mul]

theorem genuine_of_induced_not_derived
    {V : Type*} [Fintype V] [DecidableEq V]
    {q j : ℕ} {B S : TripleSystemOn V} (hj : 3 ≤ j)
    (hS : S ∈ absorberInducedConfigurationsOn q j B)
    (hnot : S ∉ derivedAbsorberConfigurations q j B) :
    5 ≤ j ∧ IsErdosConfigOn j S := by
  classical
  obtain ⟨hcard, r, hr5, hrq, E, hE, hEout⟩ := mem_absorberInducedConfigurationsOn_iff.mp hS
  have hbank : E ∩ B = ∅ := by
    apply not_nonempty_iff_eq_empty.mp
    intro hne
    exact hnot (mem_filter.mpr ⟨hS, r, hr5, hrq, E, hE, hEout, hne⟩)
  have hSE : S = E := by
    have hdecomp := sdiff_union_inter E B
    rw [hbank, union_empty, hEout] at hdecomp
    exact hdecomp
  have hrj : r = j := by rw [hSE, hE.1.1] at hcard; omega
  refine ⟨by omega, ?_⟩
  rw [hSE, ← hrj]
  exact hE

end

end Erdos207
