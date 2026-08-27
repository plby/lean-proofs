/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.DerivedAbsorberCount

/-! # A nontrivial bank-derived configuration has a bank vertex outside any non-bank root -/

namespace Erdos207

open Finset

noncomputable section

theorem derivedAbsorber_bank_vertex_outside_root
    {V : Type*} [Fintype V] [DecidableEq V]
    {q j : ℕ} {bank D : TripleSystemOn V} (T : TripleOn V)
    (hD : D ∈ derivedAbsorberConfigurations q j bank) (hDtwo : 2 ≤ D.card) (hT : T ∉ bank) :
    ∃ v ∈ verticesOn D, v ∈ verticesOn bank ∧ v ∉ T.1 := by
  classical
  obtain ⟨_, r, hr5, _, E, hE, hEout, hbank⟩ := mem_filter.mp hD
  let K := E ∩ bank
  have hDE : D ⊆ E := by rw [← hEout]; exact sdiff_subset
  have hKE : K ⊆ E := inter_subset_left
  have hKB : K ⊆ bank := inter_subset_right
  have hKpos : 0 < K.card := card_pos.mpr hbank
  have hdecomp : D ∪ K = E := by rw [← hEout]; exact sdiff_union_inter E bank
  have hdis : Disjoint D K := by
    apply Finset.disjoint_left.mpr
    intro U hUD hUK
    have hUout : U ∈ E \ bank := by rwa [hEout]
    exact (mem_sdiff.mp hUout).2 (hKB hUK)
  have hcards : D.card + K.card = r - 2 := by
    rw [← card_union_of_disjoint hdis, hdecomp, hE.1.1]
  have hspanE := IsErdosConfig.vertices_card_eq hE hr5
  by_cases hKone : K.card = 1
  · obtain ⟨U, hKU⟩ := card_eq_one.mp hKone
    have hUK : U ∈ K := by rw [hKU]; exact mem_singleton_self _
    have hUB := hKB hUK
    have hDcard : D.card = r - 3 := by omega
    have hspanD := IsErdosConfig.vertices_eq_of_card_sub_three hE hr5 hDE hDcard
    have hnot : ¬ U.1 ⊆ T.1 := by
      intro hUT
      have heq : U = T := Subtype.ext (eq_of_subset_of_card_le hUT (by rw [U.2, T.2]))
      exact hT (heq ▸ hUB)
    obtain ⟨v, hvU, hvT⟩ := not_subset.mp hnot
    refine ⟨v, ?_, mem_biUnion.mpr ⟨U, hUB, hvU⟩, hvT⟩
    rw [hspanD]
    exact mem_biUnion.mpr ⟨U, hKE hUK, hvU⟩
  · have hKtwo : 2 ≤ K.card := by omega
    have hDspan := IsErdosConfig.subset_span hE hDE hDtwo (by omega)
    have hKspan := IsErdosConfig.subset_span hE hKE hKtwo (by omega)
    have hunion : (verticesOn D ∪ verticesOn K).card ≤ r := by
      rw [← hspanE]
      exact card_le_card (union_subset (verticesOn_mono hDE) (verticesOn_mono hKE))
    have hinc := card_union_add_card_inter (verticesOn D) (verticesOn K)
    have hinter : 4 ≤ (verticesOn D ∩ verticesOn K).card := by omega
    have hnot : ¬ verticesOn D ∩ verticesOn K ⊆ T.1 := by
      intro hsub
      have hcard := card_le_card hsub
      rw [T.2] at hcard
      omega
    obtain ⟨v, hv, hvT⟩ := not_subset.mp hnot
    exact ⟨v, (mem_inter.mp hv).1, verticesOn_mono hKB (mem_inter.mp hv).2, hvT⟩

end

end Erdos207
