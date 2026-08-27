/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.RegularizationGraphEncoding
import ErdosProblems.Erdos207.ProperPatternExtensions
import ErdosProblems.Erdos207.MasterIterationData

/-! # Clique patterns on the ambient type and their exact support and edges -/

namespace Erdos207

open Finset

noncomputable section

abbrev cliquePattern {V : Type*} [DecidableEq V] (S : Finset V) : SimpleGraph V :=
  graphRestrictedTo ⊤ S

theorem mem_graphPairFamily_pair_iff
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (v w : V) :
    {v, w} ∈ graphPairFamily G ↔ G.Adj v w := by
  rw [← Sym2.toFinset_mk_eq, mem_graphPairFamily_toFinset_iff, mem_graphEdges_iff]
  rfl

theorem graphPairFamily_cliquePattern
    {V : Type*} [Fintype V] [DecidableEq V] (S : Finset V) :
    graphPairFamily (cliquePattern S) = S.powersetCard 2 := by
  ext P
  constructor
  · intro hP
    have hc := graphPairFamily_uniform (cliquePattern S) P hP
    obtain ⟨v, w, hvw, rfl⟩ := card_eq_two.mp hc
    have hAdj := (mem_graphPairFamily_pair_iff (cliquePattern S) v w).mp hP
    exact mem_powersetCard.mpr ⟨insert_subset hAdj.2.1 (singleton_subset_iff.mpr hAdj.2.2),
      by simp [hvw]⟩
  · intro hP
    have hm := mem_powersetCard.mp hP
    obtain ⟨v, w, hvw, rfl⟩ := card_eq_two.mp hm.2
    apply (mem_graphPairFamily_pair_iff (cliquePattern S) v w).mpr
    exact ⟨hvw, hm.1 (by simp), hm.1 (by simp)⟩

theorem cliquePattern_support
    {V : Type*} [Fintype V] [DecidableEq V] (S : Finset V) (hS : 2 ≤ S.card) :
    graphSupportFinset (cliquePattern S) = S := by
  ext v
  rw [mem_graphSupportFinset_iff]
  constructor
  · rintro ⟨w, hvw⟩
    exact hvw.2.1
  · intro hv
    have hne : (S.erase v).Nonempty := card_pos.mp (by rw [card_erase_of_mem hv]; omega)
    obtain ⟨w, hw⟩ := hne
    exact ⟨w, (mem_erase.mp hw).1.symm, hv, (mem_erase.mp hw).2⟩

theorem cliquePattern_edge_card
    {V : Type*} [Fintype V] [DecidableEq V] (S : Finset V) :
    (graphEdges (cliquePattern S)).card = S.card.choose 2 := by
  have h := congrArg Finset.card (graphPairFamily_cliquePattern S)
  simpa only [graphPairFamily, card_image_of_injective _ sym2_toFinset_injective,
    card_powersetCard] using h

theorem cliquePattern_le_iff
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (S : Finset V) :
    cliquePattern S ≤ G ↔ S.powersetCard 2 ⊆ graphPairFamily G := by
  constructor
  · intro h P hP
    have hm := mem_powersetCard.mp hP
    obtain ⟨v, w, hvw, rfl⟩ := card_eq_two.mp hm.2
    apply (mem_graphPairFamily_pair_iff G v w).mpr
    exact h ⟨hvw, hm.1 (by simp), hm.1 (by simp)⟩
  · intro h v w hvw
    apply (mem_graphPairFamily_pair_iff G v w).mp
    apply h
    exact mem_powersetCard.mpr
      ⟨insert_subset hvw.2.1 (singleton_subset_iff.mpr hvw.2.2),
        by simp only [card_pair (show v ≠ w from hvw.1)]⟩

theorem graphPairFamily_subset_powerset_of_supported
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (U : Finset V)
    (hG : GraphSupportedOn G (U : Set V)) :
    graphPairFamily G ⊆ U.powersetCard 2 := by
  intro P hP
  have hc := graphPairFamily_uniform G P hP
  obtain ⟨v, w, hvw, rfl⟩ := card_eq_two.mp hc
  have hAdj := (mem_graphPairFamily_pair_iff G v w).mp hP
  have hU := hG hAdj
  exact mem_powersetCard.mpr
    ⟨insert_subset hU.1 (singleton_subset_iff.mpr hU.2), card_pair hvw⟩

theorem graphEdges_card_le_support_sq
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (U : Finset V)
    (hG : GraphSupportedOn G (U : Set V)) :
    (graphEdges G).card ≤ U.card ^ 2 := by
  rw [← graphPairFamily_card]
  calc
    _ ≤ (U.powersetCard 2).card := card_le_card (graphPairFamily_subset_powerset_of_supported G U hG)
    _ = U.card.choose 2 := card_powersetCard _ _
    _ ≤ U.card ^ 2 := Nat.choose_le_pow _ _

end

end Erdos207
