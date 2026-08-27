/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.SourceRootOmissionMoment
import ErdosProblems.Erdos207.GreedyRootedConfigurationWeight
import ErdosProblems.Erdos207.LocalForbiddenConfiguration
import ErdosProblems.Erdos207.SelectedWitnessImage

/-! # The actual localized rooted statistic is dominated by fixed source witnesses -/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

theorem localization_eq_sdiff_old
    {V : Type*} [DecidableEq V] {available old C E : TripleSystemOn V}
    (hdis : Disjoint available old) (hCA : C ⊆ available) (hCE : C ⊆ E) (hOld : E \ C ⊆ old) :
    E \ old = C := by
  ext T
  constructor
  · intro hT
    have hm := mem_sdiff.mp hT
    by_contra hnot
    exact hm.2 (hOld (mem_sdiff.mpr ⟨hm.1, hnot⟩))
  · intro hT
    exact mem_sdiff.mpr ⟨hCE hT, fun ho ↦ disjoint_left.mp hdis (hCA hT) ho⟩

theorem localizedRooted_source_omission_code
    {V : Type*} [Fintype V] [DecidableEq V] {ell j j' c : ℕ}
    (W : Vortex V ell) (F J processF : ForbiddenFamilyOn V) (S : GreedyStateOn V)
    (Q C E : TripleSystemOn V) (hj : 2 ≤ j) (hjj : j ≤ j')
    (hS : GreedyInvariant processF S) (hterminal : ∀ T ∈ S.available, W.level T = Fin.last ell)
    (hC : C ∈ greedyRootedConfigurationClass J S Q c) (hCcard : C.card = j - 2)
    (hE : E ∈ F) (hEcard : E.card = j' - 2) (hCE : C ⊆ E) :
    (E, (E \ C) ∪ (C ∩ S.chosen)) ∈
      terminalOmissionCodes W (familyExtensions F Q) (fun E ↦ E \ Q) (j' - j + c) := by
  have hdata := mem_filter.mp hC
  have hQC : Q ⊆ C := hdata.2.1.trans inter_subset_left
  have hQA : Q ⊆ S.available := hdata.2.1.trans inter_subset_right
  apply mem_terminalOmissionCodes_iff.mpr
  refine ⟨mem_familyExtensions_iff.mpr ⟨hE, hQC.trans hCE⟩,
    mem_terminalRemainderChoices_iff.mpr ⟨?_, ?_, ?_⟩⟩
  · intro T hT
    rcases mem_union.mp hT with ho | hn
    · have hm := mem_sdiff.mp ho
      exact mem_sdiff.mpr ⟨hm.1, fun hq ↦ hm.2 (hQC hq)⟩
    · have hm := mem_inter.mp hn
      exact mem_sdiff.mpr ⟨hCE hm.1, fun hq ↦ (hS.2.2 T (hQA hq)).1 hm.2⟩
  · have hdis : Disjoint (E \ C) (C ∩ S.chosen) := by
      apply disjoint_left.mpr
      intro T ho hn
      exact (mem_sdiff.mp ho).2 (mem_inter.mp hn).1
    rw [card_union_of_disjoint hdis, card_sdiff_of_subset hCE, hEcard, hCcard, hdata.2.2.1]
    omega
  · intro T hT
    have hm := mem_sdiff.mp hT
    have hTE := (mem_sdiff.mp hm.1).1
    have hTC : T ∈ C := by
      by_contra hnot
      exact hm.2 (mem_union_left _ (mem_sdiff.mpr ⟨hTE, hnot⟩))
    rcases mem_union.mp (hdata.2.2.2 hTC) with hs | ha
    · exact (hm.2 (mem_union_right _ (mem_inter.mpr ⟨hTC, hs⟩))).elim
    · exact hterminal T ha

theorem localizedRooted_card_le_source_selectedCount
    {V : Type*} [Fintype V] [DecidableEq V] {ell j j' c : ℕ}
    (W : Vortex V ell) (F J processF : ForbiddenFamilyOn V) (S : GreedyStateOn V)
    (Q available old : TripleSystemOn V) (hj : 2 ≤ j) (hjj : j ≤ j')
    (huniform : ∀ E ∈ F, E.card = j' - 2)
    (hS : GreedyInvariant processF S) (hterminal : ∀ T ∈ S.available, W.level T = Fin.last ell)
    (hdis : Disjoint available old)
    (hJ : J ⊆ localForbiddenConfigurations F available old j) :
    ((greedyRootedConfigurationClass J S Q c).card : ℝ≥0) ≤
      selectedCount
        (fun u : terminalOmissionCodes W (familyExtensions F Q) (fun E ↦ E \ Q) (j' - j + c) ↦ u.1.2)
        (old ∪ S.chosen) := by
  classical
  let rem := fun u : terminalOmissionCodes W (familyExtensions F Q) (fun E ↦ E \ Q) (j' - j + c) ↦ u.1.2
  let decode := fun u : terminalOmissionCodes W (familyExtensions F Q) (fun E ↦ E \ Q) (j' - j + c) ↦ u.1.1 \ old
  have hsub : greedyRootedConfigurationClass J S Q c ⊆ selectedWitnessImage rem decode (old ∪ S.chosen) := by
    intro C hC
    obtain ⟨hCA, hCcard, E, hE, hCE, hOld⟩ :=
      (mem_localForbiddenConfigurations_iff F available old C j).mp (hJ (mem_filter.mp hC).1)
    have hcode := localizedRooted_source_omission_code W F J processF S Q C E hj hjj hS hterminal hC hCcard
      hE (huniform E hE) hCE
    apply mem_selectedWitnessImage.mpr
    refine ⟨⟨(E, (E \ C) ∪ (C ∩ S.chosen)), hcode⟩, ?_, ?_⟩
    · exact union_subset_union hOld inter_subset_right
    · exact localization_eq_sdiff_old hdis hCA hCE hOld
  have hcard : ((greedyRootedConfigurationClass J S Q c).card : ℝ≥0) ≤
      (selectedWitnessImage rem decode (old ∪ S.chosen)).card := by exact_mod_cast card_le_card hsub
  exact hcard.trans (card_selectedWitnessImage_le_selectedCount rem decode (old ∪ S.chosen))

end

end Erdos207
