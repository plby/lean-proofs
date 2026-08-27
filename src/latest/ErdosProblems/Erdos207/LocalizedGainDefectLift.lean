/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.LocalizedRootedOmissionCode
import ErdosProblems.Erdos207.GreedyGainDefectPairs

/-! # Gain-defect localization preserves the omitted root and noncontainment -/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

def sourceGainDefects
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    (W : Vortex V ell) (F G : ForbiddenFamilyOn V) (T : TripleOn V) (a : ℕ) :=
  (univ : Finset (GainDefectWitness F G T a)).filter fun u ↦
    ∀ U ∈ u.omittedRoot, W.level U = Fin.last ell

namespace GainDefectWitness

def liftLocalized
    {V : Type*} [Fintype V] [DecidableEq V] {a : ℕ}
    {J J' F G : ForbiddenFamilyOn V} {T : TripleOn V}
    (u : GainDefectWitness J J' T a) (available old E E' : TripleSystemOn V)
    (hdis : Disjoint available old) (hCA : u.first ⊆ available) (hCA' : u.second ⊆ available)
    (hE : E ∈ F) (hE' : E' ∈ G) (hCE : u.first ⊆ E) (hCE' : u.second ⊆ E')
    (hOld : E \ u.first ⊆ old) (hOld' : E' \ u.second ⊆ old) : GainDefectWitness F G T a where
  first := E
  second := E'
  omitted := u.omitted
  first_mem := hE
  second_mem := hE'
  root_mem := hCE u.root_mem
  omitted_subset := by
    intro U hU
    have hm := mem_erase.mp (u.omitted_subset hU)
    exact mem_erase.mpr ⟨hm.1, hCE hm.2⟩
  omitted_card := u.omitted_card
  second_root_card := by
    have heq : E' ∩ insert T u.omitted = u.second ∩ insert T u.omitted := by
      apply Subset.antisymm
      · intro U hU
        obtain ⟨hUE', hUroot⟩ := mem_inter.mp hU
        refine mem_inter.mpr ⟨?_, hUroot⟩
        by_contra hnot
        exact disjoint_left.mp hdis (hCA (u.omittedRoot_subset_first hUroot))
          (hOld' (mem_sdiff.mpr ⟨hUE', hnot⟩))
      · intro U hU
        exact mem_inter.mpr ⟨hCE' (mem_inter.mp hU).1, (mem_inter.mp hU).2⟩
    rw [heq]
    exact u.second_root_card
  not_subset := by
    intro hEE
    apply u.not_subset
    intro U hU
    have heq := localization_eq_sdiff_old hdis hCA hCE hOld
    rw [← heq]
    exact mem_sdiff.mpr ⟨hEE (hCE' hU), fun ho ↦ disjoint_left.mp hdis (hCA' hU) ho⟩

theorem liftLocalized_remainder_subset
    {V : Type*} [Fintype V] [DecidableEq V] {a : ℕ}
    {J J' F G : ForbiddenFamilyOn V} {T : TripleOn V}
    (u : GainDefectWitness J J' T a) (available old E E' : TripleSystemOn V)
    (hdis : Disjoint available old) (hCA : u.first ⊆ available) (hCA' : u.second ⊆ available)
    (hE : E ∈ F) (hE' : E' ∈ G) (hCE : u.first ⊆ E) (hCE' : u.second ⊆ E')
    (hOld : E \ u.first ⊆ old) (hOld' : E' \ u.second ⊆ old) :
    (u.liftLocalized available old E E' hdis hCA hCA' hE hE' hCE hCE' hOld hOld').remainder ⊆
      old ∪ u.remainder := by
  let v := u.liftLocalized available old E E' hdis hCA hCA' hE hE' hCE hCE' hOld hOld'
  change v.remainder ⊆ _
  rw [v.remainder_eq_sdiff, u.remainder_eq_sdiff]
  intro U hU
  obtain ⟨hmem, hnroot⟩ := mem_sdiff.mp hU
  by_cases hUo : U ∈ old
  · exact mem_union_left _ hUo
  · apply mem_union_right
    refine mem_sdiff.mpr ⟨?_, hnroot⟩
    rcases mem_union.mp hmem with hUE | hUE'
    · apply mem_union_left
      by_contra hnot
      exact hUo (hOld (mem_sdiff.mpr ⟨hUE, hnot⟩))
    · apply mem_union_right
      by_contra hnot
      exact hUo (hOld' (mem_sdiff.mpr ⟨hUE', hnot⟩))

end GainDefectWitness

theorem localizedGainDefectCount_le_source
    {V : Type*} [Fintype V] [DecidableEq V] {ell c m : ℕ}
    (W : Vortex V ell) (F G J J' processF : ForbiddenFamilyOn V) (S : GreedyStateOn V)
    (T : TripleOn V) (available old : TripleSystemOn V)
    (hS : GreedyInvariant processF S) (huniform : ∀ C ∈ J, C.card = m)
    (hdis : Disjoint available old) (hterm : ∀ U ∈ available, W.level U = Fin.last ell)
    (hJ : ∀ C ∈ J, C ⊆ available ∧ ∃ E ∈ F, C ⊆ E ∧ E \ C ⊆ old)
    (hJ' : ∀ C ∈ J', C ⊆ available ∧ ∃ E ∈ G, C ⊆ E ∧ E \ C ⊆ old) :
    (greedyActiveGainDefectCount J J' S T c : ℝ≥0) ≤
      selectedCount (fun u : sourceGainDefects W F G T (m - c - 1) ↦ u.1.remainder) (old ∪ S.chosen) := by
  classical
  by_cases hT : T ∈ S.available
  · simp only [greedyActiveGainDefectCount, if_pos hT]
    let rem := fun u : sourceGainDefects W F G T (m - c - 1) ↦ u.1.remainder
    let decode := fun u : sourceGainDefects W F G T (m - c - 1) ↦ (u.1.first \ old, u.1.second \ old)
    have hsub : greedyGainDefectPairs J J' S T c ⊆ selectedWitnessImage rem decode (old ∪ S.chosen) := by
      intro p hp
      let u := greedyGainDefectPairWitness J J' S T c m hS hT huniform ⟨p, hp⟩
      obtain ⟨hCA, E, hE, hCE, hOld⟩ := hJ u.first u.first_mem
      obtain ⟨hCA', E', hE', hCE', hOld'⟩ := hJ' u.second u.second_mem
      let v := u.liftLocalized available old E E' hdis hCA hCA' hE hE' hCE hCE' hOld hOld'
      have hv : v ∈ sourceGainDefects W F G T (m - c - 1) :=
        mem_filter.mpr ⟨mem_univ v, fun U hU ↦ hterm U (hCA (u.omittedRoot_subset_first hU))⟩
      apply mem_selectedWitnessImage.mpr
      refine ⟨⟨v, hv⟩, ?_, ?_⟩
      · exact (u.liftLocalized_remainder_subset available old E E' hdis hCA hCA' hE hE'
          hCE hCE' hOld hOld').trans (union_subset_union_right
            (greedyGainDefectPairWitness_remainder_subset J J' S T c m hS hT huniform ⟨p, hp⟩))
      · exact Prod.ext (localization_eq_sdiff_old hdis hCA hCE hOld)
          (localization_eq_sdiff_old hdis hCA' hCE' hOld')
    have hc : ((greedyGainDefectPairs J J' S T c).card : ℝ≥0) ≤
        (selectedWitnessImage rem decode (old ∪ S.chosen)).card := by exact_mod_cast card_le_card hsub
    exact hc.trans (card_selectedWitnessImage_le_selectedCount rem decode (old ∪ S.chosen))
  · simp only [greedyActiveGainDefectCount, if_neg hT, Nat.cast_zero, zero_le]

end

end Erdos207
