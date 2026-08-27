/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.LocalizedRootedOmissionCode
import ErdosProblems.Erdos207.GreedyCommonThreatPairs

/-! # Lifting localized common threats preserves distinct source configurations -/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

def sourceCommonThreats
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    (W : Vortex V ell) (F G : ForbiddenFamilyOn V) (T T' : TripleOn V) :=
  (univ : Finset (CommonThreatWitness F G T T')).filter fun u ↦ W.level u.bridge = Fin.last ell

namespace CommonThreatWitness

def liftLocalized
    {V : Type*} [Fintype V] [DecidableEq V]
    {J J' F G : ForbiddenFamilyOn V} {T T' : TripleOn V}
    (u : CommonThreatWitness J J' T T') (available old E E' : TripleSystemOn V)
    (hdis : Disjoint available old) (hCA : u.first ⊆ available) (hCA' : u.second ⊆ available)
    (hE : E ∈ F) (hE' : E' ∈ G) (hCE : u.first ⊆ E) (hCE' : u.second ⊆ E')
    (hOld : E \ u.first ⊆ old) (hOld' : E' \ u.second ⊆ old) : CommonThreatWitness F G T T' where
  bridge := u.bridge
  first := E
  second := E'
  first_mem := hE
  second_mem := hE'
  first_root := hCE u.first_root
  second_root := hCE' u.second_root
  bridge_first := hCE u.bridge_first
  bridge_second := hCE' u.bridge_second
  bridge_ne_first := u.bridge_ne_first
  bridge_ne_second := u.bridge_ne_second
  first_cross := by
    intro hT'
    apply u.first_cross
    by_contra hnot
    exact disjoint_left.mp hdis (hCA' u.second_root) (hOld (mem_sdiff.mpr ⟨hT', hnot⟩))
  second_cross := by
    intro hT
    apply u.second_cross
    by_contra hnot
    exact disjoint_left.mp hdis (hCA u.first_root) (hOld' (mem_sdiff.mpr ⟨hT, hnot⟩))
  different := by
    intro heq
    apply u.different
    rw [← localization_eq_sdiff_old hdis hCA hCE hOld,
      ← localization_eq_sdiff_old hdis hCA' hCE' hOld', heq]

theorem liftLocalized_remainder_subset
    {V : Type*} [Fintype V] [DecidableEq V]
    {J J' F G : ForbiddenFamilyOn V} {T T' : TripleOn V}
    (u : CommonThreatWitness J J' T T') (available old E E' : TripleSystemOn V)
    (hdis : Disjoint available old) (hCA : u.first ⊆ available) (hCA' : u.second ⊆ available)
    (hE : E ∈ F) (hE' : E' ∈ G) (hCE : u.first ⊆ E) (hCE' : u.second ⊆ E')
    (hOld : E \ u.first ⊆ old) (hOld' : E' \ u.second ⊆ old) :
    (u.liftLocalized available old E E' hdis hCA hCA' hE hE' hCE hCE' hOld hOld').remainder ⊆
      old ∪ u.remainder := by
  let v := u.liftLocalized available old E E' hdis hCA hCA' hE hE' hCE hCE' hOld hOld'
  change v.remainder ⊆ _
  rw [v.remainder_eq_sdiff, u.remainder_eq_sdiff]
  intro R hR
  obtain ⟨hmem, hnroot⟩ := mem_sdiff.mp hR
  by_cases hRo : R ∈ old
  · exact mem_union_left _ hRo
  · apply mem_union_right
    refine mem_sdiff.mpr ⟨?_, hnroot⟩
    rcases mem_union.mp hmem with hRE | hRE'
    · apply mem_union_left
      by_contra hnot
      exact hRo (hOld (mem_sdiff.mpr ⟨hRE, hnot⟩))
    · apply mem_union_right
      by_contra hnot
      exact hRo (hOld' (mem_sdiff.mpr ⟨hRE', hnot⟩))

end CommonThreatWitness

theorem localizedCommonThreatPairs_card_le_source
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    (W : Vortex V ell) (F G J J' : ForbiddenFamilyOn V) (S : GreedyStateOn V)
    (T T' : TripleOn V) (available old : TripleSystemOn V)
    (hdis : Disjoint available old) (hterm : ∀ U ∈ available, W.level U = Fin.last ell)
    (hJ : ∀ C ∈ J, C ⊆ available ∧ ∃ E ∈ F, C ⊆ E ∧ E \ C ⊆ old)
    (hJ' : ∀ C ∈ J', C ⊆ available ∧ ∃ E ∈ G, C ⊆ E ∧ E \ C ⊆ old) :
    ((greedyCommonThreatPairs J J' S T T').card : ℝ≥0) ≤
      selectedCount (fun u : sourceCommonThreats W F G T T' ↦ u.1.remainder) (old ∪ S.chosen) := by
  classical
  let rem := fun u : sourceCommonThreats W F G T T' ↦ u.1.remainder
  let decode := fun u : sourceCommonThreats W F G T T' ↦ (u.1.first \ old, u.1.second \ old)
  have hsub : greedyCommonThreatPairs J J' S T T' ⊆ selectedWitnessImage rem decode (old ∪ S.chosen) := by
    intro p hp
    let u := greedyCommonThreatPairWitness J J' S T T' ⟨p, hp⟩
    obtain ⟨hCA, E, hE, hCE, hOld⟩ := hJ u.first u.first_mem
    obtain ⟨hCA', E', hE', hCE', hOld'⟩ := hJ' u.second u.second_mem
    let v := u.liftLocalized available old E E' hdis hCA hCA' hE hE' hCE hCE' hOld hOld'
    have hv : v ∈ sourceCommonThreats W F G T T' :=
      mem_filter.mpr ⟨mem_univ v, hterm _ (hCA u.bridge_first)⟩
    apply mem_selectedWitnessImage.mpr
    refine ⟨⟨v, hv⟩, ?_, ?_⟩
    · exact (u.liftLocalized_remainder_subset available old E E' hdis hCA hCA' hE hE'
        hCE hCE' hOld hOld').trans (union_subset_union_right
          (greedyCommonThreatPairWitness_remainder_subset J J' S T T' ⟨p, hp⟩))
    · exact Prod.ext (localization_eq_sdiff_old hdis hCA hCE hOld)
        (localization_eq_sdiff_old hdis hCA' hCE' hOld')
  have hc : ((greedyCommonThreatPairs J J' S T T').card : ℝ≥0) ≤
      (selectedWitnessImage rem decode (old ∪ S.chosen)).card := by exact_mod_cast card_le_card hsub
  exact hc.trans (card_selectedWitnessImage_le_selectedCount rem decode (old ∪ S.chosen))

end

end Erdos207
