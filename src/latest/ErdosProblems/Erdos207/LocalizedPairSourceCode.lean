/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.SourcePinnedEdgeExtension
import ErdosProblems.Erdos207.LocalizedRootedOmissionCode
import ErdosProblems.Erdos207.PairTwoAwayThreatWeight
import ErdosProblems.Erdos207.PreliminaryEdgeSupply

/-! # Multiplicity-preserving fixed-source codes for actual pair threats -/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

theorem sourceNibbleRemaining_erase_two
    {V : Type*} [DecidableEq V] (E : TripleSystemOn V) (T U : TripleOn V)
    (hU : U ∈ E) (hne : U ≠ T) :
    sourceNibbleRemaining T (E, (E.erase U).erase T) = {U} := by
  ext R
  simp only [sourceNibbleRemaining, mem_sdiff, mem_singleton, mem_erase]
  constructor
  · rintro ⟨⟨hR, hRT⟩, hn⟩
    by_contra hRU
    exact hn ⟨hRT, hRU, hR⟩
  · rintro rfl
    exact ⟨⟨hU, hne⟩, fun h ↦ h.2.1 rfl⟩

theorem localizedPair_source_code
    {V : Type*} [Fintype V] [DecidableEq V] {ell j : ℕ}
    (W : Vortex V ell) (F : ForbiddenFamilyOn V) (T U : TripleOn V)
    (E : TripleSystemOn V) (e : Sym2 V) (hE : E ∈ F) (hcard : E.card = j - 2)
    (hT : T ∈ E) (hU : U ∈ E) (hne : U ≠ T)
    (hterm : W.level U = Fin.last ell) (he : e ∈ tripleEdgeFinset U) :
    (E, (E.erase U).erase T) ∈ sourcePinnedEdgeCodes W F T j e := by
  classical
  apply mem_filter.mpr
  constructor
  · apply mem_terminalOmissionCodes_iff.mpr
    refine ⟨mem_familyExtensions_iff.mpr ⟨hE, singleton_subset_iff.mpr hT⟩,
      mem_terminalRemainderChoices_iff.mpr ⟨?_, ?_, ?_⟩⟩
    · intro R hR
      have hm := mem_erase.mp hR
      exact mem_sdiff.mpr ⟨mem_of_mem_erase hm.2, by simpa only [mem_singleton] using hm.1⟩
    · rw [card_erase_of_mem (mem_erase.mpr ⟨hne.symm, hT⟩), card_erase_of_mem hU, hcard]
      omega
    · intro R hR
      have hrem := sourceNibbleRemaining_erase_two E T U hU hne
      have hm : R ∈ sourceNibbleRemaining T (E, (E.erase U).erase T) := hR
      rw [hrem, mem_singleton] at hm
      simpa only [hm] using hterm
  · simp only [sourceNibbleCoordinates, toRight_disjSum,
      sourceNibbleRemaining_erase_two E T U hU hne]
    exact mem_biUnion.mpr ⟨U, mem_singleton_self U, he⟩

theorem pairOn_exists_nondiagonal_edge
    {V : Type*} [DecidableEq V] (P : PairOn V) :
    ∃ e : Sym2 V, ¬ e.IsDiag ∧ e.toFinset = P.1 := by
  obtain ⟨u, v, huv, hP⟩ := card_eq_two.mp P.2
  exact ⟨s(u, v), by simpa only [Sym2.mk_isDiag_iff] using huv,
    by simpa only [Sym2.toFinset_mk_eq] using hP.symm⟩

theorem localizedPair_selectedCount_le_source
    {V : Type*} [Fintype V] [DecidableEq V] {ell j : ℕ}
    (W : Vortex V ell) (F J : ForbiddenFamilyOn V) (T : TripleOn V) (P : PairOn V)
    (available old selected : TripleSystemOn V) (e : Sym2 V)
    (he : ¬ e.IsDiag) (heP : e.toFinset = P.1)
    (huniform : ∀ E ∈ F, E.card = j - 2)
    (hterm : ∀ U ∈ available, W.level U = Fin.last ell)
    (hdis : Disjoint available old)
    (hJ : ∀ C ∈ J, C ⊆ available ∧ ∃ E ∈ F, C ⊆ E ∧ E \ C ⊆ old) :
    selectedCount (fun u : PairTwoAwayThreatWitness V J T P ↦ pairTwoAwayThreatRemainder u) selected ≤
      selectedCount (fun u : sourcePinnedEdgeCodes W F T j e ↦ u.1.2) (old ∪ selected) := by
  classical
  let rem := fun u : sourcePinnedEdgeCodes W F T j e ↦ u.1.2
  let decode := fun u : sourcePinnedEdgeCodes W F T j e ↦
    (u.1.1 \ old, sourceNibbleRemaining T u.1)
  let encode := fun u : PairTwoAwayThreatWitness V J T P ↦ (u.1.1.1, ({u.1.1.2} : TripleSystemOn V))
  have hinj : Function.Injective encode := by
    intro u v huv
    have hc := congrArg (fun x : TripleSystemOn V × TripleSystemOn V ↦ x.1) huv
    have hu := congrArg (fun x : TripleSystemOn V × TripleSystemOn V ↦ x.2) huv
    exact Subtype.ext (Subtype.ext (Prod.ext hc (singleton_injective hu)))
  have hmap : ∀ u ∈ activePairTwoAwayThreatWitnesses J selected T P,
      encode u ∈ selectedWitnessImage rem decode (old ∪ selected) := by
    intro u hu
    obtain ⟨hCA, E, hE, hCE, hOld⟩ := hJ u.1.1.1 u.1.2.1
    have hU := u.1.2.2.1
    have hT := u.1.2.2.2.1
    have hne := u.1.2.2.2.2
    have hpair : e ∈ tripleEdgeFinset u.1.1.2 := by
      apply (mem_tripleEdgeFinset_iff_toFinset_subset_of_not_isDiag e u.1.1.2 he).mpr
      rw [heP]
      exact u.2.1
    have hcode := localizedPair_source_code W F T u.1.1.2 E e hE (huniform E hE)
      (hCE hT) (hCE hU) hne (hterm _ (hCA hU)) hpair
    apply mem_selectedWitnessImage.mpr
    refine ⟨⟨(E, (E.erase u.1.1.2).erase T), hcode⟩, ?_, ?_⟩
    · intro R hR
      have hm := mem_erase.mp hR
      have hm' := mem_erase.mp hm.2
      by_cases hRC : R ∈ u.1.1.1
      · apply mem_union_right
        exact (mem_activePairTwoAwayThreatWitnesses_iff.mp hu)
          (mem_erase.mpr ⟨hm.1, mem_erase.mpr ⟨hm'.1, hRC⟩⟩)
      · exact mem_union_left _ (hOld (mem_sdiff.mpr ⟨hm'.2, hRC⟩))
    · apply Prod.ext
      · exact localization_eq_sdiff_old hdis hCA hCE hOld
      · exact sourceNibbleRemaining_erase_two E T u.1.1.2 (hCE hU) hne
  rw [selectedCount_pairTwoAwayThreatRemainder]
  have hc : (activePairTwoAwayThreatWitnesses J selected T P).card ≤
      (selectedWitnessImage rem decode (old ∪ selected)).card :=
    card_le_card_of_injOn encode hmap (fun _ _ _ _ h ↦ hinj h)
  have hc' : ((activePairTwoAwayThreatWitnesses J selected T P).card : ℝ≥0) ≤
      ((selectedWitnessImage rem decode (old ∪ selected)).card : ℝ≥0) := by exact_mod_cast hc
  exact hc'.trans (card_selectedWitnessImage_le_selectedCount rem decode (old ∪ selected))

end

end Erdos207
