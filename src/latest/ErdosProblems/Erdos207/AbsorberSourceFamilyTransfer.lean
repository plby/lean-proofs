/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.AbsorberNontrivialFamily
import ErdosProblems.Erdos207.ResidualMasterIteration

/-! # The indexed source family retains the exact full absorber invariant -/

namespace Erdos207

open Finset
open scoped Classical NNReal

noncomputable section

def absorberSourceFamily {V : Type*} [Fintype V] [DecidableEq V]
    (q : ℕ) (bank : TripleSystemOn V) : ForbiddenFamilyOn V :=
  (Icc 4 q).biUnion fun j ↦ absorberInducedConfigurationsOn q j bank

theorem mem_absorberSourceFamily_iff
    {V : Type*} [Fintype V] [DecidableEq V] {q : ℕ} {bank S : TripleSystemOn V} :
    S ∈ absorberSourceFamily q bank ↔ S ∈ absorberErdosForbiddenConfigurationsOn q bank ∧ 2 ≤ S.card := by
  constructor
  · intro hS
    obtain ⟨j, hj, hSj⟩ := mem_biUnion.mp hS
    have hj4 := (mem_Icc.mp hj).1
    have hc := (mem_absorberInducedConfigurationsOn_iff.mp hSj).1
    exact ⟨absorberInducedConfigurationsOn_subset_erdosForbidden (by omega) hSj, by omega⟩
  · rintro ⟨hS, hc⟩
    obtain ⟨j, hj4, hjq, hSj⟩ := mem_absorberNontrivialInducedFamily.mp
      (mem_absorberNontrivialInducedFamily_of_card_ge_two hS hc)
    exact mem_biUnion.mpr ⟨j, mem_Icc.mpr ⟨hj4, hjq⟩, hSj⟩

theorem avoids_absorberSource_iff_of_singleton_safe
    {V : Type*} [Fintype V] [DecidableEq V] {q : ℕ} {bank P : TripleSystemOn V}
    (hsafe : ∀ T ∈ P, {T} ∉ absorberErdosForbiddenConfigurationsOn q bank) :
    AvoidsForbidden P (absorberSourceFamily q bank) ↔
      AvoidsForbidden P (absorberErdosForbiddenConfigurationsOn q bank) := by
  constructor
  · intro h S hS hSP
    by_cases htwo : 2 ≤ S.card
    · exact h S (mem_absorberSourceFamily_iff.mpr ⟨hS, htwo⟩) hSP
    · have hpos := card_pos.mpr (mem_absorberErdosForbiddenConfigurationsOn_iff.mp hS).1
      obtain ⟨T, rfl⟩ := card_eq_one.mp (show S.card = 1 by omega)
      exact hsafe T (hSP (mem_singleton_self _)) hS
  · intro h S hS
    exact h S (mem_absorberSourceFamily_iff.mp hS).1

theorem completes_absorberSource_iff_of_singleton_safe
    {V : Type*} [Fintype V] [DecidableEq V] {q : ℕ} {bank P : TripleSystemOn V} {T : TripleOn V}
    (hsafe : {T} ∉ absorberErdosForbiddenConfigurationsOn q bank) :
    CompletesForbidden (absorberSourceFamily q bank) P T ↔
      CompletesForbidden (absorberErdosForbiddenConfigurationsOn q bank) P T := by
  constructor
  · rintro ⟨S, hS, hT, hP⟩
    exact ⟨S, (mem_absorberSourceFamily_iff.mp hS).1, hT, hP⟩
  · rintro ⟨S, hS, hT, hP⟩
    have htwo : 2 ≤ S.card := by
      by_contra h
      have hpos := card_pos.mpr (mem_absorberErdosForbiddenConfigurationsOn_iff.mp hS).1
      obtain ⟨T', rfl⟩ := card_eq_one.mp (show S.card = 1 by omega)
      have heq := mem_singleton.mp hT
      subst T'
      exact hsafe hS
    exact ⟨S, mem_absorberSourceFamily_iff.mpr ⟨hS, htwo⟩, hT, hP⟩

theorem IsMasterStagePointwiseGood.absorber_singleton_safe
    {V : Type*} [Fintype V] [DecidableEq V] {ell q h : ℕ} {W : Vortex V ell}
    {k : Fin (ell+1)} {G : SimpleGraph V} {bank A I D : TripleSystemOn V} {p eta xi : ℝ≥0}
    (hg : IsMasterStagePointwiseGood W k (absorberErdosForbiddenConfigurationsOn q bank) G A I D p eta xi h) :
    (∀ T ∈ I ∪ D, {T} ∉ absorberErdosForbiddenConfigurationsOn q bank) ∧
      (∀ T ∈ A, {T} ∉ absorberErdosForbiddenConfigurationsOn q bank) := by
  constructor
  · intro T hT hF
    exact hg.2.2.1 {T} hF (singleton_subset_iff.mpr hT)
  · intro T hT hF
    exact hg.2.2.2.2.2.2 T hT ⟨{T}, hF, mem_singleton_self _, by simp⟩

theorem IsMasterStagePointwiseGood.to_absorberSource
    {V : Type*} [Fintype V] [DecidableEq V] {ell q h : ℕ} {W : Vortex V ell}
    {k : Fin (ell+1)} {G : SimpleGraph V} {bank A I D : TripleSystemOn V} {p eta xi : ℝ≥0}
    (hg : IsMasterStagePointwiseGood W k (absorberErdosForbiddenConfigurationsOn q bank) G A I D p eta xi h) :
    IsMasterStagePointwiseGood W k (absorberSourceFamily q bank) G A I D p eta xi h := by
  refine ⟨hg.1, hg.2.1, ?_, hg.2.2.2.1, hg.2.2.2.2.1, hg.2.2.2.2.2.1, ?_⟩
  · intro S hS
    exact hg.2.2.1 S (mem_absorberSourceFamily_iff.mp hS).1
  · intro T hT hcompletion
    exact hg.2.2.2.2.2.2 T hT
      ((completes_absorberSource_iff_of_singleton_safe (hg.absorber_singleton_safe.2 T hT)).mp hcompletion)

theorem IsMasterStagePointwiseGood.restore_absorber_singletons
    {V : Type*} [Fintype V] [DecidableEq V] {ell q h : ℕ} {W : Vortex V ell}
    {k : Fin (ell+1)} {G : SimpleGraph V} {bank A I D : TripleSystemOn V} {p eta xi : ℝ≥0}
    (hg : IsMasterStagePointwiseGood W k (absorberSourceFamily q bank) G A I D p eta xi h)
    (hselected : ∀ T ∈ I ∪ D, {T} ∉ absorberErdosForbiddenConfigurationsOn q bank)
    (havailable : ∀ T ∈ A, {T} ∉ absorberErdosForbiddenConfigurationsOn q bank) :
    IsMasterStagePointwiseGood W k (absorberErdosForbiddenConfigurationsOn q bank) G A I D p eta xi h := by
  refine ⟨hg.1, hg.2.1, (avoids_absorberSource_iff_of_singleton_safe hselected).mp hg.2.2.1,
    hg.2.2.2.1, hg.2.2.2.2.1, hg.2.2.2.2.2.1, ?_⟩
  intro T hT hcompletion
  exact hg.2.2.2.2.2.2 T hT
    ((completes_absorberSource_iff_of_singleton_safe (havailable T hT)).mpr hcompletion)

theorem IsMasterCoverStep.restore_absorber_singletons
    {V : Type*} [Fintype V] [DecidableEq V] {q : ℕ} {G : SimpleGraph V}
    {U : Finset V} {bank A I D M : TripleSystemOn V}
    (hs : IsMasterCoverStep (absorberSourceFamily q bank) G U A I D M)
    (hselected : ∀ T ∈ I ∪ D, {T} ∉ absorberErdosForbiddenConfigurationsOn q bank)
    (havailable : ∀ T ∈ A, {T} ∉ absorberErdosForbiddenConfigurationsOn q bank) :
    IsMasterCoverStep (absorberErdosForbiddenConfigurationsOn q bank) G U A I D M := by
  refine ⟨hs.selected, hs.disjoint_initial, hs.packing, ?_, hs.covers_outside⟩
  apply (avoids_absorberSource_iff_of_singleton_safe ?_).mp hs.avoids
  intro T hT
  rw [← union_assoc] at hT
  exact (mem_union.mp hT).elim (hselected T) (fun hM ↦ havailable T (hs.selected hM))

theorem isLegalExtension_absorberSource_iff
    {V : Type*} [Fintype V] [DecidableEq V] {q : ℕ} {bank P : TripleSystemOn V} {T : TripleOn V}
    (hsafe : ∀ U ∈ P, {U} ∉ absorberErdosForbiddenConfigurationsOn q bank)
    (hT : {T} ∉ absorberErdosForbiddenConfigurationsOn q bank) :
    IsLegalExtension (absorberSourceFamily q bank) P T ↔
      IsLegalExtension (absorberErdosForbiddenConfigurationsOn q bank) P T := by
  have hs : ∀ U ∈ insert T P, {U} ∉ absorberErdosForbiddenConfigurationsOn q bank := by
    intro U hU
    rcases mem_insert.mp hU with rfl | hU
    · exact hT
    · exact hsafe U hU
  simp only [IsLegalExtension, avoids_absorberSource_iff_of_singleton_safe hs]

theorem updatedStageAvailable_absorberSource_eq
    {V : Type*} [Fintype V] [DecidableEq V] {q : ℕ} {bank A I D M : TripleSystemOn V}
    (U : Finset V) (hM : M ⊆ A)
    (hselected : ∀ T ∈ I ∪ D, {T} ∉ absorberErdosForbiddenConfigurationsOn q bank)
    (havailable : ∀ T ∈ A, {T} ∉ absorberErdosForbiddenConfigurationsOn q bank) :
    updatedStageAvailable (absorberSourceFamily q bank) U A I D M =
      updatedStageAvailable (absorberErdosForbiddenConfigurationsOn q bank) U A I D M := by
  have hsafe : ∀ T ∈ I ∪ (D ∪ M), {T} ∉ absorberErdosForbiddenConfigurationsOn q bank := by
    intro T hT
    rw [← union_assoc] at hT
    exact (mem_union.mp hT).elim (hselected T) (fun hm ↦ havailable T (hM hm))
  ext T
  simp only [mem_updatedStageAvailable_iff]
  by_cases hT : T ∈ A
  · simp only [hT, true_and, isLegalExtension_absorberSource_iff hsafe (havailable T hT)]
  · simp only [hT, false_and]

theorem IsResidualMasterIterationGood.restore_absorber_singletons
    {Omega V : Type*} [Fintype Omega] [Fintype V] [DecidableEq V] {ell q h : ℕ}
    {L : FiniteLaw Omega} {W : Vortex V ell} {k : Fin (ell+1)} {Gamma : SimpleGraph V}
    {G : Omega → SimpleGraph V} {bank : TripleSystemOn V} {A I D : Omega → TripleSystemOn V}
    {p eta xi C beta : ℝ≥0}
    (hg : IsResidualMasterIterationGood L W k Gamma (absorberSourceFamily q bank) G A I D p eta xi C beta h)
    (hselected : L.SupportedOn fun omega ↦ ∀ T ∈ I omega ∪ D omega,
      {T} ∉ absorberErdosForbiddenConfigurationsOn q bank)
    (havailable : L.SupportedOn fun omega ↦ ∀ T ∈ A omega,
      {T} ∉ absorberErdosForbiddenConfigurationsOn q bank) :
    IsResidualMasterIterationGood L W k Gamma (absorberErdosForbiddenConfigurationsOn q bank)
      G A I D p eta xi C beta h := by
  refine ⟨hg.1, hg.2.1, hg.2.2.trans ?_⟩
  have hsafe : L.SupportedOn fun omega ↦
      (∀ T ∈ I omega ∪ D omega, {T} ∉ absorberErdosForbiddenConfigurationsOn q bank) ∧
      (∀ T ∈ A omega, {T} ∉ absorberErdosForbiddenConfigurationsOn q bank) :=
    fun omega hm ↦ ⟨hselected omega hm, havailable omega hm⟩
  apply L.probability_mono_of_supported hsafe
  intro omega hs hgood
  exact hgood.restore_absorber_singletons hs.1 hs.2

theorem IsResidualMasterIterationGood.restore_updated_absorber
    {Omega V : Type*} [Fintype Omega] [Fintype V] [DecidableEq V] {ell q h : ℕ}
    {L : FiniteLaw Omega} {W : Vortex V ell} {k next : Fin (ell+1)} {Gamma : SimpleGraph V}
    {G : Omega → SimpleGraph V} {bank : TripleSystemOn V} {A I D M : Omega → TripleSystemOn V}
    {p eta xi xi' C beta : ℝ≥0}
    (hg : IsResidualMasterIterationGood L W next Gamma (absorberSourceFamily q bank)
      (fun omega ↦ updatedStageGraph (G omega) (W.U next) (M omega))
      (fun omega ↦ updatedStageAvailable (absorberSourceFamily q bank) (W.U next)
        (A omega) (I omega) (D omega) (M omega))
      I (fun omega ↦ D omega ∪ M omega) p eta xi' C beta h)
    (hold : L.SupportedOn (masterPointwiseGoodEvent W k (absorberErdosForbiddenConfigurationsOn q bank)
      G A I D p eta xi h))
    (hstep : L.SupportedOn fun omega ↦ IsMasterCoverStep (absorberSourceFamily q bank)
      (G omega) (W.U next) (A omega) (I omega) (D omega) (M omega)) :
    IsResidualMasterIterationGood L W next Gamma (absorberErdosForbiddenConfigurationsOn q bank)
      (fun omega ↦ updatedStageGraph (G omega) (W.U next) (M omega))
      (fun omega ↦ updatedStageAvailable (absorberErdosForbiddenConfigurationsOn q bank) (W.U next)
        (A omega) (I omega) (D omega) (M omega))
      I (fun omega ↦ D omega ∪ M omega) p eta xi' C beta h ∧
    L.SupportedOn (fun omega ↦ IsMasterCoverStep (absorberErdosForbiddenConfigurationsOn q bank)
      (G omega) (W.U next) (A omega) (I omega) (D omega) (M omega)) := by
  have hfullStep : L.SupportedOn fun omega ↦ IsMasterCoverStep (absorberErdosForbiddenConfigurationsOn q bank)
      (G omega) (W.U next) (A omega) (I omega) (D omega) (M omega) := by
    intro omega hm
    have hs := (hold omega hm).absorber_singleton_safe
    exact (hstep omega hm).restore_absorber_singletons hs.1 hs.2
  refine ⟨residualMasterIterationGood_of_probability_update hg.1 hg.2.1 hold hfullStep ?_, hfullStep⟩
  apply hg.2.2.trans
  have hscope : L.SupportedOn fun omega ↦
      masterPointwiseGoodEvent W k (absorberErdosForbiddenConfigurationsOn q bank) G A I D p eta xi h omega ∧
      IsMasterCoverStep (absorberSourceFamily q bank) (G omega) (W.U next)
        (A omega) (I omega) (D omega) (M omega) := fun omega hm ↦ ⟨hold omega hm, hstep omega hm⟩
  apply L.probability_mono_of_supported hscope
  intro omega hs hgood
  have hsafe := hs.1.absorber_singleton_safe
  have heq := updatedStageAvailable_absorberSource_eq (W.U next) hs.2.selected hsafe.1 hsafe.2
  rw [← heq]
  exact hgood.2.2.2.1

end

end Erdos207
